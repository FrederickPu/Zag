import Lang.SSA
import Lang.Simple.ABI

/-!
  # SSA dialects — full AutoCorres pipeline

  Source: <https://github.com/seL4/l4v/tree/master/tools/autocorres>

  ```
  SIMPL  →  L1  →  L2  →  HL  →  WA  →  TS
            └─ same primCtx ─┘    └─ new prims ─┘
  ```

  Phases are AC's `datatype phase = CP | L1 | L2 | HL | WA | TS`
  (function_info.ML:135); the pipeline that sequences them is
  autocorres.ML:586–625.

  ## One PrimCtx per abstraction tier? **No.**

  `Val` / `Term` are indexed by `primCtx` only (AutoCorres.md §4a). So:

  | phases | share primCtx? | why |
  | --- | --- | --- |
  | **Simpl, L1, L2** | **yes** (`liveCtx`) | only whitelist / state *shape* change; same `Word`/`Heap`/`State` carriers |
  | **HL** | **no** | `Heap` (bytes/words) ⟹ `HeapW` (typed) — different prims → `CtxRefine` |
  | **WA** | **no** | `Word` (BitVec32) ⟹ `Nat`/`Int` — different prims → `CtxRefine` |
  | **TS** | maybe | may change `M` only; still a cross-`M` refine if monadic |

  Heap **is** fundamentally different after HL (AC `HeapLift.thy`). Word **is**
  fundamentally different after WA (`WordAbstract.thy`). Forcing one PrimCtx
  across those would lie about types: `Val` of concrete heap ≠ `Val` of typed heap.

  L1/L2 only drop `state.get/set/pack` and shrink ambient state to globals;
  they do **not** change how heap/word bits are represented — so one PrimCtx
  is correct *there* (§5.0).

  Zag encoding for Simpl/L1/L2: `M := Id`, state explicit SSA; exception flags
  ≈ `unit+unit` (L1Defs.thy:16,54–65).
-/

namespace Lang.Simple.Dialect

open Zag
open Zag.Lang.SSA
open Lang.Simple.ABI

/-! ## Re-export state carriers (defined live in ABI) -/

abbrev L1State := FullState
abbrev GlobalsState := Globals

def localsTy (arity : Nat) : Ty :=
  .struct (List.replicate arity WordTy)

def globalsTy : Ty := HeapTy

def fullStateTy (_arity : Nat) : Ty := StateTy

/--
  AC `datatype phase = CP | L1 | L2 | HL | WA | TS` — function_info.ML:135.
  `CP` is the definition as it comes out of the C parser (SIMPL).
-/
inductive Phase where
  | CP | L1 | L2 | HL | WA | TS
  deriving DecidableEq, Repr

namespace Phase

/-- AC `string_of_phase` — function_info.ML:136–141. -/
def toName : Phase → String
  | .CP => "CP" | .L1 => "L1" | .L2 => "L2"
  | .HL => "HL" | .WA => "WA" | .TS => "TS"

/-- AC `encode_phase` — function_info.ML:142–147. -/
def encode : Phase → Nat
  | .CP => 0 | .L1 => 1 | .L2 => 2
  | .HL => 3 | .WA => 4 | .TS => 5

/-- The AC pipeline order — autocorres.ML:586–625. -/
def pipeline : List Phase := [.CP, .L1, .L2, .HL, .WA, .TS]

/-- HL and WA are the optional phases (`skip_heap_abs` / `skip_word_abs`). -/
def isOptional : Phase → Bool
  | .HL | .WA => true
  | _ => false

end Phase

structure Dialect where
  /-- Which AC phase this dialect is the output of — function_info.ML:135. -/
  phase : Phase
  ctx : Ctx
  /-- Host ambient state type for this phase. -/
  State : Type
  stateTy : Ty
  primFns : List String
  ops : List String
  resultTy : Ty

namespace Dialect

def primCtx (d : Dialect) : PrimitiveCtx := d.ctx.primCtx
def M (d : Dialect) : Type → Type := d.ctx.primCtx.M

mutual
partial def mentionsOk (d : Dialect) : SSAValue d.primCtx → Bool
  | .raw (.primFunc name) => d.primFns.contains name
  | .raw _ => true
  | .var _ => true
  | .call fn args => mentionsOk d fn && args.all (mentionsOk d)
  | .struct _ fs => fs.all (mentionsOk d)
  | .field _ _ v => mentionsOk d v
  | .op name args =>
      (name == "pure" || name == "bind" || d.ops.contains name) && args.all (mentionsOk d)
  | .block _ b => exprMentionsOk d b
  | .phi _ _ => true
  | .loopBody _ _ init _ b => init.all (mentionsOk d) && exprMentionsOk d b

partial def exprMentionsOk (d : Dialect) : SSAExpr d.primCtx → Bool
  | .ret v => mentionsOk d v
  | .let_ _ v n => mentionsOk d v && exprMentionsOk d n
  | .seq a b => exprMentionsOk d a && exprMentionsOk d b
  | .ite c t e => mentionsOk d c && exprMentionsOk d t && exprMentionsOk d e
  | .yield vs => vs.all (mentionsOk d)
end

structure WF (d : Dialect) (expr : SSAExpr d.primCtx) : Prop where
  mentions : exprMentionsOk d expr = true
  lowers : ∃ term, SSAExpr.toTerm? expr {} = some term

end Dialect

def peanoOps : List String := ["ite", "eq", "lt", "gt"]
def wordFns : List String := ["word.add", "word.sub", "word.lt"]
def heapFns : List String := ["heap.load", "heap.store"]
def heapWFns : List String := ["heap.w.get", "heap.w.set", "heap.w.valid"]
def natFns : List String := ["add", "sub", "wa.guard.add", "wa.guard.sub"]

def localAbiFns (arity : Nat) : List String :=
  (List.range arity).map stateGetName ++
  (List.range arity).map stateSetName ++
  [statePackName arity]

/--
  Shared **lifting** context only (Simpl/L1/L2).
  Not used for HL/WA — those get their own primCtx (§4a).
-/
def liveCtx (arity : Nat) : Ctx :=
  (wordStateContext arity).zagCtx

/-! ## Phase dialects -/

/--
  **Simpl** — AC SIMPL `com` (C parser). Zag: `Com` + `BigStep`.
  State = full record. M unused.
-/
def simplDialect (arity : Nat) : Dialect where
  phase := .CP
  ctx := liveCtx arity
  State := L1State
  stateTy := StateTy
  primFns := localAbiFns arity ++ wordFns ++ heapFns
  ops := peanoOps
  resultTy := StateTy

/--
  **L1** — AC SimplConv / ExceptionRewrite (`L1Defs.thy`).

  * AC monad: `('s, unit+unit) nondet_monad` — L1Defs.thy:16
  * Zag: explicit full state + flags ≈ Inr/Inl (L1corres :54–65);
    `M := Id` (§5.0); live path = `liveCtx`
  * L1_skip/modify/throw/guard — L1Defs.thy:18–25
-/
def l1Dialect (arity : Nat) : Dialect where
  phase := .L1
  ctx := liveCtx arity
  State := L1State
  stateTy := StateTy
  primFns := localAbiFns arity ++ wordFns ++ heapFns
  ops := peanoOps
  resultTy := .struct [.prim "Bool", .prim "Bool", StateTy]

/--
  **L2** — AC LocalVarExtract (`L2Defs.thy`).

  * AC monad: `('s_g, 'e+'a) nondet_monad` — L2Defs.thy:11
  * Ambient State = **Globals** (heap), not Unit — LocalVarExtract
  * Locals = SSA / L2_gets — L2Defs.thy:15
  * `st` = projectGlobals — L2Defs.thy:85–91
  * drops local ABI; keeps word + heap
-/
def l2Dialect (arity : Nat) : Dialect where
  phase := .L2
  ctx := liveCtx arity
  State := L2State
  stateTy := globalsTy
  primFns := wordFns ++ heapFns
  ops := peanoOps
  resultTy := .struct (List.replicate arity WordTy)

/-- HL abstract primCtx (Heap → HeapW). AC HeapLift.thy -/
def hlZagCtx : Ctx where
  primCtx := heapPrimitiveCtx
  primFuncCtx := heapPrimFuncs
  opCtx := Peano.opCtx heapPrimitiveCtx

/--
  **HL** — AC HeapLift.thy / heap_lift.ML

  * Concrete `heap.load/store` → `heap.w.get/set` + `heap.w.valid`
  * prims: Heap ⟹ HeapW (AutoCorres.md §5.0 table)
-/
def hlDialect : Dialect where
  phase := .HL
  ctx := hlZagCtx
  State := L2State
  stateTy := globalsTy
  primFns := wordFns ++ heapWFns
  ops := peanoOps
  resultTy := globalsTy

/-- WA abstract Nat ctx. AC WordAbstract.thy -/
def waPrimCtx : PrimitiveCtx :=
  .ofPrims [.of "Nat" Nat, .of "Bool" Bool, .of "Unit" Unit, .of "Heap" Heap, .of "Ptr" Ptr]

instance : Peano.Types waPrimCtx where
  natType := by rfl
  boolType := by rfl

def waNatAdd : PrimFunc waPrimCtx where
  args := ["Nat", "Nat"]; out := "Nat"; hprim := by decide
  interp
  | [a, b] => do
      let x ← a.asNat?; let y ← b.asNat?
      some (Val.nat (x + y))
  | _ => none

def waNatSub : PrimFunc waPrimCtx where
  args := ["Nat", "Nat"]; out := "Nat"; hprim := by decide
  interp
  | [a, b] => do
      let x ← a.asNat?; let y ← b.asNat?
      some (Val.nat (x - y))
  | _ => none

/--
  AC's overflow guard for unsigned add, as a primitive that **fails**.
  `L2_guard c ≡ liftE (guard c)` (L2Defs.thy:21) fails the monad when `c` is
  false; AC emits it before the abstracted operation (`corresTA_L2_seq`,
  WordAbstract.thy:597–601). The precondition is `unat_abstract_binops(1)`'s
  `a + b ≤ UWORD_MAX` — WordAbstract.thy:166.
-/
def waGuardAdd : PrimFunc waPrimCtx where
  args := ["Nat", "Nat"]; out := "Nat"; hprim := by decide
  interp
  | [a, b] => do
      let x ← a.asNat?; let y ← b.asNat?
      if x + y ≤ 4294967295 then some (Val.nat (x + y)) else none
  | _ => none

/--
  AC's guard for unsigned subtraction: `unat_abstract_binops(3)`'s `a ≥ b`
  — WordAbstract.thy:168.
-/
def waGuardSub : PrimFunc waPrimCtx where
  args := ["Nat", "Nat"]; out := "Nat"; hprim := by decide
  interp
  | [a, b] => do
      let x ← a.asNat?; let y ← b.asNat?
      if y ≤ x then some (Val.nat (x - y)) else none
  | _ => none

def waZagCtx : Ctx where
  primCtx := waPrimCtx
  primFuncCtx :=
    [("add", waNatAdd), ("sub", waNatSub),
     ("wa.guard.add", waGuardAdd), ("wa.guard.sub", waGuardSub)]
  opCtx := Peano.opCtx waPrimCtx

/--
  **WA** — AC WordAbstract.thy

  * Word (BitVec 32) → Nat; leaf law `(x+y).toNat = x.toNat+y.toNat` if no ovf
  * valRel: w ~ n ↔ w.toNat = n
-/
def waDialect (arity : Nat) : Dialect where
  phase := .WA
  ctx := waZagCtx
  State := L2State
  stateTy := globalsTy
  primFns := natFns ++ heapFns
  ops := peanoOps
  resultTy := .struct (List.replicate arity (.prim "Nat"))

/--
  **TS** — AC TypeStrengthen.thy / monad_types.ML

  * AC ladder: nondet → gets → option → pure
  * Zag §5.0: state already explicit, so TS = drop `.m` where no guard fails
  * First cut: identity on pure L2/WA output (Preserves.refl)
-/
def tsDialect (arity : Nat) : Dialect where
  phase := .TS
  ctx := waZagCtx
  State := L2State
  stateTy := globalsTy
  primFns := natFns
  ops := peanoOps
  resultTy := .struct (List.replicate arity (.prim "Nat"))

/-! ## Faithfulness pins -/

/-- Every AC phase (function_info.ML:135) has a dialect, in pipeline order. -/
def dialectOf (arity : Nat) : Phase → Dialect
  | .CP => simplDialect arity
  | .L1 => l1Dialect arity
  | .L2 => l2Dialect arity
  | .HL => hlDialect
  | .WA => waDialect arity
  | .TS => tsDialect arity

/-- Each dialect reports the phase it is the output of. -/
theorem dialectOf_phase (arity : Nat) (p : Phase) : (dialectOf arity p).phase = p := by
  cases p <;> rfl

/-- Pipeline covers exactly AC's phase enum — function_info.ML:135. -/
theorem pipeline_covers_all (p : Phase) : p ∈ Phase.pipeline := by
  cases p <;> decide

/-- AC `encode_phase` order — function_info.ML:142–147. -/
theorem pipeline_encodes_in_order :
    Phase.pipeline.map Phase.encode = [0, 1, 2, 3, 4, 5] := by decide

/-- AC's optional phases are exactly HL and WA (autocorres.ML:596–617). -/
theorem optional_phases :
    Phase.pipeline.filter Phase.isOptional = [.HL, .WA] := by decide

theorem l1_l2_same_live_primCtx (arity : Nat) :
    (l1Dialect arity).ctx.primCtx = (l2Dialect arity).ctx.primCtx := rfl

theorem l1_l2_same_as_simpl (arity : Nat) :
    (l1Dialect arity).ctx.primCtx = (simplDialect arity).ctx.primCtx := rfl

/-- HL changes prims (HeapW) — not the live lifting primCtx. -/
theorem hl_primCtx_ne_live :
    hlDialect.ctx.primCtx ≠ (l1Dialect 2).ctx.primCtx := by
  intro h
  have h1 := congrArg (fun c : PrimitiveCtx => (c.get? "HeapW").isSome) h
  -- live has no HeapW; hl does
  have hlW : (hlDialect.ctx.primCtx.get? "HeapW").isSome = true := by native_decide
  have liveW : ((l1Dialect 2).ctx.primCtx.get? "HeapW").isSome = false := by native_decide
  simp [hlW, liveW] at h1

/-- WA changes Word→Nat prims — not the live lifting primCtx. -/
theorem wa_primCtx_ne_live :
    (waDialect 2).ctx.primCtx ≠ (l1Dialect 2).ctx.primCtx := by
  intro h
  have h1 := congrArg (fun c : PrimitiveCtx => (c.get? "Word").isSome) h
  have waW : ((waDialect 2).ctx.primCtx.get? "Word").isSome = false := by native_decide
  have liveW : ((l1Dialect 2).ctx.primCtx.get? "Word").isSome = true := by native_decide
  simp [waW, liveW] at h1

/-- Live path uses Id (explicit state = AC StateM plumbing) — §5.0 -/
theorem live_monad_is_Id :
    (l1Dialect 2).ctx.primCtx.M = Id := rfl

theorem l1_state_is_FullState : (l1Dialect 2).State = L1State := rfl
theorem l2_state_is_Globals : (l2Dialect 2).State = L2State := rfl

theorem l2_drops_state_get :
    ¬ (l2Dialect 2).primFns.contains "state.get.0" := by native_decide

theorem l2_keeps_heap_load :
    (l2Dialect 2).primFns.contains "heap.load" = true := by native_decide

theorem l2_keeps_word_add :
    (l2Dialect 2).primFns.contains "word.add" = true := by native_decide

theorem hl_has_heap_w :
    (hlDialect).primFns.contains "heap.w.get" = true := by native_decide

theorem wa_has_nat_add :
    (waDialect 2).primFns.contains "add" = true := by native_decide

theorem projectGlobals_drops_locals (locals : List Word) (h : Heap) :
    (projectGlobals ⟨locals, ⟨h⟩⟩).heap = h := rfl

/-- Field lookup is State.getLocal? on the record (not “list is state”). -/
example (s : FullState) (i : Nat) : State.getLocal? s i = s.locals[i]? := rfl

end Lang.Simple.Dialect
