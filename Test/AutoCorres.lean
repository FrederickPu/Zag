import Lang.Simple
import Lib.Peano
import Test.L1

/-!
  AutoCorres-shaped executable pipeline and correspondence scaffolding.
  The quantified per-phase proofs and end-to-end chain are intentionally not
  claimed until their obligations are implemented.
-/

namespace Zag.Test.AutoCorres

open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.C0.W2
open Lang.Simple.Lift
open Lang.Simple.Lift.L1
open Lang.Simple.Lift.WA
open Lang.Simple.Dialect
open Zag.Test.L1 (run boolFalse)

theorem add_from_c0 : (toCom addStmt).isSome = true := add_elab
theorem max_from_c0 : (toCom maxStmt).isSome = true := max_elab

theorem add_fused_rewrite : add_fusedL2.isSome = true := by native_decide
theorem max_fused_rewrite : max_fusedL2.isSome = true := by native_decide

def w (n : Nat) : Word := Word.ofNat n

theorem add_eval_3_4 :
    (do let s ← add_fusedL2; eval_L2 s (w 3) (w 4)) = some (w 7, w 4) := by
  native_decide

theorem max_eval_3_5 :
    (do let s ← max_fusedL2; eval_L2 s (w 3) (w 5)) = some (w 5, w 5) := by
  native_decide

theorem max_eval_7_2 :
    (do let s ← max_fusedL2; eval_L2 s (w 7) (w 2)) = some (w 7, w 2) := by
  native_decide

theorem throw_catch_l1_syntax : throwCatch_L1Syntax.isSome = true := by native_decide

/-! The proved phase rules use AC's result-set plus failure-bit semantics. -/

theorem l1_skip_corres :
    L1corres false Zag.Test.L1.Γ Zag.Test.L1.uf skipResult
      (.Skip : Com ctx Proc Fault) :=
  l1corres_skip false Zag.Test.L1.Γ Zag.Test.L1.uf

theorem l1_throw_corres :
    L1corres false Zag.Test.L1.Γ Zag.Test.L1.uf throwResult
      (.Throw : Com ctx Proc Fault) :=
  l1corres_throw false Zag.Test.L1.Γ Zag.Test.L1.uf

def exactSimplEnv : Lang.Simple.SIMPL.Body Nat Proc Fault := fun _ => none

def exactSimplL1Pass :=
  Lang.Simple.Lift.SIMPL.L1.basePass false exactSimplEnv

theorem exact_simpl_l1_is_nontrivial :
    exists source target, exactSimplL1Pass.translate source = some target :=
  exactSimplL1Pass.nontrivial

theorem exact_simpl_basic_is_certified :
    Lang.Simple.Lift.SIMPL.L1.Certificate false exactSimplEnv
      (.basic Nat.succ) (.modify Nat.succ) :=
  exactSimplL1Pass.sound _ _ rfl

def exactLocalModel :
    Lang.Simple.Lift.SIMPL.L2.LocalModel (Nat × Nat) Unit (Nat × Nat) where
  projectState := fun _ => ()
  inputArgs := id

def exactSimplL2Pass := Lang.Simple.Lift.L2.certifiedBasePass exactLocalModel

theorem exact_simpl_l2_is_nontrivial :
    exists source target, exactSimplL2Pass.translate source = some target :=
  exactSimplL2Pass.nontrivial

theorem exact_simpl_l2_skip_is_certified :
    Lang.Simple.Lift.L2.Refinement exactLocalModel (.skip)
      (fun _ => Lang.Simple.Lift.SIMPL.L2.skip) :=
  exactSimplL2Pass.sound _ _ rfl

theorem l2_skip_corres :
    L2.L2corres projectGlobals (fun _ => ()) (fun _ => ()) (fun _ => True)
      (L2.l2Skip : Globals → Lang.Simple.Corres.XFResult Unit Unit Globals)
      (L2.l1Skip : FullState → Lang.Simple.Corres.XFResult Unit Unit FullState) :=
  L2.l2corres_skip projectGlobals (fun _ => ()) (fun _ => True)

/-- WA leaf: bitvector add = nat add when no overflow. -/
theorem wa_add_leaf (x y : Word)
    (h : x.toNat + y.toNat < overflowBound) :
    (x + y).toNat = x.toNat + y.toNat :=
  toNat_add_of_lt x y h

example : (w 3 + w 4).toNat = 3 + 4 :=
  wa_add_leaf (w 3) (w 4) (by native_decide)

/-- WA leaf: bitvector sub = nat sub when no wrap. -/
theorem wa_sub_leaf (x y : Word) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  toNat_sub_of_le x y h

example : (w 7 - w 3).toNat = 7 - 3 :=
  wa_sub_leaf (w 7) (w 3) (by native_decide)

/-- Word2 Skip packing/eval (concrete). -/
theorem skip_pack_eval : Lang.Simple.Word2.evalPackNats 1 2 = some (1, 2) :=
  Lang.Simple.Word2.eval_pack_1_2

example : Word = BitVec 32 := rfl

-- Experimental dense-heap syntax helper (not AC HeapLift).
open Lang.Simple.Lift (heapConcreteCtx)
def heapLoad : Zag.Lang.SSA.SSAExpr heapConcreteCtx.primCtx :=
  .ret (.call (.primFunc "heap.load") [.var "h", .var "p"])

def heapStore : Zag.Lang.SSA.SSAExpr heapConcreteCtx.primCtx :=
  .ret (.call (.primFunc "heap.store") [.var "h", .var "p", .var "w"])

theorem dense_heap_load_helper :
    (Lang.Simple.Lift.HL.rewriteDenseWordHeap? heapLoad).isSome = true := by
  native_decide

-- Experimental run-then-unpack helper; not LocalVarExtract.
open Lang.Simple.Lift.L2 (evalFromL1?)

def runL1L2 (cmd : Com ctx Proc Fault) (x y : Nat) : Option (Nat × Nat) := do
  let l1 ← toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) cmd
  let v ← evalFromL1? locals l1 (State.val [w x, w y])
  let tys := [WordTy, WordTy]
  let raw ← v.as? (.struct tys)
  let fields := cast (Zag.Ty.type.eq_5 ctx.primCtx tys) raw
  some (Word.toNat (State.toWord (fields ⟨0, by decide⟩)),
        Word.toNat (State.toWord (fields ⟨1, by decide⟩)))

theorem skip_l1l2_eval :
    runL1L2 .Skip 3 4 = some (3, 4) := by
  native_decide

theorem throw_l1l2_eval_rejected_by_normal_extract :
    runL1L2 .Throw 3 4 = none := by
  native_decide

/-- C0 add through L1 exception path (Normal outcome). -/
theorem add_l1_eval :
    run add 3 4 = some (false, false, 7, 4) := by
  native_decide

/-- C0 add through L1→L2 extract. -/
theorem add_l1l2_eval :
    runL1L2 add 3 4 = some (7, 4) := by
  native_decide

/-- C0 max through L1. -/
theorem max_l1_eval_lt :
    run max 3 5 = some (false, false, 5, 5) := by
  native_decide

theorem max_l1_eval_ge :
    run max 7 2 = some (false, false, 7, 2) := by
  native_decide

/-- Pure L2 Skip pack matches env (AC L2 skip). -/
theorem l2_skip_pack :
    (do
      let e ← L2.fusedFromCom? (sc := ctx) (proc := Proc) (fault := Fault) locals .Skip
      eval_L2 e (w 3) (w 4)) = some (w 3, w 4) := by
  native_decide

/-- Pure L2 add agrees with L1 Normal outcome locals. -/
theorem l2_add_agrees_l1 :
    (do let s ← add_fusedL2; eval_L2 s (w 3) (w 4)) = some (w 7, w 4) ∧
    run add 3 4 = some (false, false, 7, 4) := by
  native_decide


-- Dialect pins (AC state/monad shape)
theorem dialect_l1_full : (l1Dialect 2).State = FullState := rfl
theorem dialect_l2_globals : (l2Dialect 2).State = Globals := rfl
theorem dialect_live_Id : (l1Dialect 2).ctx.primCtx.M = Id := rfl
theorem dialect_l2_keeps_heap :
    (l2Dialect 2).primFns.contains "heap.load" = true := by native_decide
theorem dialect_hl_w :
    (hlDialect 2).primFns.contains "heap.w.get" = true := by native_decide
theorem dialect_wa_add :
    (waDialect 2).primFns.contains "add" = true := by native_decide

theorem project_globals_heap :
    (projectGlobals ⟨[w 1, w 2], ⟨[w 9]⟩⟩).heap = [w 9] := rfl

-- Missing phases are explicit data, not constant-none translators.
theorem l2_is_unavailable :
    Lang.Simple.Lift.l2Availability.reason =
      "Deep-SSA LocalVarExtract has no structural proof-producing translator" := rfl

theorem hl_is_unavailable :
    Lang.Simple.Lift.hlAvailability.reason =
      "HeapLift lacks generated lifted globals and typed-heap proofs" := rfl

theorem wa_is_unavailable :
    Lang.Simple.Lift.waAvailability.reason =
      "WordAbstract syntax rewrites lack evaluator-backed corresTA proofs" := rfl

theorem ts_is_unavailable :
    Lang.Simple.Lift.tsAvailability.reason =
      "TypeStrengthen has no retyped generated definition" := rfl

/-!
  ## AC `ac_corres_chain` — AutoCorres.thy:78–85

  There is deliberately **no chain instance here yet.**

  The previous chain instance in this file was rejected by the type checker — it populated the five slots with *four unrelated programs* across two
  incompatible routes (`Skip`/`Throw` for L1, the fused `fusedFromCom?` helper for
  L2, a hand-written `heapLoad` for HL, and a WA result whose input never went
  through HL), and four of its five slots were `.isSome` facts or `True` rather
  than correspondences.

  `Corres.lean` now contains the upstream-shaped result-set/failure-bit
  `CorresXF` relation and its merge theorem. There is no synthetic chain
  schema: the real `ac_corres_chain` must use actual L1/L2/HL/WA/TS premises.

  An instance needs the per-phase corres theorems for the *actual* translators,
  which do not exist yet (see AC_NOTES). The individual execution facts the old
  instance bundled are still asserted above and in `Test/L1.lean`.
-/

/-- No fuel: While lowers via `loopBody`/`recurse` shape. -/
theorem while_lowers_no_fuel :
    (toSSA? (ctx := ctx) (proc := Proc) (fault := Fault)
      (.While boolFalse .Skip)).isSome = true := by
  native_decide

/-! ## AC phase enum — function_info.ML:135 -/

open Lang.Simple.Dialect (Phase dialectOf)

theorem phases_are_ac_enum :
    Phase.pipeline.map Phase.toName = ["CP", "L1", "L2", "HL", "WA", "TS"] := by
  decide

theorem every_phase_has_a_dialect (p : Phase) : (dialectOf 2 p).phase = p :=
  Lang.Simple.Dialect.dialectOf_phase 2 p

/-- CP is the C-parser/SIMPL tier; its dialect is the Simpl one. -/
theorem cp_is_simpl : dialectOf 2 .CP = simplDialect 2 := rfl

/-- Dialect checks inspect primitive functions nested inside raw terms. -/
theorem l2_rejects_nested_local_abi :
    Dialect.mentionsOk (l2Dialect 2)
      (.raw (.app (.primFunc "state.pack.2") [.var 0, .var 1])) = false := by
  native_decide

/-! ## AC pipeline options — autocorres.ML:35,44 -/

open Lang.Simple.Lift (Options)

/-- Default options run every phase (AC default: both skips off). -/
theorem default_options_run_everything :
    ({} : Options).skipHeapAbs = false ∧ ({} : Options).skipWordAbs = false := by
  decide

/-! ## WA leaves in AC's `abstract_binop` form — WordAbstract.thy:113–170 -/

open Lang.Simple.Lift.WA (AbstractBinop AbstractBoolBinop uwordMax
  unat_abstract_binop_add unat_abstract_binop_sub unat_abstract_bool_binop_lt)

/-- AC WordAbstract.thy:31 — `UWORD_MAX TYPE(32) = 2 ^ 32 - 1`. -/
theorem uword_max_32 : uwordMax = 4294967295 := by decide

/-- AC `unat_abstract_binops(1)` — WordAbstract.thy:166. -/
theorem wa_add_is_abstract_binop :
    AbstractBinop (fun a b => a + b ≤ uwordMax) Word.toNat (· + ·) (· + ·) :=
  unat_abstract_binop_add

/-- AC `unat_abstract_binops(3)` — WordAbstract.thy:168. -/
theorem wa_sub_is_abstract_binop :
    AbstractBinop (fun a b => b ≤ a) Word.toNat (· - ·) (· - ·) :=
  unat_abstract_binop_sub

/-- AC `unat_abstract_bool_binops(1)` — WordAbstract.thy:154 (no side condition). -/
theorem wa_lt_is_abstract_bool_binop :
    AbstractBoolBinop (fun _ _ => True) Word.toNat
      (fun a b => decide (a < b)) (fun a b => decide (BitVec.ult a b)) :=
  unat_abstract_bool_binop_lt

/-- The add law is not vacuous: it fires below the bound and the guard bites above it. -/
example : (w 3 + w 4).toNat = 3 + 4 :=
  wa_add_is_abstract_binop (w 3) (w 4) (by native_decide)

example : ¬ ((Word.toNat (w 4294967295) + Word.toNat (w 1)) ≤ uwordMax) := by
  native_decide

/-! ## WA emits AC's overflow guard — WordAbstract.thy:166,168 -/

private def waAdd : Option (Zag.Lang.SSA.SSAExpr abstractNatCtx.primCtx) := do
  let l2 ← add_fusedL2
  Lang.Simple.Lift.WA.rewriteUnsigned? abstractNatCtx waFuncMap l2

private def evalWA (x y : Nat) : Option (Zag.Val abstractNatCtx.primCtx) := do
  let e ← waAdd
  let t ← Zag.Lang.SSA.SSAExpr.toTerm? e { vars := [("x", .var 0), ("y", .var 1)] }
  let value? ← Zag.Term.eval abstractNatCtx [Zag.Val.nat x, Zag.Val.nat y] t
  value?

/-- Below `UWORD_MAX` the abstracted add computes. -/
theorem wa_add_in_range : (evalWA 3 4).isSome = true := by native_decide

/--
  **Regression.** Above `UWORD_MAX` the guard fires and the abstract body
  *fails*, rather than returning `2^32` where the concrete `BitVec 32` wraps
  to `0`. Before the guard was emitted this returned a wrong answer.
  AC: `unat_abstract_binops(1)`'s `a + b ≤ UWORD_MAX` — WordAbstract.thy:166,
  discharged by an `L2_guard` (`corresTA_L2_seq`, WordAbstract.thy:597–601).
-/
theorem wa_add_overflow_is_guarded :
    (evalWA 4294967295 1).isSome = false := by native_decide

/-- The concrete side really does wrap, so the guard is not vacuous. -/
theorem wa_concrete_wraps : (w 4294967295 + w 1).toNat = 0 := by native_decide

/-! ## TS monad-type ladder — TypeStrengthen.thy:81,145,231,323 -/

open Lang.Simple.Lift.TS (MonadType tierOf)

theorem ts_ladder_names :
    [MonadType.pure, .gets, .option, .nondet].map MonadType.name =
      ["pure", "gets", "option", "nondet"] := by decide

/-- AC's precedences, verbatim — TypeStrengthen.thy:85,149,235,327. -/
theorem ts_ladder_precedences :
    MonadType.ladder.map MonadType.precedence = [100, 80, 60, 0] := by decide

/-!
  The tier selection must *distinguish* programs, otherwise it is a constant
  dressed up as a ladder. One body per tier:
-/

private abbrev E := Zag.Lang.SSA.SSAExpr ctx.primCtx

/-- Computes only: AC `pure` (precedence 100, TypeStrengthen.thy:81). -/
theorem ts_pure_body : tierOf (Zag.Lang.SSA.SSAExpr.ret (.var "x") : E) = .pure := by
  native_decide

/-- Reads the heap: AC `gets` (precedence 80, TypeStrengthen.thy:145). -/
theorem ts_gets_body :
    tierOf (Zag.Lang.SSA.SSAExpr.ret
      (.call (.primFunc "heap.load") [.var "h", .var "p"]) : E) = .gets := by
  native_decide

/-- HL's validity guard can fail: AC `option` (precedence 60, :231). -/
theorem ts_option_body :
    tierOf (Zag.Lang.SSA.SSAExpr.let_ "v"
      (.call (.primFunc "heap.w.valid") [.var "h", .var "p"])
      (.ret (.var "v")) : E) = .option := by
  native_decide

/-- Writes the state: AC `nondet`, the default (precedence 0, :323). -/
theorem ts_nondet_body :
    tierOf (Zag.Lang.SSA.SSAExpr.ret
      (.call (.primFunc "heap.store") [.var "h", .var "p", .var "w"]) : E) = .nondet := by
  native_decide

/-- The four tiers are actually distinguished (not one constant). -/
theorem ts_tiers_are_distinct :
    [tierOf (Zag.Lang.SSA.SSAExpr.ret (.var "x") : E),
     tierOf (.ret (.call (.primFunc "heap.load") [.var "h", .var "p"]) : E),
     tierOf (.let_ "v" (.call (.primFunc "heap.w.valid") [.var "h", .var "p"])
       (.ret (.var "v")) : E),
     tierOf (.ret (.call (.primFunc "heap.store") [.var "h", .var "p", .var "w"]) : E)]
      = [.pure, .gets, .option, .nondet] := by
  native_decide

/-- L1 bodies still carry raw Simpl state reads, so they are not `pure`. -/
theorem ts_l1_body_is_not_pure :
    (do let e ← toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) add
        some (tierOf e)) ≠ some .pure := by
  native_decide

/-! ## L2corres `st` = projectGlobals — L2Defs.thy:85–91 -/

open Lang.Simple.Lift.L2 (stOfFull? stOfFull_isSome stOfFull_eq_globals)

/-- `st` is total on `State` values, for every state — not just tested ones. -/
theorem l2_st_total (s : FullState) : (stOfFull? (State.valFull s)).isSome = true :=
  stOfFull_isSome s

/-- `st` keeps globals, drops locals — the content of the extract. -/
theorem l2_st_projects (s : FullState) : stOfFull? (State.valFull s) = some s.globals :=
  stOfFull_eq_globals s

end Zag.Test.AutoCorres
