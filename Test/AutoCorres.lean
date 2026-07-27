import Lang.Simple
import Lib.Peano
import Test.L1

/-!
  Full AutoCorres pipeline demos: L1 → L2 → HL → WA → TS.
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

theorem add_lifts : add_L2.isSome = true := by native_decide
theorem max_lifts : max_L2.isSome = true := by native_decide

def w (n : Nat) : Word := Word.ofNat n

theorem add_eval_3_4 :
    (do let s ← add_L2; eval_L2 s (w 3) (w 4)) = some (w 7, w 4) := by
  native_decide

theorem max_eval_3_5 :
    (do let s ← max_L2; eval_L2 s (w 3) (w 5)) = some (w 5, w 5) := by
  native_decide

theorem max_eval_7_2 :
    (do let s ← max_L2; eval_L2 s (w 7) (w 2)) = some (w 7, w 2) := by
  native_decide

theorem add_wa : add_WA.isSome = true := by native_decide
theorem add_pipeline : add_full.isSome = true := by native_decide
theorem throw_catch_l1 : throwCatch_L1.isSome = true := by native_decide

-- L1 suite: Test/L1.lean (exception ladder)
example : True := trivial

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

-- HL (AC HeapLift)
open Lang.Simple.Lift (heapConcreteCtx chainHL? l1l2Chain? fullExnChain?)
def heapLoad : Zag.Lang.SSA.SSAExpr heapConcreteCtx.primCtx :=
  .ret (.call (.primFunc "heap.load") [.var "h", .var "p"])
theorem hl_demo : (chainHL? heapLoad).isSome = true := by native_decide

def heapStore : Zag.Lang.SSA.SSAExpr heapConcreteCtx.primCtx :=
  .ret (.call (.primFunc "heap.store") [.var "h", .var "p", .var "w"])
theorem hl_store : (chainHL? heapStore).isSome = true := by native_decide

-- L1→L2 LocalVarExtract (AC LocalVarExtract): shape + eval
open Lang.Simple.Lift.L2 (evalFromL1? fromL1?)

def runL1L2 (cmd : Com ctx Proc Fault) (x y : Nat) : Option (Nat × Nat) := do
  let l1 ← toSSA? (ctx := ctx) (proc := Proc) (fault := Fault) cmd
  let v ← evalFromL1? locals l1 (State.val [w x, w y])
  let tys := [WordTy, WordTy]
  let raw ← v.as? (.struct tys)
  let fields := cast (Zag.Ty.type.eq_5 ctx.primCtx tys) raw
  some (Word.toNat (State.toWord (fields ⟨0, by decide⟩)),
        Word.toNat (State.toWord (fields ⟨1, by decide⟩)))

theorem skip_l1l2 :
    (l1l2Chain? (ctx := ctx) (proc := Proc) (fault := Fault) locals
      (Com.Skip : Com ctx Proc Fault)).isSome = true := by
  native_decide

theorem skip_l1l2_eval :
    runL1L2 .Skip 3 4 = some (3, 4) := by
  native_decide

theorem throw_l1l2_eval_still_unpacks :
    runL1L2 .Throw 3 4 = some (3, 4) := by
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
      let e ← L2.fromCom? (sc := ctx) (proc := Proc) (fault := Fault) locals .Skip
      eval_L2 e (w 3) (w 4)) = some (w 3, w 4) := by
  native_decide

/-- Pure L2 add agrees with L1 Normal outcome locals. -/
theorem l2_add_agrees_l1 :
    (do let s ← add_L2; eval_L2 s (w 3) (w 4)) = some (w 7, w 4) ∧
    run add 3 4 = some (false, false, 7, 4) := by
  native_decide


theorem throw_catch_l1l2 :
    (l1l2Chain? (ctx := ctx) (proc := Proc) (fault := Fault) locals
      throwCatch).isSome = true := by
  native_decide

theorem skip_full_exn :
    (fullExnChain? (proc := Proc) (fault := Fault) 2 locals
      (Com.Skip : Com ctx Proc Fault)).isSome = true := by
  native_decide

-- Dialect pins (AC state/monad shape)
theorem dialect_l1_full : (l1Dialect 2).State = FullState := rfl
theorem dialect_l2_globals : (l2Dialect 2).State = Globals := rfl
theorem dialect_live_Id : (l1Dialect 2).ctx.primCtx.M = Id := rfl
theorem dialect_l2_keeps_heap :
    (l2Dialect 2).primFns.contains "heap.load" = true := by native_decide
theorem dialect_hl_w :
    hlDialect.primFns.contains "heap.w.get" = true := by native_decide
theorem dialect_wa_add :
    (waDialect 2).primFns.contains "add" = true := by native_decide

theorem project_globals_heap :
    (projectGlobals ⟨[w 1, w 2], ⟨[w 9]⟩⟩).heap = [w 9] := rfl

-- TS identity
theorem ts_id : (chainTS? abstractNatCtx
    (Zag.Lang.SSA.SSAExpr.ret (Zag.Lang.SSA.SSAValue.var "x"))).isSome = true := by
  native_decide

/-!
  ## AC `ac_corres_chain` — AutoCorres.thy:78–85

  There is deliberately **no chain instance here yet.**

  `Corres.AcCorresChain` now forces adjacency in its field types: `cL1` is the
  abstract side of the L2 link and the concrete side of the HL link, and so on.
  The previous instance in this file was rejected by the type checker once that
  landed — it populated the five slots with *four unrelated programs* across two
  incompatible routes (`Skip`/`Throw` for L1, the **pure** `fromCom?` route for
  L2, a hand-written `heapLoad` for HL, and a WA result whose input never went
  through HL), and four of its five slots were `.isSome` facts or `True` rather
  than correspondences.

  What is proved instead, in `Lang/Simple/Corres.lean`:

  * `Corres.CorresXF.merge` — CorresXF.thy:703–706, correspondence composes;
  * `Corres.AcCorresChain.resolve` — resolves L2∘HL∘WA into one `CorresXF`
    with AC's composed `st_HL ∘ st_L2` and `rx_WA ∘ rx_L2`.

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

/-! ## AC pipeline options — autocorres.ML:35,44 -/

open Lang.Simple.Lift (Options fullChain? chainHLOrSkip? chainWAOrSkip?)

/-- Default options run every phase (AC default: both skips off). -/
theorem default_options_run_everything :
    ({} : Options).skipHeapAbs = false ∧ ({} : Options).skipWordAbs = false := by
  decide

/-- `skip_word_abs`: the chain completes, staying on concrete words (`Sum.inl`). -/
theorem add_chain_skip_word_abs_is_concrete :
    ((fullChain? (proc := Proc) (fault := Fault)
      { skipWordAbs := true } 2 locals add).map Sum.isLeft) = some true := by
  native_decide

/--
  **Known gap** (AC_NOTES "real extract"): with `skip_word_abs` off, the
  `l1l2Chain?` route cannot reach WA for a body containing `Basic`.
  `fromL1?` runs the L1 body and *then* reads locals, so the L1 body's raw
  Simpl terms (`state.set.i`) survive into the WA input — and `waPrimCtx` has
  no `State` prim at all. AC's LocalVarExtract removes the state instead.
  Recorded here so the gap cannot silently close or silently widen.
-/
theorem add_chain_word_abs_blocked_by_run_then_gets :
    fullChain? (proc := Proc) (fault := Fault) {} 2 locals add = none := by
  native_decide

/-- The *pure* extract (`fromCom?`) is a real extract, so it does reach WA. -/
theorem add_pure_chain_reaches_wa :
    (fullPureChain? (proc := Proc) (fault := Fault) 2 locals add).isSome = true := by
  native_decide

/-- A `Basic`-free body survives the whole L1→L2→HL→WA→TS chain. -/
theorem skip_chain_word_abs_is_abstract :
    ((fullChain? (proc := Proc) (fault := Fault)
      {} 2 locals (Com.Skip : Com ctx Proc Fault)).map Sum.isRight) = some true := by
  native_decide

/-- Live HL accepts a heap-free body (so `skip_heap_abs` changes nothing here). -/
theorem heap_free_hl_succeeds :
    (do let l2 ← add_L2; chainHLOrSkip? {} l2).isSome = true := by
  native_decide

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
  let l2 ← add_L2; chainWA? 2 l2

private def evalWA (x y : Nat) : Option (Zag.Val abstractNatCtx.primCtx) := do
  let e ← waAdd
  let t ← Zag.Lang.SSA.SSAExpr.toTerm? e { vars := [("x", .var 0), ("y", .var 1)] }
  Zag.Term.eval abstractNatCtx [Zag.Val.nat x, Zag.Val.nat y] t

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
