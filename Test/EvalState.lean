import Meta.Eval
import Zag.EvalState
import Test.Gauss
import Test.Gauss.Rec
import Test.Exit

/-!
The small-step evaluator, checked against the same programs the big-step one runs.

`EvaluatesTo` is proved the way you would hope: point the machine at the term and keep stepping
until it stops. That is one tactic unfolding *one* function, where the big-step calculus needs a
rule per term former and a rule per operator.

`rfl` and `decide` cannot do the running, even though `Machine.step` is structural: a `Val`
carries a `Ty.type primCtx ty`, `Ty.type` is well-founded and `Type`-valued, and the `cast`s
that go with it do not reduce definitionally. So the driver is `simp`, which gets through them
with the `Peano` lemmas that already exist.
-/

namespace Zag.Test.EvalState

open Zag Zag.Lib.Peano
open Zag.EvalTriple.Exact

set_option maxRecDepth 100000

/-! ### operators -/

private def authoredBody {primCtx : PrimitiveCtx} (enabled : Bool) (value : Val primCtx) :
    Op.Body primCtx :=
  if enabled then .done value else .fail

@[eval_step] private theorem authoredBody_true {primCtx : PrimitiveCtx} {enabled : Bool}
    {value : Val primCtx} (h : enabled = true) :
    authoredBody enabled value = .done value := by
  simp [authoredBody, h]

attribute [irreducible] authoredBody

private def authoredOp {primCtx : PrimitiveCtx} (enabled : Bool) (value : Val primCtx) :
    Op primCtx :=
  Op.fixed 0 (fun _ => some value.ty) (authoredBody enabled value)

private abbrev authoredCtx {primCtx : PrimitiveCtx} (enabled : Bool) (value : Val primCtx) : Ctx :=
  { primCtx := primCtx, opCtx := [("authored", authoredOp enabled value)] }

private def authoredName : String := "authored"

private def subtractOpCtx : OpCtx natCtx :=
  [("add", Op.natBinary Nat.sub)]

private abbrev subtractCtx : Ctx where
  primCtx := natCtx
  opCtx := subtractOpCtx

/-- An operator-authored non-rfl rule exposes the irreducible body before generic driving. -/
example {primCtx : PrimitiveCtx} {enabled : Bool} {value : Val primCtx}
    (h : enabled = true) (env : Env primCtx) (base : List (Frame primCtx)) :
    EvaluatesFrom (authoredCtx enabled value) ⟨.eval (.op "authored" []), env, base⟩ value base
      (hM := rfl) := by
  exact (EvaluatesTo.op_applyVals (ctx := authoredCtx enabled value) (env := env)
    (oper := authoredOp enabled value) (values := []) (result := value) rfl
    EvaluatesList.nil (by
      simp [Op.applyValsAt, authoredOp, Op.fixed, authoredBody_true h,
        Op.Body.applyVals])) base

/-- Finalizer selection accepts a reducible name, matching the legacy tactic's behavior. -/
example {primCtx : PrimitiveCtx} {enabled : Bool} {value : Val primCtx}
    (h : enabled = true) (env : Env primCtx) (base : List (Frame primCtx)) :
    EvaluatesFrom (authoredCtx enabled value) ⟨.eval (.op "authored" []), env, base⟩ value base
      (hM := rfl) := by
  exact (EvaluatesTo.op_applyVals (ctx := authoredCtx enabled value) (env := env)
    (oper := authoredOp enabled value) (values := []) (result := value) rfl
    EvaluatesList.nil (by
      simp [Op.applyValsAt, authoredOp, Op.fixed, authoredBody_true h,
        Op.Body.applyVals])) base

example : EvaluatesTo peanoCtx [] (.op "add" [Term.nat 3, Term.nat 4]) (Val.nat 7)
    (hM := rfl) := by
  exact evaluates_add_nat (evaluates_nat _ 3) (evaluates_nat _ 4)

/-- Only the leaves are symbolic; the control flow is still concrete, so the machine runs. -/
example (x : Nat) :
    EvaluatesTo peanoCtx [] (.op "add" [Term.nat x, Term.nat 1]) (Val.nat (x + 1))
      (hM := rfl) := by
  exact evaluates_add_nat (evaluates_nat _ x) (evaluates_nat _ 1)

/-- Registered semantics evaluates a symbolic operator without unfolding its machine body. -/
example (a b : Nat) (env : Env peanoCtx.primCtx) (base : List (Frame peanoCtx.primCtx)) :
    EvaluatesFrom peanoCtx
      ⟨.eval (.op "add" [Term.nat a, Term.nat b]), env, base⟩ (Val.nat (a + b)) base
      (hM := rfl) := by
  exact (evaluates_add_nat (evaluates_nat env a) (evaluates_nat env b)) base

/-- Semantic recursion resolves known local operands before applying the operator rule. -/
example (a b : Nat) (env : Env peanoCtx.primCtx) (base : List (Frame peanoCtx.primCtx))
    (ha : Scope.get? env "a" = some (Val.nat a))
    (hb : Scope.get? env "b" = some (Val.nat b)) :
    EvaluatesFrom peanoCtx
      ⟨.eval (.op "add" [.var "a", .var "b"]), env, base⟩ (Val.nat (a + b)) base
      (hM := rfl) := by
  exact (evaluates_add_nat (EvaluatesTo.var_local ha) (EvaluatesTo.var_local hb)) base

/-- A same-named operator without `Peano.Model` must use its actual machine semantics. -/
example (a b : Nat) (env : Env subtractCtx.primCtx)
    (base : List (Frame subtractCtx.primCtx)) :
    EvaluatesFrom subtractCtx
      ⟨.eval (.op "add" [Term.nat a, Term.nat b]), env, base⟩ (Val.nat (a - b)) base
      (hM := rfl) := by
  exact (EvaluatesTo.op_applyVals (ctx := subtractCtx) (env := env)
    (oper := Op.natBinary Nat.sub) (values := [Val.nat a, Val.nat b])
    (result := Val.nat (a - b)) rfl
    (EvaluatesList.cons (evaluates_nat env a)
      (EvaluatesList.cons (evaluates_nat env b) EvaluatesList.nil))
    (by simp [Op.applyValsAt, Op.natBinary, Op.ofVals, Op.fixed, Op.Body.eager,
      Op.Body.applyVals])) base

example (a b expected : Nat) :
    EvaluatesTo peanoCtx [] (.op "add" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a + b = expected := by
  exact evaluates_add_nat_iff

example (a b expected : Nat) :
    EvaluatesTo peanoCtx [] (.op "sub" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a - b = expected := by
  exact evaluates_sub_nat_iff

example (a b : Nat) :
    EvaluatesTo peanoCtx [] (.op "gt" [Term.nat a, Term.nat b]) (Val.bool true) ↔
      b < a := by
  rw [evaluates_gt_nat_iff]
  simp

/-- `ite` is lazy, and the machine keeps it that way: the untaken branch is never stepped. -/
example : EvaluatesTo peanoCtx [] (Term.ite (Term.bool false) (Term.nat 1) (Term.nat 2))
    (Val.nat 2) (hM := rfl) := by
  refine EvaluatesTo.op_applyVals
    (values := [Val.bool false, Val.nat 1, Val.nat 2]) (result := Val.nat 2)
    (Peano.Model.iteOp (ctx := peanoCtx)) ?_ ?_
  · exact EvaluatesList.cons (evaluates_bool [] false)
      (EvaluatesList.cons (evaluates_nat _ 1)
        (EvaluatesList.cons (evaluates_nat _ 2) EvaluatesList.nil))
  · simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

/-! ### blocks, including a recursive one -/

/-- A block body is a left-to-right sequence: each result is bound before the tail is proved. -/
example : EvaluatesInstrs peanoCtx
    [Instr.ofTerm "x" (Term.nat 3),
      Instr.ofTerm "y" (.op "add" [.var "x", Term.nat 4])]
    (.var "y") [] (Val.nat 7) (hM := rfl) := by
  refine .cons (instrValue := Val.nat 3) ?_ ?_
  · evaluates 5 [natOpCtx, Op.fixed]
  refine .cons (instrValue := Val.nat 7) ?_ ?_
  · exact evaluates_add_nat (EvaluatesTo.var_local (by rfl)) (evaluates_nat _ 4)
  exact .nil (EvaluatesTo.var_local (by rfl))

open Zag.Test.Gauss in
example : EvaluatesTo gaussCtx [] (.call "gauss" [Term.nat 3]) (Val.nat 6) (hM := rfl) := by
  have hgauss := Rec.gauss_eval 3
  change EvalTriple.Exact.EvaluatesCallValues (hM := rfl) gaussCtx "gauss"
    ([Val.nat 3] : List (Val natCtx)) (Val.nat (Rec.sumTo 3)) at hgauss
  refine EvaluatesTo.call
    (EvaluatesCallValues.of_eq hgauss (by
      rw [show Rec.sumTo 3 = 6 by decide])) rfl ?_
  exact EvaluatesList.cons (evaluates_nat _ 3) EvaluatesList.nil

open Zag.Test.Gauss in
example : EvaluatesTo gaussCtx [] (.call "gauss" [Term.nat 5]) (Val.nat 15) (hM := rfl) := by
  have hgauss := Rec.gauss_eval 5
  change EvalTriple.Exact.EvaluatesCallValues (hM := rfl) gaussCtx "gauss"
    ([Val.nat 5] : List (Val natCtx)) (Val.nat (Rec.sumTo 5)) at hgauss
  refine EvaluatesTo.call
    (EvaluatesCallValues.of_eq hgauss (by
      rw [show Rec.sumTo 5 = 15 by decide])) rfl ?_
  exact EvaluatesList.cons (evaluates_nat _ 5) EvaluatesList.nil

/-! ### non-local exit

  `clamp` returns early via `exit clamp nat(10)`, so the machine must unwind past the pending
  instruction frame and stop at the `Frame.call` named `clamp` -- and must *not* reach `ret n`.
  This is the case the old big-step result type existed to encode. -/

open Zag.Test.Exit in
example : EvaluatesTo clampCtx [] (.call "clamp" [Term.nat 3]) (Val.nat 3) (hM := rfl) := by
  apply EvaluatesTo.ofEvalFuel (fuel := 200)
  let result := Id.run (Machine.evalFuel (EvalTriple.Exact.idView clampCtx rfl) 200 []
    (.call "clamp" [Term.nat 3])).run
  change result = some (Val.nat 3)
  have hnat : result.bind Val.asNat? = some 3 := by native_decide
  cases hresult : result with
  | none => simp [hresult] at hnat
  | some value =>
      have hvalue : value.asNat? = some 3 := by simpa [hresult] using hnat
      rw [Val.eq_nat_of_asNat? hvalue]

open Zag.Test.Exit in
example : EvaluatesTo clampCtx [] (.call "clamp" [Term.nat 42]) (Val.nat 10) (hM := rfl) := by
  apply EvaluatesTo.ofEvalFuel (fuel := 200)
  let result := Id.run (Machine.evalFuel (EvalTriple.Exact.idView clampCtx rfl) 200 []
    (.call "clamp" [Term.nat 42])).run
  change result = some (Val.nat 10)
  have hnat : result.bind Val.asNat? = some 10 := by native_decide
  cases hresult : result with
  | none => simp [hresult] at hnat
  | some value =>
      have hvalue : value.asNat? = some 10 := by simpa [hresult] using hnat
      rw [Val.eq_nat_of_asNat? hvalue]

/- The normal-completion instruction VC does not replace the machine path for an early exit. -/
open Zag.Test.Exit in
example : EvaluatesCallValues clampCtx "clamp" ([Val.nat 42] : List (Val natCtx)) (Val.nat 10)
    (hM := rfl) := by
  intro callerEnv base
  let block := clampBlocks[0].2
  let state := Machine.enterInstrs block.instrs block.result
    (block.entryEnv [Val.nat 42]) (.call "clamp" callerEnv :: base)
  refine ⟨block, state, rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, state, block]
  · change EvalTriple.Exact.EvaluatesFrom clampCtx state (Val.nat 10) base rfl
    dsimp [state, block]
    evaluates_from 20 [Machine.enterInstrs, clampBlocks, natOpCtx, Op.fixed]

/-! ### evaluator regression tests

  These are the same programs `Test/Exit.lean` and `Test/Gauss.lean` exercise with `#guard`, but
  stated here as `EvaluatesTo` facts so the machine itself carries the regression coverage. -/

/-! ### ambient effects -/

private def tickOp : Op natCtx (StateM Nat) :=
  Op.effectful 0 (fun _ => some NatTy) fun
  | [] => fun state => (some (Val.nat state), state + 1)
  | _ => pure none

private def effectBlock : Block natCtx where
  params := []
  instrs := [Instr.ofTerm "first" (.op "tick" []), Instr.ofTerm "second" (.op "tick" [])]
  outTy := NatTy
  result := .var "second"

private def effectBlocks : BlockCtx natCtx where
  val := [("effects", effectBlock)]
  isValid := by
    simp [BlockCtx.Valid, effectBlock, Block.callNames, Instr.callNames, Term.callNames]

private abbrev effectCtx : Ctx where
  primCtx := natCtx
  M := StateM Nat
  monad := StateT.instMonad
  opCtx := [("tick", tickOp)]
  blockCtx := effectBlocks
  postShape := .arg Nat .pure
  wpMonad := inferInstance

/-- A named focused computation; its logical specifications do not expose the machine bound. -/
private def effectfulSequence : Machine.Effect effectCtx (Val natCtx) :=
  Machine.evalFuel effectCtx 20 [] (.call "effects" [])

/-- Consecutive instructions preserve and sequence both ambient state transitions. -/
theorem effectfulSequence_run :
    (match effectfulSequence.run 0 with
      | (some value, state) => (value.asNat?, state)
      | (none, state) => (none, state)) = (some 1, 2) := by
  native_decide

private theorem effectfulSequence_run_raw :
    effectfulSequence.run 0 = (some (Val.nat 1), 2) := by
  have h := effectfulSequence_run
  cases hrun : effectfulSequence.run 0 with
  | mk value? state =>
      cases value? with
      | none => simp [hrun] at h
      | some value =>
          simp [hrun] at h
          have hvalue : value.asNat? = some 1 := h.1
          have hstate : state = 2 := h.2
          rw [Val.eq_nat_of_asNat? hvalue, hstate]

/-- The bounded run constructs the corresponding fuel-free Hoare derivation. -/
theorem effectfulSequence_evaluates :
    EvalTriple.State.EvaluatesCall natCtx ([("tick", tickOp)] : OpCtx natCtx (StateM Nat))
      effectBlocks "effects" [] 0 (Val.nat 1) 2 := by
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  simpa [effectfulSequence, effectCtx, Machine.evalFuel] using effectfulSequence_run_raw

private def tickM : OptionT (StateM Nat) (Val natCtx) :=
  OptionT.mk fun state => (some (Val.nat state), state + 1)

/-- The focused, unbounded composition used for the VC statement. -/
private def twoTicksM : Machine.Effect effectCtx (Val natCtx) :=
  OptionT.bind tickM fun _ => tickM

/-- The same sequencing fact as a fuel-free `Std.Do` total-correctness statement. -/
theorem twoTicksM_triple :
    Std.Do.Triple twoTicksM
      (fun state => ULift.up (state = 0))
      (Std.Do.PostCond.noThrow (ps := .except PUnit (.arg Nat .pure))
        fun value finalState => ULift.up (value = Val.nat 1 ∧ finalState = 2)) := by
  simp [Std.Do.Triple, Std.Do.wp, twoTicksM, tickM, effectCtx,
    OptionT.mk, OptionT.run, OptionT.lift, OptionT.bind, OptionT.pure, StateT.mk, StateT.run,
    StateT.bind, StateT.pure,
    StateT.map, StateT.run_bind, StateT.run_pure, Id.run, Id.run_bind, Id.run_pure,
    Bind.bind, Functor.map, Option.elimM, monadLift, MonadLift.monadLift]

end Zag.Test.EvalState
