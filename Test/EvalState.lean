import Meta.Eval
import Zag.EvalState
import Test.Gauss
import Test.Exit

/-!
The small-step evaluator, checked against the same programs the big-step one runs.

`EvaluatesTo` is proved the way you would hope: point the machine at the term and keep stepping
until it stops. That is one tactic unfolding *one* function, where the big-step calculus needs a
rule per term former and a rule per operator.

`rfl` and `decide` cannot do the running, even though `EvalState.step` is structural: a `Val`
carries a `Ty.type primCtx ty`, `Ty.type` is well-founded and `Type`-valued, and the `cast`s
that go with it do not reduce definitionally. So the driver is `simp`, which gets through them
with the `Peano` lemmas that already exist.
-/

namespace Zag.Test.EvalState

open Zag Zag.Lib.Peano

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
    EvaluatesFrom (authoredCtx enabled value) ⟨.eval (.op "authored" []), env, base⟩ value base := by
  evaluates_from [authoredCtx, authoredOp, Op.fixed, h]

/-- Finalizer selection accepts a reducible name, matching the legacy tactic's behavior. -/
example {primCtx : PrimitiveCtx} {enabled : Bool} {value : Val primCtx}
    (h : enabled = true) (env : Env primCtx) (base : List (Frame primCtx)) :
    EvaluatesFrom (authoredCtx enabled value) ⟨.eval (.op "authored" []), env, base⟩ value base := by
  evaluates_from [authoredCtx, authoredOp, Op.fixed, h]
    finalizing_at_op authoredName with (refine EvaluatesFrom.atOp ?_)
  evaluates_from [authoredCtx, authoredOp, Op.fixed, h]

example : EvaluatesTo peanoCtx [] (.op "add" [Term.nat 3, Term.nat 4]) (Val.nat 7) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-- Only the leaves are symbolic; the control flow is still concrete, so the machine runs. -/
example (x : Nat) :
    EvaluatesTo peanoCtx [] (.op "add" [Term.nat x, Term.nat 1]) (Val.nat (x + 1)) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-- Registered semantics evaluates a symbolic operator without unfolding its machine body. -/
example (a b : Nat) (env : Env peanoCtx.primCtx) (base : List (Frame peanoCtx.primCtx)) :
    EvaluatesFrom peanoCtx
      ⟨.eval (.op "add" [Term.nat a, Term.nat b]), env, base⟩ (Val.nat (a + b)) base := by
  evaluates_from 1 [natOpCtx]

/-- Semantic recursion resolves known local operands before applying the operator rule. -/
example (a b : Nat) (env : Env peanoCtx.primCtx) (base : List (Frame peanoCtx.primCtx))
    (ha : Scope.get? env "a" = some (Val.nat a))
    (hb : Scope.get? env "b" = some (Val.nat b)) :
    EvaluatesFrom peanoCtx
      ⟨.eval (.op "add" [.var "a", .var "b"]), env, base⟩ (Val.nat (a + b)) base := by
  evaluates_from 1 [natOpCtx, ha, hb]

/-- A same-named operator without `Peano.Model` must use its actual machine semantics. -/
example (a b : Nat) (env : Env subtractCtx.primCtx)
    (base : List (Frame subtractCtx.primCtx)) :
    EvaluatesFrom subtractCtx
      ⟨.eval (.op "add" [Term.nat a, Term.nat b]), env, base⟩ (Val.nat (a - b)) base := by
  evaluates_from 20 [subtractCtx, subtractOpCtx, Op.fixed]

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
    (Val.nat 2) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-! ### blocks, including a recursive one -/

/-- A block body is a left-to-right sequence: each result is bound before the tail is proved. -/
example : EvaluatesInstrs peanoCtx
    [Instr.ofTerm "x" (Term.nat 3),
      Instr.ofTerm "y" (.op "add" [.var "x", Term.nat 4])]
    (.var "y") [] (Val.nat 7) := by
  refine .cons (instrValue := Val.nat 3) ?_ ?_
  · evaluates 5 [natOpCtx, Op.fixed]
  refine .cons (instrValue := Val.nat 7) ?_ ?_
  · evaluates 20 [natOpCtx, Op.fixed]
  exact .nil (EvaluatesTo.var_local (by rfl))

open Zag.Test.Gauss in
example : EvaluatesTo gaussCtx [] (.call "gauss" [Term.nat 3]) (Val.nat 6) := by
  evaluates 300 [natOpCtx, Op.fixed, Op.whileOp, Op.Body.collect,
    Op.whileBodyFromValues, Op.whileAfterCondition, Op.whileResultTy?, gaussBlocks]

open Zag.Test.Gauss in
example : EvaluatesTo gaussCtx [] (.call "gauss" [Term.nat 5]) (Val.nat 15) := by
  evaluates 600 [natOpCtx, Op.fixed, Op.whileOp, Op.Body.collect,
    Op.whileBodyFromValues, Op.whileAfterCondition, Op.whileResultTy?, gaussBlocks]

/-! ### non-local exit

  `clamp` returns early via `exit clamp nat(10)`, so the machine must unwind past the pending
  instruction frame and stop at the `Frame.call` named `clamp` -- and must *not* reach `ret n`.
  This is the case the old big-step result type existed to encode. -/

open Zag.Test.Exit in
example : EvaluatesTo clampCtx [] (.call "clamp" [Term.nat 3]) (Val.nat 3) := by
  evaluates 200 [natOpCtx, Op.fixed, clampBlocks]

open Zag.Test.Exit in
example : EvaluatesTo clampCtx [] (.call "clamp" [Term.nat 42]) (Val.nat 10) := by
  evaluates 200 [natOpCtx, Op.fixed, clampBlocks]

/- The normal-completion instruction WP does not replace the machine path for an early exit. -/
open Zag.Test.Exit in
example : EvaluatesCall clampCtx "clamp" ([Val.nat 42] : List (Val natCtx)) (Val.nat 10) := by
  evaluates_call 200 [natOpCtx, Op.fixed, clampBlocks]

/-! ### evaluator regression tests

  These are the same programs `Test/Exit.lean` and `Test/Gauss.lean` exercise with `#guard`, but
  stated here as `EvaluatesTo` facts so the machine itself carries the regression coverage. -/

end Zag.Test.EvalState
