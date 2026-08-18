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

example : EvaluatesTo peanoCtx [] (.op "add" [Term.nat 3, Term.nat 4]) (Val.nat 7) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-- Only the leaves are symbolic; the control flow is still concrete, so the machine runs. -/
example (x : Nat) :
    EvaluatesTo peanoCtx [] (.op "add" [Term.nat x, Term.nat 1]) (Val.nat (x + 1)) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-- `ite` is lazy, and the machine keeps it that way: the untaken branch is never stepped. -/
example : EvaluatesTo peanoCtx [] (Term.ite (Term.bool false) (Term.nat 1) (Term.nat 2))
    (Val.nat 2) := by
  evaluates 20 [natOpCtx, Op.fixed]

/-! ### blocks, including a recursive one -/

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

/-! ### evaluator regression tests

  These are the same programs `Test/Exit.lean` and `Test/Gauss.lean` exercise with `#guard`, but
  stated here as `EvaluatesTo` facts so the machine itself carries the regression coverage. -/

end Zag.Test.EvalState
