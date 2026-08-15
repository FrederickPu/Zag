import Lib.Peano.Eval
import Zag.EvalState

/-!
# `concretize` -- proof automation for evaluating a term against a concretization context

`concretize` discharges goals of the form

```
Term.eval ctx env t = some value
Term.evalCall ctx name vargs = some value
Block.run ctx env instrs result = some value
```

by rewriting with the evaluation calculus (`Zag/Eval.lean`, `Lib/Peano/Eval.lean`). The
*concretization context* is `env`: it says what value each bound variable of `t` stands for.
Those values may mention Lean variables, so what comes out is a symbolic expression rather than
a literal -- with `x` and `y` bound to `Val.nat x` and `Val.nat y`, the term `op "add" [x, y]`
concretizes to `Val.nat (x + y)`.

Extra arguments are handed to `simp`. Two kinds are worth passing:

* another block's specification (`Term.evalCall ctx name vargs = some ..`), which is how one
  block's proof reuses another's;
* an induction hypothesis, which is the same thing for a *recursive* call, and is the only way
  such a call is ever discharged.

Whatever arithmetic is left over belongs to the caller -- `concretize` evaluates the program, it
does not do number theory.
-/

namespace Zag

syntax (name := concretizeTactic) "concretize" (" [" Lean.Parser.Tactic.simpLemma,* "]")? :
  tactic

/- Two steps alternate until neither applies: `simp` with the evaluation calculus (all of which
  is already `@[simp]`; what is added here is how to compute a scope lookup and an entry
  environment), and stepping into a callee's body once a call has been reduced to its argument
  values. The callee is found by `rfl`, not by rewriting, so the goal never mentions the program
  text.

  Rewriting comes first on purpose. A recursive call is discharged by an induction hypothesis,
  which is a rewrite; stepping into the block instead would unfold one iteration too many and
  leave the hypothesis with nothing to match. -/
macro_rules
| `(tactic| concretize) => `(tactic| concretize [])
| `(tactic| concretize [$lemmas,*]) =>
    `(tactic|
      focus
        repeat (first
          | simp +arith [Scope.get?_cons, Scope.get?_append_singleton, Block.entryEnv,
              $lemmas,*]
          | refine Zag.Term.evalCall_of_run rfl rfl ?_))

/-- Run the small-step machine until it stops, discharging `EvaluatesTo`.

  `fuel` only has to be an upper bound -- `EvalState.run` halts early, so over-estimating is
  free. The lemmas to pass are the program's own: its operator context (`natOpCtx`, `heapOpCtx`,
  ..) and its block list. Everything context-independent is already in the set below.

  Symbolic *leaves* are fine -- `add [nat x, nat 1]` runs to `Val.nat (x + 1)`. Symbolic
  *control flow* is not: a branch on an unknown condition, or a recursive call with an unknown
  bound, stops and needs a case split or an induction hypothesis. -/
syntax (name := evaluatesTactic) "evaluates" num
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
| `(tactic| evaluates $fuel:num [$lemmas,*]) =>
    `(tactic|
      refine ⟨$fuel, ?_⟩ <;>
      set_option linter.unusedSimpArgs false in
        simp +arith [Zag.EvalState.run, Zag.EvalState.step, Zag.EvalState.start,
          Zag.EvalState.result?, Zag.EvalState.driveOp, Zag.EvalState.enterInstrs,
          Zag.EvalState.enterBlock, Zag.OpCtx.get?, Zag.BlockCtx.get?, Zag.BlockCtx.Raw.get?,
          Zag.Scope.get?, Zag.Block.entryEnv, Zag.Peano.opCtx, Zag.Op.natBinary,
          Zag.Op.natUnary, Zag.Op.compare, Zag.Op.eq, Zag.Op.ite, Zag.Op.ofVals,
          Zag.Op.Body.eager, Zag.Term.nat, Zag.Term.bool, Zag.Term.ite, $lemmas,*])

end Zag
