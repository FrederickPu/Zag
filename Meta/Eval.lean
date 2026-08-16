import Lib.Peano.Eval
import Zag.EvalState

/-!
# Small-step evaluation tactics

`evaluates` runs a closed `EvaluatesTo` goal with bounded fuel. `evaluates_call` proves block
specifications stated as `EvaluatesCall`; recursive proofs splice an induction hypothesis with
`EvaluatesFrom.call_then` when the machine reaches the recursive call.
-/

namespace Zag

/-- Run the small-step machine until it stops, discharging `EvaluatesTo`.

  `fuel` only has to be an upper bound -- `EvalState.run` halts early, so over-estimating is
  free. The lemmas to pass are the program's own: its operator context (`natOpCtx`, `heapOpCtx`,
  ..) and its block list. Everything context-independent is already in the set below.

  Symbolic *leaves* are fine -- `add [nat x, nat 1]` runs to `Val.nat (x + 1)`. Symbolic
  *control flow* is not: a branch on an unknown condition, or a recursive call with an unknown
  bound, stops and needs a case split or an induction hypothesis. -/
syntax (name := evaluatesTactic) "evaluates" num
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallTactic) "evaluates_call" num
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesToAllTactic) "evaluates_to_all" num
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesFromTactic) "evaluates_from" num
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
| `(tactic| evaluates_to_all $fuel:num [$lemmas,*]) =>
    `(tactic|
      first
      | exact Zag.EvaluatesToAll.nil
      | constructor
        · evaluates $fuel [$lemmas,*]
        · evaluates_to_all $fuel [$lemmas,*])
| `(tactic| evaluates_from $fuel:num [$lemmas,*]) => do
    let n := fuel.getNat
    if n == 0 then
      `(tactic| exact Zag.EvaluatesFrom.done)
    else
      let nextFuel := Lean.Syntax.mkNumLit (toString (n - 1))
      `(tactic|
        first
        | exact Zag.EvaluatesFrom.done
        | (apply Zag.EvaluatesFrom.step
           · set_option linter.unusedSimpArgs false in
               simp +arith [Zag.EvalState.step, Zag.EvalState.driveOp,
                 Zag.EvalState.enterInstrs, Zag.EvalState.enterBlock, Zag.OpCtx.get?,
                 Zag.BlockCtx.get?, Zag.BlockCtx.Raw.get?, Zag.Scope.get?, Zag.Block.entryEnv,
                 Zag.Peano.opCtx, Zag.Op.natBinary, Zag.Op.natUnary, Zag.Op.compare,
                 Zag.Op.eq, Zag.Op.ite, Zag.Op.ofVals, Zag.Op.Body.eager, Zag.Term.nat,
                 Zag.Term.bool, Zag.Term.ite, $lemmas,*] <;> rfl
           · evaluates_from $nextFuel [$lemmas,*]))
| `(tactic| evaluates_call $fuel:num [$lemmas,*]) =>
    `(tactic|
      focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [Zag.EvalState.enterInstrs,
            Zag.EvalState.enterBlock, Zag.BlockCtx.get?, Zag.BlockCtx.Raw.get?,
            Zag.Scope.get?, Zag.Block.entryEnv, Zag.Term.nat, Zag.Term.bool, Zag.Term.ite,
            $lemmas,*]
        evaluates_from $fuel [$lemmas,*])

end Zag
