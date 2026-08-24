import Test.Autocorres.Examples.MultByAddLoopManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap Zag.EvalTriple.Exact

private abbrev heapOpCtx := pureHeapOpCtx

/-! A direct semantic proof of `multByAdd_eval`. The wrapper block is assembled from its block
body and the apply-only loop specification, without evaluator tactics. -/

theorem multByAdd_eval_manual (x y : Nat) :
    EvaluatesCallValues multByAddCtx "multByAdd" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x * y)) := by
  apply EvaluatesCallValues.of_evaluatesInstrs
    (name := "multByAdd") (block := multByAddBlocks[0].2)
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  apply EvaluatesTo.call
  · have hloop := multByAddLoop_eval_manual y x 0
    rw [Nat.zero_add] at hloop
    exact hloop
  · rfl
  · exact EvaluatesList.cons
      (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons
        (EvaluatesTo.var_local (by rfl))
        (EvaluatesList.cons
          (evaluates_nat _ 0)
          EvaluatesList.nil))

end Zag.Test.Autocorres.Examples
