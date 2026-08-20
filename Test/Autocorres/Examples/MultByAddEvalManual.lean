import Test.Autocorres.Examples.MultByAddLoopManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! A direct semantic proof of `multByAdd_eval`. The wrapper block is assembled from its block
body and the apply-only loop specification, without evaluator tactics. -/

theorem multByAdd_eval_manual (x y : Nat) :
    EvaluatesCall multByAddCtx "multByAdd" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x * y)) := by
  apply EvaluatesCall.of_evaluatesInstrs
    (name := "multByAdd") (block := multByAddBlocks[0].2)
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  apply EvaluatesTo.call
  · have hloop := multByAddLoop_eval_manual x y 0
    rw [Nat.zero_add, Nat.mul_comm] at hloop
    exact hloop
  · rfl
  · exact EvaluatesToAll.cons
      (EvaluatesTo.var_local (by rfl))
      (EvaluatesToAll.cons
        (EvaluatesTo.var_local (by rfl))
        (EvaluatesToAll.cons
          (evaluates_nat _ 0)
          EvaluatesToAll.nil))

end Zag.Test.Autocorres.Examples
