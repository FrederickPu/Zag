import Test.Autocorres.Examples.MultByAddLoopManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

/-! A direct semantic proof of `multByAdd_eval`. The wrapper block is assembled from its block
body and the apply-only loop specification, without evaluator tactics. -/

private theorem multByAdd_eval_manual_exact (x y : Nat) :
    Exact.EvaluatesCallValues multByAddCtx "multByAdd"
      ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x * y)) := by
  have hloop : Exact.EvaluatesCallValues multByAddCtx "multByAddLoop"
      ([Val.nat y, Val.nat x, Val.nat 0] : List (Val heapCtx))
      (Val.nat (x * y)) := by
    simpa [Nat.zero_add, Exact.EvaluatesCallValues, Exact.pre, Exact.post,
      Singleton.idPre, Singleton.idPost] using multByAddLoop_eval_manual y x 0
  apply EvaluatesCallValues.of_evaluatesInstrs
    (name := "multByAdd") (block := multByAddBlocks[0].2)
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call hloop (by rfl)
    (EvaluatesList.cons (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl))
        (EvaluatesList.cons (evaluates_nat _ 0) EvaluatesList.nil)))

theorem multByAdd_eval_manual (x y : Nat) :
    Zag.EvaluatesCallValues multByAddCtx "multByAdd"
      ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x * y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using multByAdd_eval_manual_exact x y

end Zag.Test.Autocorres.Examples
