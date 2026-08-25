import Test.Autocorres.Examples.MultByAddEvalManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

/-! A direct semantic proof of `multByAdd_eval_call`, using the manual value-level call
specification and explicit literal evaluation. -/

theorem multByAdd_eval_call_manual (x y : Nat) :
    Exact.EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  have h : Exact.EvaluatesCallValues multByAddCtx "multByAdd"
      ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x * y)) := by
    simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
      using multByAdd_eval_manual x y
  apply EvaluatesTo.call h
  · rfl
  · exact EvaluatesList.cons
      (evaluates_nat _ x)
      (EvaluatesList.cons
        (evaluates_nat _ y)
        EvaluatesList.nil)

end Zag.Test.Autocorres.Examples
