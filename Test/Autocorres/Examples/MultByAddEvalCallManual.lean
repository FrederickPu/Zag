import Test.Autocorres.Examples.MultByAddEvalManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap Zag.EvalTriple.Exact

private abbrev heapOpCtx := pureHeapOpCtx

/-! A direct semantic proof of `multByAdd_eval_call`, using the manual value-level call
specification and explicit literal evaluation. -/

theorem multByAdd_eval_call_manual (x y : Nat) :
    EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  apply EvaluatesTo.call (multByAdd_eval_manual x y)
  · rfl
  · exact EvaluatesList.cons
      (evaluates_nat _ x)
      (EvaluatesList.cons
        (evaluates_nat _ y)
        EvaluatesList.nil)

end Zag.Test.Autocorres.Examples
