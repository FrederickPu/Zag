import Test.Autocorres.Examples.MultByAddEvalManual

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! A direct semantic proof of `multByAdd_eval_call`, using the manual value-level call
specification and explicit literal evaluation. -/

theorem multByAdd_eval_call_manual (x y : Nat) :
    EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  apply EvaluatesTo.call (multByAdd_eval_manual x y)
  · rfl
  · exact EvaluatesToAll.cons
      (evaluates_nat _ x)
      (EvaluatesToAll.cons
        (evaluates_nat _ y)
        EvaluatesToAll.nil)

end Zag.Test.Autocorres.Examples
