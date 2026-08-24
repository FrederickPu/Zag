import Test.Autocorres.Examples.MultByAdd

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap Zag.EvalTriple
open scoped Std.Do

/-- Performance-baseline alias of multByAddLoop_eval. -/
theorem multByAddLoop_eval_manual (x remaining acc : Nat) :
    Zag.EvaluatesCallValues multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (fun v => v = Val.nat (acc + remaining * x))) :=
  multByAddLoop_eval x remaining acc

end Zag.Test.Autocorres.Examples