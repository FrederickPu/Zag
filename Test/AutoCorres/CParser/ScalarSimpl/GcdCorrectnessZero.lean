import Test.AutoCorres.CParser.ScalarSimpl.GcdCorrectnessModel

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

theorem gcd_resolved_executes_zero (b : GcdWord32) :
    gcdFunction.Exec (gcdInitial 0 b)
      (.normal (gcdReturnedState (gcdABState 0 b) b)) := by
  apply Function.Exec.returned
  rw [gcd_is_exact_resolved_function]
  apply Stmt.Exec.seqNormal
  · exact Stmt.Exec.declare 3 u32
  · rw [gcd_declared_state]
    apply Stmt.Exec.seqNormal
    · unfold gcdLoop
      exact Stmt.Exec.whileFalse (gcd_condition_zero b)
    · apply Stmt.Exec.seqReturned
      apply Stmt.Exec.ret
      exact gcdAB_read_b 0 b

end Zag.Test.AutoCorres.CParser.ScalarSimpl
