import Test.AutoCorres.CParser.ScalarSimpl.GcdLoopExecution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

set_option maxRecDepth 100000

theorem gcd_loop_exec_ab_zero (b : GcdWord32) :
    Stmt.Exec gcdLoop (gcdABState 0 b) (.normal (gcdABState 0 b)) := by
  unfold gcdLoop
  exact Stmt.Exec.whileFalse (gcd_condition_zero b)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
