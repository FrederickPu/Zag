import Test.AutoCorres.CParser.ScalarSimpl.GcdRemainderEval
import Test.AutoCorres.CParser.ScalarSimpl.GcdExecution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

theorem gcd_condition_zero_abc (b c : GcdWord32) :
    gcdCondition.eval (gcdABCState 0 b c) = some 0 := by
  have zeroU : u32.cast 0 = 0 := by native_decide
  have zeroS : s32.cast 0 = 0 := by native_decide
  simp [gcdCondition, Expr.eval, gcdABC_read_a, zeroU, zeroS]

theorem gcd_loop_body_exec_abc (a b c : GcdWord32) (nonzero : a ≠ 0) :
    Stmt.Exec gcdLoopBody (gcdABCState a b c)
      (.normal (gcdABCState (b % a) a a)) := by
  unfold gcdLoopBody
  apply Stmt.Exec.seqNormal
  · apply Stmt.Exec.seqNormal
    · exact Stmt.Exec.assign 3 u32 (.variable u32 1) (gcdABC_read_a a b c)
    · rw [gcdABC_set_c]
      apply Stmt.Exec.seqNormal
      · exact Stmt.Exec.assign 1 u32 gcdRemainder
          (gcd_remainder_eval a b a nonzero)
      · rw [gcdABC_set_a]
        apply Stmt.Exec.seqNormal
        · exact Stmt.Exec.assign 2 u32 (.variable u32 3)
            (gcdABC_read_c (b % a) b a)
        · rw [gcdABC_set_b]
          exact Stmt.Exec.skip
  · exact Stmt.Exec.skip

theorem gcd_loop_body_exec_ab (a b : GcdWord32) (nonzero : a ≠ 0) :
    Stmt.Exec gcdLoopBody (gcdABState a b)
      (.normal (gcdABCState (b % a) a a)) := by
  unfold gcdLoopBody
  apply Stmt.Exec.seqNormal
  · apply Stmt.Exec.seqNormal
    · exact Stmt.Exec.assign 3 u32 (.variable u32 1) (gcdAB_read_a a b)
    · rw [gcdAB_set_c]
      apply Stmt.Exec.seqNormal
      · exact Stmt.Exec.assign 1 u32 gcdRemainder
          (gcd_remainder_eval a b a nonzero)
      · rw [gcdABC_set_a]
        apply Stmt.Exec.seqNormal
        · exact Stmt.Exec.assign 2 u32 (.variable u32 3)
            (gcdABC_read_c (b % a) b a)
        · rw [gcdABC_set_b]
          exact Stmt.Exec.skip
  · exact Stmt.Exec.skip

end Zag.Test.AutoCorres.CParser.ScalarSimpl
