import Test.AutoCorres.CParser.ScalarSimpl.GcdLoopBodyExecution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000

theorem gcd_loop_exec_abc (a b c : GcdWord32) :
    ∃ finalC, Stmt.Exec gcdLoop (gcdABCState a b c)
      (.normal (gcdABCState 0 (gcdWord a b) finalC)) := by
  induction a, b using gcdWord.induct generalizing c with
  | case1 b =>
      rw [gcdWord]
      exact ⟨c, by
        unfold gcdLoop
        exact Stmt.Exec.whileFalse (gcd_condition_zero_abc b c)⟩
  | case2 a b nonzero induction =>
      obtain ⟨finalC, rest⟩ := induction a
      rw [gcdWord, if_neg nonzero]
      exact ⟨finalC, Stmt.Exec.whileTrue (gcd_condition_nonzero a b c nonzero)
        (by decide) (gcd_loop_body_exec_abc a b c nonzero) rest⟩

end Zag.Test.AutoCorres.CParser.ScalarSimpl
