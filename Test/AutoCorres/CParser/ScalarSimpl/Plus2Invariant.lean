import Test.AutoCorres.CParser.ScalarSimpl.Plus2Model

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

/-- The upstream word invariant `a' + b' = a + b`, expressed through C's u32 cast. -/
def plus2Invariant (a b currentA currentB : Int) : Prop :=
  u32.cast (currentA + currentB) = u32.cast (a + b)

def plus2Variant (currentB : Nat) : Nat := currentB

theorem plus2_invariant_initial (a : Int) (b : Nat) :
    plus2Invariant a (Int.ofNat b) a (Int.ofNat b) := rfl

theorem plus2_invariant_preserved (a b currentA : Int) (currentB : Nat)
    (invariant : plus2Invariant a b currentA (Int.ofNat (currentB + 1))) :
    plus2Invariant a b (currentA + 1) (Int.ofNat currentB) := by
  unfold plus2Invariant at invariant ⊢
  rw [← invariant]
  congr 1
  simp [Int.natCast_add]
  omega

theorem plus2_variant_decreases (currentB : Nat) :
    plus2Variant currentB < plus2Variant (currentB + 1) := by
  simp [plus2Variant]

theorem plus2LoopBody_exec (a : Int) (b : Nat) (bound : b + 1 < 2 ^ 32) :
    Stmt.Exec plus2LoopBody (plus2State a (b + 1))
      (.normal (plus2State (a + 1) b)) := by
  unfold plus2LoopBody
  apply Stmt.Exec.seqNormal
  · apply Stmt.Exec.seqNormal
    · exact Stmt.Exec.assign 1 u32 plus2Increment (plus2Increment_eval a (b + 1))
    · apply Stmt.Exec.seqNormal
      · rw [plus2_increment_state]
        exact Stmt.Exec.assign 2 u32 plus2Decrement
          (plus2Decrement_eval (a + 1) b bound)
      · rw [show
          State.write (plus2State (a + 1) (b + 1)) 2 u32 (Int.ofNat b) =
            plus2State (a + 1) b by exact plus2_decrement_state (a + 1) b]
        exact Stmt.Exec.skip
  · exact Stmt.Exec.skip

theorem plus2Loop_exec (a : Int) (b : Nat) (bound : b < 2 ^ 32) :
    Stmt.Exec plus2Loop (plus2State a b)
      (.normal (plus2State (a + Int.ofNat b) 0)) := by
  induction b generalizing a with
  | zero =>
      simpa [plus2Loop] using
        (Stmt.Exec.whileFalse (body := plus2LoopBody) (plus2Condition_zero a))
  | succ b induction =>
      apply Stmt.Exec.whileTrue (value := 1)
      · exact plus2Condition_succ a b bound
      · decide
      · exact plus2LoopBody_exec a b bound
      · have rest := induction (a := a + 1) (by omega)
        have sumEq : a + 1 + Int.ofNat b = a + Int.ofNat (b + 1) := by
          simp [Int.natCast_add]
          omega
        rw [← sumEq]
        simpa [plus2Loop] using rest

end Zag.Test.AutoCorres.CParser.ScalarSimpl
