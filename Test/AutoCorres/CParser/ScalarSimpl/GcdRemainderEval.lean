import Test.AutoCorres.CParser.ScalarSimpl.GcdRemainder

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxHeartbeats 100000
set_option maxRecDepth 100000

private theorem eval_u32_modulus
    (left right : Zag.Lang.AutoCorres.CParser.ScalarSimpl.Expr)
    (state : State) (leftValue rightValue result : Int)
    (leftEval : left.eval state = some leftValue)
    (rightEval : right.eval state = some rightValue)
    (rightNonzero : u32.cast rightValue ≠ 0)
    (truncates : Expr.truncMod (u32.cast leftValue) (u32.cast rightValue) = result)
    (resultCast : u32.cast result = result) :
    (Zag.Lang.AutoCorres.CParser.ScalarSimpl.Expr.binary u32 u32 .modulus
      left right).eval state = some result := by
  rw [Expr.eval, leftEval, rightEval]
  have unsigned : decide (u32.signedness = .signed) = false := by native_decide
  simp [rightNonzero, unsigned, truncates, resultCast]

theorem gcd_remainder_eval (a b c : GcdWord32) (nonzero : a ≠ 0) :
    gcdRemainder.eval (gcdABCState a b c) =
      some (Int.ofNat (b % a).toNat) := by
  have castA := u32_cast_nat a.toNat a.isLt
  have castB := u32_cast_nat b.toNat b.isLt
  have positive : 0 < a.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using zero)
  have remainderBound : b.toNat % a.toNat < 2 ^ 32 :=
    Nat.lt_trans (Nat.mod_lt _ positive) a.isLt
  have castRemainder := u32_cast_nat (b.toNat % a.toNat) remainderBound
  have castA' : u32.cast (a.toNat : Int) = (a.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using castA
  have castB' : u32.cast (b.toNat : Int) = (b.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using castB
  have castRemainder' : u32.cast (b.toNat % a.toNat : Int) =
      (b.toNat % a.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using castRemainder
  have remainder := gcd_remainder_toNat a b
  apply eval_u32_modulus
      (.variable u32 2) (.variable u32 1) _
      (Int.ofNat b.toNat) (Int.ofNat a.toNat)
      (Int.ofNat (b % a).toNat)
  · exact gcdABC_read_b a b c
  · exact gcdABC_read_a a b c
  · rw [castA]
    simpa using Nat.ne_of_gt positive
  · rw [castA, castB]
    have truncates := truncMod_nat b.toNat a.toNat
    rw [show Expr.truncMod (Int.ofNat b.toNat) (Int.ofNat a.toNat) =
      Int.ofNat (b.toNat % a.toNat) by
        simpa [Int.ofNat_eq_natCast] using truncates]
    exact congrArg Int.ofNat remainder.symm
  · rw [remainder]
    exact castRemainder

end Zag.Test.AutoCorres.CParser.ScalarSimpl
