import Test.AutoCorres.CParser.ScalarSimpl.GcdExecutionModel

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxHeartbeats 100000

theorem truncMod_nat (left right : Nat) :
    Expr.truncMod (left : Int) (right : Int) = (left % right : Nat) := by
  have leftNonnegative : ¬(left : Int) < 0 := by omega
  have rightNonnegative : ¬(right : Int) < 0 := by omega
  have decomposition := congrArg Int.ofNat (Nat.mod_add_div left right)
  simp [Expr.truncMod, Expr.truncDiv, leftNonnegative, rightNonnegative]
  simp at decomposition
  rw [Int.ofNat_ediv_ofNat] at *
  rw [Int.mul_comm]
  omega

end Zag.Test.AutoCorres.CParser.ScalarSimpl
