import Test.AutoCorres.CParser.ScalarSimpl.GcdExecutionUpdates

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

def gcdWord : GcdWord32 → GcdWord32 → GcdWord32
  | a, b => if a = 0 then b else gcdWord (b % a) a
termination_by a => a.toNat
decreasing_by exact gcd_variant_strictly_decreases a b (by assumption)

theorem gcdWord_toNat (a b : GcdWord32) :
    (gcdWord a b).toNat = Nat.gcd a.toNat b.toNat := by
  rw [gcdWord]
  split
  next zero => subst a; simp
  next nonzero =>
    rw [gcdWord_toNat, gcd_remainder_toNat, ← Nat.gcd_rec]
termination_by a.toNat
decreasing_by exact gcd_variant_strictly_decreases a b (by assumption)

theorem gcdWord_nonzero (a b : GcdWord32) (nonzero : a ≠ 0) :
    gcdWord a b = gcdWord (b % a) a := by
  rw [gcdWord, if_neg nonzero]

end Zag.Test.AutoCorres.CParser.ScalarSimpl
