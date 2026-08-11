import Test.AutoCorres.CParser.ScalarSimpl.GcdShape

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

abbrev GcdWord32 := BitVec 32

def gcdInvariant (a b a' b' : GcdWord32) : Prop :=
  Nat.gcd a.toNat b.toNat = Nat.gcd a'.toNat b'.toNat

def gcdVariant (a' : GcdWord32) : Nat := a'.toNat

theorem gcd_invariant_initial (a b : GcdWord32) : gcdInvariant a b a b := rfl

theorem gcd_remainder_toNat (a b : GcdWord32) :
    (b % a).toNat = b.toNat % a.toNat := by exact BitVec.toNat_umod

theorem gcd_invariant_preserved (a b a' b' : GcdWord32)
    (invariant : gcdInvariant a b a' b') :
    gcdInvariant a b (b' % a') a' := by
  unfold gcdInvariant at invariant ⊢
  rw [gcd_remainder_toNat, ← Nat.gcd_rec]
  exact invariant

theorem gcd_variant_strictly_decreases (a' b' : GcdWord32)
    (nonzero : a' ≠ 0) : gcdVariant (b' % a') < gcdVariant a' := by
  unfold gcdVariant
  rw [gcd_remainder_toNat]
  apply Nat.mod_lt
  exact Nat.pos_of_ne_zero (by
    intro zero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using zero))

theorem gcd_invariant_final (a b b' : GcdWord32)
    (invariant : gcdInvariant a b 0 b') :
    b'.toNat = Nat.gcd a.toNat b.toNat := by
  unfold gcdInvariant at invariant
  simpa [Nat.gcd_zero_left] using invariant.symm

def gcdNat : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => gcdNat (b % (a + 1)) (a + 1)
termination_by a => a
decreasing_by
  have decrease := Nat.mod_lt b (Nat.succ_pos a)
  omega

theorem gcdNat_eq_gcd (a b : Nat) : gcdNat a b = Nat.gcd a b := by
  induction a, b using gcdNat.induct with
  | case1 b => simp [gcdNat]
  | case2 a b induction =>
      rw [gcdNat, induction]
      exact (Nat.gcd_rec (a + 1) b).symm

end Zag.Test.AutoCorres.CParser.ScalarSimpl
