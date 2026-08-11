import Test.AutoCorres.CParser.ScalarSimpl.GcdInvariant
import Lang.AutoCorres.WordAbstract

/-!
# Total-map boundary for exact `gcd` WordAbstract

ScalarSimpl stores unsigned C locals as normalized `Int` values. Unsigned u32
normalization is not injective on all `Int`, so it cannot support an
unconditional round trip. WordAbstract therefore uses a canonical-value guard
and carries that invariant through continuations and loops.
-/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.WordAbstract
open Zag.Lang.AutoCorres.WordAbstract.Kernel

def unsignedIntAbstract (value : Int) : Nat :=
  (BitVec.ofInt 32 value).toNat

theorem unsignedIntAbstract_zero : unsignedIntAbstract 0 = 0 := by native_decide

theorem unsignedIntAbstract_two_pow :
    unsignedIntAbstract (Int.ofNat (2 ^ 32)) = 0 := by native_decide

/-- No concretization can left-invert unsigned u32 abstraction on every `Int`. -/
theorem no_total_unsigned_int_roundtrip
    (concretize : Nat → Int)
    (roundTrip : ∀ value, concretize (unsignedIntAbstract value) = value) : False := by
  have zero := roundTrip 0
  have wrapped := roundTrip (Int.ofNat (2 ^ 32))
  rw [unsignedIntAbstract_zero] at zero
  rw [unsignedIntAbstract_two_pow] at wrapped
  rw [zero] at wrapped
  have distinct : (0 : Int) ≠ Int.ofNat (2 ^ 32) := by decide
  exact distinct wrapped

/--
`TypeMap.sourceRoundTripGuard` plus `valid_typ_abs_fn.concretize_abstract`
would provide the impossible total round trip for an `Int`-backed u32 value.
-/
theorem no_unsigned_int_type_map
    (certificate : valid_typ_abs_fn Nat Int)
    (abstractIsU32 : certificate.abstract = unsignedIntAbstract)
    (sourceRoundTripGuard : ∀ value,
      certificate.concreteGuard (certificate.abstract value)) : False := by
  apply no_total_unsigned_int_roundtrip certificate.concretize
  intro value
  rw [← abstractIsU32]
  exact certificate.concretize_abstract value (sourceRoundTripGuard value)

/-- Canonical u32 values satisfy the guarded `Int`-to-`Nat` kernel map. -/
theorem kernel_unsigned_int_guard (value : Nat) (bounded : value < 2 ^ 32) :
    (typeMap (.uwordInt 32)).certificate.concreteGuard
      ((typeMap (.uwordInt 32)).abstract (Int.ofNat value)) := by
  change abstractUnsignedInt 32 (Int.ofNat value) < 2 ^ 32
  have canonical : intUnsignedCanonical 32 (Int.ofNat value) :=
    ⟨by simp, Int.ofNat_lt.2 bounded⟩
  unfold abstractUnsignedInt
  rw [if_pos canonical]
  simpa using bounded

end Zag.Test.AutoCorres.CParser.ScalarSimpl
