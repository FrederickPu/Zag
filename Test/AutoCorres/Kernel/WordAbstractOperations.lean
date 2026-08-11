import Lang.AutoCorres.ML.word_abstract

set_option maxHeartbeats 500000

/-!
# WordAbstract scalar operation matrix

Boundary and adversarial pins for the certified 8/16/32/64-bit signed and
unsigned kernel. These tests inspect concrete bit patterns, generated values,
and guards; the program theorem consumes the runtime-guarded partial `CorresXF`
certificate rather than claiming total refinement.
-/

namespace Zag.Test.AutoCorres.Kernel.WordAbstractOperations

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.WordAbstract
open Zag.Lang.AutoCorres.WordAbstract.Kernel

private abbrev Argument := ValueType.unit
private abbrev State := Unit

private def u8 (value : Nat) : ML.WordAbstract.Source.Expr Argument State (.word 8) :=
  .word 8 (BitVec.ofNat 8 value)

private def u16 (value : Nat) : ML.WordAbstract.Source.Expr Argument State (.word 16) :=
  .word 16 (BitVec.ofNat 16 value)

private def s8 (value : Int) : ML.WordAbstract.Source.Expr Argument State (.sword 8) :=
  .sword 8 (BitVec.ofInt 8 value)

private def s16 (value : Int) : ML.WordAbstract.Source.Expr Argument State (.sword 16) :=
  .sword 16 (BitVec.ofInt 16 value)

theorem supported_widths_are_exact :
    WordWidth.w8.bits = 8 ∧ WordWidth.w16.bits = 16 ∧
      WordWidth.w32.bits = 32 ∧ WordWidth.w64.bits = 64 := by
  decide

theorem signed_bounds_matrix :
    SWORD_MIN 8 = -128 ∧ SWORD_MAX 8 = 127 ∧
    SWORD_MIN 16 = -32768 ∧ SWORD_MAX 16 = 32767 ∧
    SWORD_MIN 32 = -2147483648 ∧ SWORD_MAX 32 = 2147483647 ∧
    SWORD_MIN 64 = -9223372036854775808 ∧
      SWORD_MAX 64 = 9223372036854775807 := by
  native_decide

theorem concrete_unsigned_binary_operations_are_bitvector_operations :
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .mul (u8 200) (u8 2)) =
        BitVec.ofNat 8 200 * BitVec.ofNat 8 2) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .div (u8 200) (u8 3)) =
        BitVec.ofNat 8 200 / BitVec.ofNat 8 3) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .mod (u8 200) (u8 3)) =
        BitVec.ofNat 8 200 % BitVec.ofNat 8 3) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .bitAnd (u8 170) (u8 15)) =
        BitVec.ofNat 8 170 &&& BitVec.ofNat 8 15) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .bitOr (u8 160) (u8 15)) =
        BitVec.ofNat 8 160 ||| BitVec.ofNat 8 15) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ubinary .w8 .bitXor (u8 170) (u8 15)) =
        BitVec.ofNat 8 170 ^^^ BitVec.ofNat 8 15) := by
  native_decide

theorem concrete_signed_binary_operations_are_bitvector_operations :
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .add (s8 70) (s8 60)) =
        BitVec.ofInt 8 70 + BitVec.ofInt 8 60) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .sub (s8 (-100)) (s8 50)) =
        BitVec.ofInt 8 (-100) - BitVec.ofInt 8 50) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .mul (s8 100) (s8 2)) =
        BitVec.ofInt 8 100 * BitVec.ofInt 8 2) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .tdiv (s8 (-7)) (s8 2)) =
        (BitVec.ofInt 8 (-7)).sdiv (BitVec.ofInt 8 2)) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .tmod (s8 (-7)) (s8 2)) =
        (BitVec.ofInt 8 (-7)).srem (BitVec.ofInt 8 2)) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .bitAnd (s8 (-2)) (s8 7)) =
        BitVec.ofInt 8 (-2) &&& BitVec.ofInt 8 7) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .bitOr (s8 (-128)) (s8 1)) =
        BitVec.ofInt 8 (-128) ||| BitVec.ofInt 8 1) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sbinary .w8 .bitXor (s8 (-1)) (s8 85)) =
        BitVec.ofInt 8 (-1) ^^^ BitVec.ofInt 8 85) := by
  native_decide

theorem concrete_unary_operations_are_bitvector_operations :
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.uunary .w8 .neg (u8 1)) =
      -(BitVec.ofNat 8 1)) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.uunary .w8 .bitNot (u8 1)) =
      ~~~(BitVec.ofNat 8 1)) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sunary .w8 .neg (s8 (-7))) =
      -(BitVec.ofInt 8 (-7))) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sunary .w8 .bitNot (s8 (-7))) =
      ~~~(BitVec.ofInt 8 (-7))) := by
  native_decide

theorem concrete_shifts_are_bitvector_operations :
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ushiftU .left .w8 .w8 (u8 3) (u8 2)) =
        BitVec.ofNat 8 3 <<< 2) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ushiftS .right .w8 .w8 (u8 128) (s8 2)) =
        BitVec.ofNat 8 128 >>> (BitVec.ofInt 8 2).toNat) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sshiftU .left .w8 .w8 (s8 3) (u8 2)) =
        BitVec.ofInt 8 3 <<< 2) ∧
    (Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.sshiftS .right .w8 .w8 (s8 (-128)) (s8 1)) =
        (BitVec.ofInt 8 (-128)).sshiftRight (BitVec.ofInt 8 1).toNat) := by
  native_decide

theorem concrete_comparisons_and_conversions_use_bit_patterns :
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ucmp .w8 .gt (u8 255) (u8 1)) = true ∧
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.scmp .w8 .lt (s8 (-1)) (s8 1)) = true ∧
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.ucast .w16 .w8 (u16 4660)) =
      (BitVec.ofNat 16 4660).setWidth 8 ∧
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.scast .w16 .w8 (s16 130)) =
      (BitVec.ofInt 16 130).signExtend 8 ∧
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.unsignedToSigned .w8 (u8 127)) =
      BitVec.ofNat 8 127 ∧
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval () ()
      (.signedToUnsigned .w8 (s8 (-1))) =
      BitVec.ofInt 8 (-1) := by
  native_decide

private def unsignedMultiply :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ubinary .w8 .mul (u8 255) (u8 1)))

theorem unsigned_multiply_boundary :
    unsignedMultiply.target.eval () () = 255 ∧ unsignedMultiply.guard () () := by
  simp [unsignedMultiply, u8, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    unsignedBinaryGuard, unsignedBinaryCDefined,
    unsignedBinaryAbstractable, unsignedBinary, UWORD_MAX] <;> native_decide

private def unsignedMultiplyOverflow :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ubinary .w8 .mul (u8 255) (u8 2)))

theorem unsigned_multiply_overflow_rejected :
    ¬unsignedMultiplyOverflow.guard () () := by
  simp [unsignedMultiplyOverflow, u8, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    unsignedBinaryGuard, unsignedBinaryCDefined,
    unsignedBinaryAbstractable, unsignedBinary, UWORD_MAX] <;> native_decide

theorem unsigned_wrap_is_defined_but_not_nat_abstractable :
    unsignedBinaryCDefined .mul 255 2 ∧
    ¬unsignedBinaryAbstractable 8 .mul 255 2 ∧
      (unsignedBinaryGuard 8 .mul 255 2 ↔ False) := by
  simp [unsignedBinaryGuard, unsignedBinaryCDefined,
    unsignedBinaryAbstractable, unsignedBinary, UWORD_MAX] <;> native_decide

theorem generated_unsigned_guard_has_exact_stages :
    unsignedBinaryGuard 8 .mul 255 2 ↔
      unsignedBinaryCDefined .mul 255 2 ∧
        unsignedBinaryAbstractable 8 .mul 255 2 :=
  unsignedBinaryGuard_iff 8 .mul 255 2

def wrappingMultiplySource :
    ML.WordAbstract.Source.Syntax Argument State .unit (.word 8) :=
  .gets (.ubinary .w8 .mul (u8 255) (u8 2)) ["wrapping-mul"]

def wrappingMultiplyEvidence :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ubinary .w8 .mul (u8 255) (u8 2)))

def wrappingMultiplyCertificate :=
  ML.WordAbstract.transformSource wrappingMultiplySource

theorem wrapping_multiply_target_is_guarded_stage :
    wrappingMultiplyCertificate.target =
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.seq
        (.guard wrappingMultiplyEvidence.guard)
        (fun _ => .gets wrappingMultiplyEvidence.target ["wrapping-mul"]) := by
  rfl

theorem concrete_source_wraps_while_abstract_target_fails :
    (Except.ok (BitVec.ofNat 8 254), ()) ∈
        (wrappingMultiplySource.denote () ()).results ∧
      (wrappingMultiplyCertificate.target.denote () ()).failed := by
  constructor
  · simp [wrappingMultiplySource, u8,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Syntax.denote,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr.eval,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.asWord,
      unsignedBinaryWord, L2.gets]
  · rw [wrapping_multiply_target_is_guarded_stage]
    simp [wrappingMultiplyEvidence, u8, ML.WordAbstract.Expr.supported,
      ML.WordAbstract.Expr.transform,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax.denote,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
      Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
      WordWidth.bits,
      unsignedBinaryGuard, unsignedBinaryCDefined,
      unsignedBinaryAbstractable, unsignedBinary, UWORD_MAX,
      L2.seq, L2.guard, bindE, L2.failed_liftE,
      Zag.Lang.AutoCorres.guard]

theorem zero_divisors_rejected_at_every_width :
    ¬unsignedBinaryGuard 8 .div 255 0 ∧
    ¬unsignedBinaryGuard 16 .mod 65535 0 ∧
    ¬unsignedBinaryGuard 32 .div 4294967295 0 ∧
    ¬unsignedBinaryGuard 64 .mod 18446744073709551615 0 := by
  simp [unsignedBinaryGuard, unsignedBinaryCDefined] <;> native_decide

theorem signed_min_div_neg_one_rejected_at_every_width :
    ¬signedBinaryGuard 8 .tdiv (-128) (-1) ∧
    ¬signedBinaryGuard 16 .tmod (-32768) (-1) ∧
    ¬signedBinaryGuard 32 .tdiv (-2147483648) (-1) ∧
    ¬signedBinaryGuard 64 .tmod (-9223372036854775808) (-1) := by
  simp [signedBinaryGuard, signedBinaryCDefined, SWORD_MIN] <;> native_decide

private def signedDivision :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sbinary .w8 .tdiv (s8 (-7)) (s8 2)))

private def signedModulo :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sbinary .w8 .tmod (s8 (-7)) (s8 2)))

theorem signed_division_truncates_toward_zero :
    signedDivision.target.eval () () = -3 ∧ signedDivision.guard () () := by
  simp [signedDivision, s8, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    signedBinaryGuard, signedBinaryCDefined, signedBinaryAbstractable,
    signedBinary, signedInRange, SWORD_MIN, SWORD_MAX] <;> native_decide

theorem signed_modulo_has_dividend_sign :
    signedModulo.target.eval () () = -1 ∧ signedModulo.guard () () := by
  simp [signedModulo, s8, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    signedBinaryGuard, signedBinaryCDefined, signedBinaryAbstractable,
    signedBinary, signedInRange, SWORD_MIN, SWORD_MAX] <;> native_decide

private def unsignedBitwise :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ubinary .w8 .bitXor
      (.ubinary .w8 .bitAnd (u8 170) (u8 15))
      (.uunary .w8 .bitNot (u8 0))))

private def signedBitwise :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sbinary .w8 .bitOr (s8 (-128)) (s8 1)))

theorem bitwise_results_and_guards_are_substantive :
    unsignedBitwise.target.eval () () = 245 ∧ unsignedBitwise.guard () () ∧
      signedBitwise.target.eval () () = -127 ∧ signedBitwise.guard () () := by
  simp [unsignedBitwise, signedBitwise, u8, s8,
    ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    unsignedBinaryGuard, unsignedBinaryCDefined, unsignedBinaryAbstractable,
    unsignedUnaryCDefined, unsignedUnaryAbstractable, unsignedBinary,
    unsignedUnary, signedBinaryGuard, signedBinaryCDefined,
    signedBinaryAbstractable, signedBinary, signedInRange,
    signedToUnsignedValue, UWORD_MAX, SWORD_MIN, SWORD_MAX] <;> native_decide

private def signedNegationMin :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sunary .w8 .neg (s8 (-128))))

private def signedNegationMax :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sunary .w8 .neg (s8 127)))

theorem signed_negation_boundary :
    ¬signedNegationMin.guard () () ∧
      signedNegationMax.target.eval () () = -127 ∧ signedNegationMax.guard () () := by
  simp [signedNegationMin, signedNegationMax, s8,
    ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    signedUnaryCDefined, signedUnaryAbstractable, signedUnary,
    signedInRange, SWORD_MIN, SWORD_MAX] <;> native_decide

private def supportedSignedRightShift :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sshiftU .right .w8 .w8 (s8 64) (u8 1)))

private def negativeSignedRightShift :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sshiftU .right .w8 .w8 (s8 (-128)) (u8 1)))

private def invalidUnsignedShift :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ushiftU .right .w8 .w8 (u8 255) (u8 8)))

private def negativeSignedCount :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ushiftS .left .w8 .w8 (u8 1) (s8 (-1))))

private def negativeSignedLeft :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sshiftU .left .w8 .w8 (s8 (-1)) (u8 1)))

private def overflowingSignedLeft :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.sshiftU .left .w8 .w8 (s8 64) (u8 1)))

theorem pinned_signed_right_shift_requires_nonnegative_source :
    supportedSignedRightShift.target.eval () () = 32 ∧
      supportedSignedRightShift.guard () () ∧
      ¬negativeSignedRightShift.guard () () := by
  simp [supportedSignedRightShift, negativeSignedRightShift, u8, s8,
    ML.WordAbstract.Expr.supported, ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    signedShiftGuard, signedShiftCDefined, signedShiftAbstractable,
    signedShift, signedInRange, SWORD_MIN, SWORD_MAX] <;> native_decide

theorem negative_signed_right_shift_is_an_abstraction_gap_not_claimed_ub :
    signedShiftCDefined 8 .right (-128) 1 ∧
      ¬signedShiftAbstractable 8 .right (-128) 1 ∧
      (signedShiftGuard 8 .right (-128) 1 ↔ False) := by
  simp [signedShiftGuard, signedShiftCDefined, signedShiftAbstractable,
    signedShift, signedInRange, SWORD_MIN, SWORD_MAX] <;> native_decide

theorem generated_signed_shift_guard_has_exact_stages :
    signedShiftGuard 8 .right (-128) 1 ↔
      signedShiftCDefined 8 .right (-128) 1 ∧
        signedShiftAbstractable 8 .right (-128) 1 :=
  signedShiftGuard_iff 8 .right (-128) 1

theorem shift_ub_is_guarded :
    ¬invalidUnsignedShift.guard () () ∧
    ¬negativeSignedCount.guard () () ∧
    ¬negativeSignedRightShift.guard () () ∧
    ¬negativeSignedLeft.guard () () ∧
    ¬overflowingSignedLeft.guard () () := by
  simp [invalidUnsignedShift, negativeSignedCount, negativeSignedRightShift,
    negativeSignedLeft, overflowingSignedLeft, u8, s8,
    ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    unsignedShiftGuard, unsignedShiftCDefined, unsignedShiftAbstractable,
    signedShiftGuard, signedShiftCDefined, signedShiftAbstractable,
    signedShift, signedInRange, UWORD_MAX, SWORD_MIN, SWORD_MAX] <;> native_decide

private def unsignedTruncation :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ucast .w16 .w8 (u16 4660)))

private def signedTruncation :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.scast .w16 .w8 (s16 130)))

private def unsignedToSignedHigh :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.unsignedToSigned .w8 (u8 128)))

private def signedToUnsignedNegative :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.signedToUnsigned .w8 (s8 (-1))))

theorem conversions_truncate_and_guard_reinterpretation :
    unsignedTruncation.target.eval () () = 52 ∧ unsignedTruncation.guard () () ∧
    signedTruncation.target.eval () () = -126 ∧ signedTruncation.guard () () ∧
    ¬unsignedToSignedHigh.guard () () ∧
    signedToUnsignedNegative.target.eval () () = 255 ∧
      signedToUnsignedNegative.guard () () := by
  simp [unsignedTruncation, signedTruncation, unsignedToSignedHigh,
    signedToUnsignedNegative, u8, u16, s8, s16,
    ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    signedInRange, signedToUnsignedValue, SWORD_MIN, SWORD_MAX] <;> native_decide

private def signedComparison :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.scmp .w8 .lt (s8 (-1)) (s8 0)))

private def unsignedComparison :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported
    (.ucmp .w8 .gt (u8 255) (u8 0)))

theorem signed_and_unsigned_comparisons_use_distinct_orders :
    signedComparison.target.eval () () = true ∧ signedComparison.guard () () ∧
      unsignedComparison.target.eval () () = true ∧ unsignedComparison.guard () () := by
  simp [signedComparison, unsignedComparison, u8, s8,
    ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr.eval,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asNat,
    Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.asInt,
    compareNat, compareInt] <;> native_decide

def signedDivisionSource :
    ML.WordAbstract.Source.Syntax Argument State .unit (.sword 8) :=
  .gets (.sbinary .w8 .tdiv (s8 (-7)) (s8 2)) ["signed-div"]

def signedDivisionCertificate := ML.WordAbstract.transformSource signedDivisionSource

theorem structural_packaging_preserves_typed_source :
    (ML.WordAbstract.package signedDivisionSource).source = signedDivisionSource := by
  rfl

private def continuationNext (value : BitVec 8) :
    ML.WordAbstract.Source.Syntax Argument State .unit (.word 8) :=
  .gets (.word 8 value) ["continuation"]

private def continuationSource :
    ML.WordAbstract.Source.Syntax Argument State .unit (.word 8) :=
  .seq (.gets (u8 7) ["first"]) continuationNext

private def continuationEvidence := ML.WordAbstract.supported continuationSource

theorem continuation_relation_is_packaged (value : BitVec 8) :
    Nonempty (ML.WordAbstract.Supported (continuationNext value)) :=
  ⟨ML.WordAbstract.Supported.seqContinuation continuationEvidence value⟩

private def continuationCertificate :=
  ML.WordAbstract.transform continuationEvidence

theorem packaged_continuation_has_runtime_guarded_corresXF :
    corresTA (fun _ => True) (typeMap (.word 8)).abstract
      (typeMap .unit).abstract
      (continuationCertificate.target.denote ())
      (continuationSource.denote ()) :=
  continuationCertificate.corres ()

theorem signed_division_has_runtime_guarded_corresXF :
    corresTA (fun _ => True) (typeMap (.sword 8)).abstract
      (typeMap .unit).abstract
      (signedDivisionCertificate.target.denote ())
      (signedDivisionSource.denote ()) :=
  signedDivisionCertificate.corres ()

end Zag.Test.AutoCorres.Kernel.WordAbstractOperations
