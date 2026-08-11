import Test.AutoCorres.CParser.ScalarSimpl.MultByAddModel

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

/-- The upstream invariant, in wrapping Word32 arithmetic. -/
def multByAddInvariant (a b a' result : MultByAddWord32) : Prop :=
  (a' * b) + result = a * b

def multByAddVariant (a' : MultByAddWord32) : Nat := a'.toNat

private theorem word_multiply_step (remaining : Nat) (b result : MultByAddWord32) :
    BitVec.ofNat 32 remaining * b + (result + b) =
      BitVec.ofNat 32 (remaining + 1) * b + result := by
  rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
  calc
    BitVec.ofNat 32 remaining * b + (result + b) =
        BitVec.ofNat 32 remaining * b + (b + result) :=
      congrArg (fun value => BitVec.ofNat 32 remaining * b + value)
        (BitVec.add_comm result b)
    _ = BitVec.ofNat 32 remaining * b + b + result :=
      (BitVec.add_assoc _ _ _).symm

theorem mult_by_add_invariant_initial (a b : MultByAddWord32) :
    multByAddInvariant a b a 0 := by
  simp [multByAddInvariant]

theorem mult_by_add_invariant_preserved (a b : MultByAddWord32)
    (remaining : Nat) (result : Int)
    (invariant : multByAddInvariant a b (BitVec.ofNat 32 (remaining + 1))
      (BitVec.ofInt 32 result)) :
    multByAddInvariant a b (BitVec.ofNat 32 remaining)
      (BitVec.ofInt 32 (u32.cast (result + Int.ofNat b.toNat))) := by
  unfold multByAddInvariant at invariant ⊢
  rw [bitvec_of_u32_cast, BitVec.ofInt_add, Int.ofNat_eq_natCast,
    BitVec.ofInt_natCast]
  have bEq : BitVec.ofNat 32 b.toNat = b := by simp
  rw [bEq]
  rw [← invariant]
  exact word_multiply_step remaining b (BitVec.ofInt 32 result)

theorem mult_by_add_variant_decreases (remaining : Nat)
    (bound : remaining + 1 < 2 ^ 32) :
    multByAddVariant (BitVec.ofNat 32 remaining) <
      multByAddVariant (BitVec.ofNat 32 (remaining + 1)) := by
  have power : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [power] at bound
  change remaining % 4294967296 < (remaining + 1) % 4294967296
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt bound]
  omega

def multByAddAccumulate (b : MultByAddWord32) : Nat → Int → Int
  | 0, result => result
  | remaining + 1, result =>
      multByAddAccumulate b remaining (u32.cast (result + Int.ofNat b.toNat))

theorem mult_by_add_accumulate_word (b : MultByAddWord32) (remaining : Nat)
    (result : Int) :
    BitVec.ofInt 32 (multByAddAccumulate b remaining result) =
      BitVec.ofNat 32 remaining * b + BitVec.ofInt 32 result := by
  induction remaining generalizing result with
  | zero => simp [multByAddAccumulate]
  | succ remaining induction =>
      rw [multByAddAccumulate, induction, bitvec_of_u32_cast, BitVec.ofInt_add,
        Int.ofNat_eq_natCast, BitVec.ofInt_natCast]
      have bEq : BitVec.ofNat 32 b.toNat = b := by simp
      rw [bEq]
      exact word_multiply_step remaining b (BitVec.ofInt 32 result)

theorem multByAddLoopBody_exec (remaining : Nat) (b : MultByAddWord32) (result : Int)
    (bound : remaining + 1 < 2 ^ 32) :
    Stmt.Exec multByAddLoopBody (multByAddState (remaining + 1) b result)
      (.normal (multByAddState remaining b
        (u32.cast (result + Int.ofNat b.toNat)))) := by
  unfold multByAddLoopBody
  apply Stmt.Exec.seqNormal
  · apply Stmt.Exec.seqNormal
    · exact Stmt.Exec.assign 3 u32 multByAddResultIncrement
        (multByAddResultIncrement_eval (remaining + 1) b result)
    · apply Stmt.Exec.seqNormal
      · rw [multByAdd_result_update]
        exact Stmt.Exec.assign 1 u32 multByAddDecrement
          (multByAddDecrement_eval remaining b _ bound)
      · rw [multByAdd_decrement_update]
        exact Stmt.Exec.skip
  · exact Stmt.Exec.skip

theorem multByAddLoop_exec (remaining : Nat) (b : MultByAddWord32) (result : Int)
    (bound : remaining < 2 ^ 32) :
    Stmt.Exec multByAddLoop (multByAddState remaining b result)
      (.normal (multByAddState 0 b (multByAddAccumulate b remaining result))) := by
  induction remaining generalizing result with
  | zero =>
      simpa [multByAddLoop, multByAddAccumulate] using
        (Stmt.Exec.whileFalse (body := multByAddLoopBody)
          (multByAddCondition_zero b result))
  | succ remaining induction =>
      apply Stmt.Exec.whileTrue (value := 1)
      · exact multByAddCondition_succ remaining b result bound
      · decide
      · exact multByAddLoopBody_exec remaining b result bound
      · simpa [multByAddLoop, multByAddAccumulate] using
          induction (result := u32.cast (result + Int.ofNat b.toNat)) (by omega)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
