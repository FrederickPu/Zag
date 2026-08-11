import Test.AutoCorres.CParser.ScalarSimpl.Plus2Shape

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

theorem u32_cast_add_left (x y : Int) :
    u32.cast (u32.cast x + y) = u32.cast (x + y) := by
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus,
    Int.add_emod]

theorem u32_cast_sub_left (x y : Int) :
    u32.cast (u32.cast x - y) = u32.cast (x - y) := by
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus,
    Int.sub_emod]

set_option maxRecDepth 100000 in
theorem u32_cast_nat (n : Nat) (bound : n < 2 ^ 32) :
    u32.cast (Int.ofNat n) = Int.ofNat n := by
  have power : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [power] at bound
  have upper : (n : Int) < (4294967296 : Int) := Int.ofNat_lt.mpr bound
  change (((n : Int) % 4294967296 + 4294967296) % 4294967296) = (n : Int)
  rw [Int.emod_eq_of_lt (by omega) upper]
  omega

theorem bitvec_of_u32_cast (value : Int) :
    BitVec.ofInt 32 (u32.cast value) = BitVec.ofInt 32 value := by
  apply BitVec.eq_of_toFin_eq
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus,
    BitVec.ofInt]

@[simp] theorem s32_cast_zero : s32.cast 0 = 0 := by native_decide
@[simp] theorem s32_cast_one : s32.cast 1 = 1 := by native_decide
@[simp] theorem u32_cast_zero : u32.cast 0 = 0 := by native_decide
@[simp] theorem u32_cast_one : u32.cast 1 = 1 := by native_decide

private theorem state_ext {left right : State}
    (value : left.value = right.value)
    (initialized : left.initialized = right.initialized)
    (returned : left.returned = right.returned)
    (result : left.result = right.result)
    (callStack : left.callStack = right.callStack)
    (temporaries : left.temporaries = right.temporaries) : left = right := by
  cases left
  cases right
  simp only [State.mk.injEq] at *
  simp_all

def plus2State (a : Int) (b : Nat) : State :=
  (State.write (State.write {} 1 u32 a) 2 u32 (Int.ofNat b))

theorem plus2State_read_a (a : Int) (b : Nat) :
    (plus2State a b).read? 1 = some (u32.cast a) := by
  simp [plus2State, State.read?, State.write]

theorem plus2State_read_b (a : Int) (b : Nat) (bound : b < 2 ^ 32) :
    (plus2State a b).read? 2 = some (Int.ofNat b) := by
  change some (u32.cast (Int.ofNat b)) = some (Int.ofNat b)
  rw [u32_cast_nat b bound]

theorem plus2Condition_zero (a : Int) :
    plus2Condition.eval (plus2State a 0) = some 0 := by
  simp [plus2Condition, Expr.eval, plus2State_read_b]

theorem plus2Condition_succ (a : Int) (b : Nat) (bound : b + 1 < 2 ^ 32) :
    plus2Condition.eval (plus2State a (b + 1)) = some 1 := by
  have cast := u32_cast_nat (b + 1) bound
  have cast' : u32.cast ((b : Int) + 1) = (b : Int) + 1 := by
    simpa [Int.ofNat_eq_natCast, Int.natCast_add] using cast
  rw [show plus2Condition =
    .binary s32 u32 .greater (.variable u32 2) (.literal s32 0) by rfl]
  simp [Expr.eval, plus2State_read_b, bound, cast']

theorem plus2Increment_eval (a : Int) (b : Nat) :
    plus2Increment.eval (plus2State a b) = some (u32.cast (a + 1)) := by
  simp [plus2Increment, Expr.eval, plus2State_read_a, u32_checked,
    u32_cast_add_left]

theorem plus2Decrement_eval (a : Int) (b : Nat) (bound : b + 1 < 2 ^ 32) :
    plus2Decrement.eval (plus2State a (b + 1)) = some (Int.ofNat b) := by
  have castCurrent := u32_cast_nat (b + 1) bound
  have castNext := u32_cast_nat b (by omega)
  have castCurrent' : u32.cast ((b : Int) + 1) = (b : Int) + 1 := by
    simpa [Int.ofNat_eq_natCast, Int.natCast_add] using castCurrent
  have castNext' : u32.cast (b : Int) = (b : Int) := by
    simpa [Int.ofNat_eq_natCast] using castNext
  rw [show plus2Decrement =
    .binary u32 u32 .subtract (.variable u32 2) (.literal s32 1) by rfl]
  simp [Expr.eval, plus2State_read_b _ _ bound, castCurrent', u32_checked,
    castNext']

theorem plus2_increment_state (a : Int) (b : Nat) :
    State.write (plus2State a b) 1 u32 (u32.cast (a + 1)) =
      plus2State (a + 1) b := by
  apply state_ext
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;>
      simp_all [plus2State, State.write, u32_cast_idempotent]
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> simp_all [plus2State, State.write]
  all_goals rfl

theorem plus2_decrement_state (a : Int) (b : Nat) :
    State.write (plus2State a (b + 1)) 2 u32 (Int.ofNat b) = plus2State a b := by
  apply state_ext
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;>
      simp_all [plus2State, State.write]
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> simp_all [plus2State, State.write]
  all_goals rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
