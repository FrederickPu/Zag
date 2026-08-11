import Test.AutoCorres.CParser.ScalarSimpl.MultByAddShape
import Test.AutoCorres.CParser.ScalarSimpl.Plus2Model

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

abbrev MultByAddWord32 := BitVec 32

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

def multByAddState (remaining : Nat) (b : MultByAddWord32) (result : Int) : State :=
  ((State.write (State.write (State.write {} 1 u32 (Int.ofNat remaining))
    2 u32 (Int.ofNat b.toNat)) 3 u32 result))

theorem multByAddState_read_a (remaining : Nat) (b : MultByAddWord32) (result : Int)
    (bound : remaining < 2 ^ 32) :
    (multByAddState remaining b result).read? 1 = some (Int.ofNat remaining) := by
  simp [multByAddState, State.read?, State.write]
  exact u32_cast_nat remaining bound

theorem multByAddState_read_b (remaining : Nat) (b : MultByAddWord32) (result : Int) :
    (multByAddState remaining b result).read? 2 = some (Int.ofNat b.toNat) := by
  simp [multByAddState, State.read?, State.write]
  exact u32_cast_nat b.toNat b.isLt

theorem multByAddState_read_result (remaining : Nat) (b : MultByAddWord32) (result : Int) :
    (multByAddState remaining b result).read? 3 = some (u32.cast result) := by
  simp [multByAddState, State.read?, State.write]

theorem multByAddCondition_zero (b : MultByAddWord32) (result : Int) :
    multByAddCondition.eval (multByAddState 0 b result) = some 0 := by
  simp [multByAddCondition, Expr.eval, multByAddState_read_a]

theorem multByAddCondition_succ (remaining : Nat) (b : MultByAddWord32) (result : Int)
    (bound : remaining + 1 < 2 ^ 32) :
    multByAddCondition.eval (multByAddState (remaining + 1) b result) = some 1 := by
  have cast := u32_cast_nat (remaining + 1) bound
  have cast' : u32.cast ((remaining : Int) + 1) = (remaining : Int) + 1 := by
    simpa [Int.ofNat_eq_natCast, Int.natCast_add] using cast
  rw [show multByAddCondition =
    .binary s32 u32 .greater (.variable u32 1) (.literal s32 0) by rfl]
  simp [Expr.eval, multByAddState_read_a _ _ _ bound, cast']

theorem multByAddResultIncrement_eval (remaining : Nat) (b : MultByAddWord32)
    (result : Int) :
    multByAddResultIncrement.eval (multByAddState remaining b result) =
      some (u32.cast (result + Int.ofNat b.toNat)) := by
  rw [show multByAddResultIncrement =
    .binary u32 u32 .add (.variable u32 3) (.variable u32 2) by rfl]
  simp [Expr.eval, multByAddState_read_result, multByAddState_read_b,
    u32_checked, u32_cast_add_left]
  have castB : u32.cast (b.toNat : Int) = (b.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using u32_cast_nat b.toNat b.isLt
  rw [castB]

theorem multByAddDecrement_eval (remaining : Nat) (b : MultByAddWord32) (result : Int)
    (bound : remaining + 1 < 2 ^ 32) :
    multByAddDecrement.eval (multByAddState (remaining + 1) b result) =
      some (Int.ofNat remaining) := by
  have castCurrent := u32_cast_nat (remaining + 1) bound
  have castNext := u32_cast_nat remaining (by omega)
  have castCurrent' : u32.cast ((remaining : Int) + 1) = (remaining : Int) + 1 := by
    simpa [Int.ofNat_eq_natCast, Int.natCast_add] using castCurrent
  have castNext' : u32.cast (remaining : Int) = (remaining : Int) := by
    simpa [Int.ofNat_eq_natCast] using castNext
  rw [show multByAddDecrement =
    .binary u32 u32 .subtract (.variable u32 1) (.literal s32 1) by rfl]
  simp [Expr.eval, multByAddState_read_a _ _ _ bound, castCurrent', u32_checked,
    castNext']

theorem multByAdd_result_update (remaining : Nat) (b : MultByAddWord32) (result : Int) :
    State.write (multByAddState remaining b result) 3 u32
        (u32.cast (result + Int.ofNat b.toNat)) =
      multByAddState remaining b (u32.cast (result + Int.ofNat b.toNat)) := by
  apply state_ext
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [multByAddState, State.write, u32_cast_idempotent]
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [multByAddState, State.write]
  all_goals rfl

theorem multByAdd_decrement_update (remaining : Nat) (b : MultByAddWord32)
    (result : Int) :
    State.write (multByAddState (remaining + 1) b result) 1 u32
        (Int.ofNat remaining) = multByAddState remaining b result := by
  apply state_ext
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [multByAddState, State.write]
  next =>
    apply funext
    intro key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [multByAddState, State.write]
  all_goals rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
