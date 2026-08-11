import Test.AutoCorres.CParser.ScalarSimpl.GcdExecutionModel

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

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

theorem gcdAB_set_c (a b : GcdWord32) :
    (gcdABState a b).write 3 u32 (Int.ofNat a.toNat) = gcdABCState a b a := by
  apply state_ext
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABState, gcdABCState, State.write, State.clear]
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABState, gcdABCState, State.write, State.clear]
  all_goals rfl

theorem gcdABC_set_c (a b c : GcdWord32) :
    (gcdABCState a b c).write 3 u32 (Int.ofNat a.toNat) = gcdABCState a b a := by
  apply state_ext
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  all_goals rfl

theorem gcdABC_set_a (a b c : GcdWord32) :
    (gcdABCState a b c).write 1 u32 (Int.ofNat (b % a).toNat) =
      gcdABCState (b % a) b c := by
  apply state_ext
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  all_goals rfl

theorem gcdABC_set_b (a b c : GcdWord32) :
    (gcdABCState a b c).write 2 u32 (Int.ofNat c.toNat) = gcdABCState a c c := by
  apply state_ext
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  · funext key
    by_cases key = 1 <;> by_cases key = 2 <;> by_cases key = 3 <;>
      simp_all [gcdABCState, State.write]
  all_goals rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
