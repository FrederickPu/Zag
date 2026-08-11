import Test.AutoCorres.CParser.ScalarSimpl.GcdInvariant
import Test.AutoCorres.CParser.ScalarSimpl.Plus2Model

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxHeartbeats 100000
set_option maxRecDepth 100000

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

def gcdABState (a b : GcdWord32) : State :=
  ((State.write (State.write {} 1 u32 (Int.ofNat a.toNat))
    2 u32 (Int.ofNat b.toNat))).clear 3

def gcdABCState (a b c : GcdWord32) : State :=
  State.write (State.write (State.write {} 1 u32 (Int.ofNat a.toNat))
    2 u32 (Int.ofNat b.toNat)) 3 u32 (Int.ofNat c.toNat)

theorem gcdAB_read_a (a b : GcdWord32) :
    (gcdABState a b).read? 1 = some (Int.ofNat a.toNat) := by
  simp [gcdABState, State.read?, State.write, State.clear]
  exact u32_cast_nat a.toNat a.isLt

theorem gcdAB_read_b (a b : GcdWord32) :
    (gcdABState a b).read? 2 = some (Int.ofNat b.toNat) := by
  simp [gcdABState, State.read?, State.write, State.clear]
  exact u32_cast_nat b.toNat b.isLt

theorem gcdABC_read_a (a b c : GcdWord32) :
    (gcdABCState a b c).read? 1 = some (Int.ofNat a.toNat) := by
  simp [gcdABCState, State.read?, State.write]
  exact u32_cast_nat a.toNat a.isLt

theorem gcdABC_read_b (a b c : GcdWord32) :
    (gcdABCState a b c).read? 2 = some (Int.ofNat b.toNat) := by
  simp [gcdABCState, State.read?, State.write]
  exact u32_cast_nat b.toNat b.isLt

theorem gcdABC_read_c (a b c : GcdWord32) :
    (gcdABCState a b c).read? 3 = some (Int.ofNat c.toNat) := by
  simp [gcdABCState, State.read?, State.write]
  exact u32_cast_nat c.toNat c.isLt

theorem gcd_condition_zero (b : GcdWord32) :
    gcdCondition.eval (gcdABState 0 b) = some 0 := by
  have zeroU : u32.cast 0 = 0 := by native_decide
  have zeroS : s32.cast 0 = 0 := by native_decide
  simp [gcdCondition, Expr.eval, gcdAB_read_a, zeroU, zeroS]

theorem gcd_condition_nonzero (a b c : GcdWord32) (nonzero : a ≠ 0) :
    gcdCondition.eval (gcdABCState a b c) = some 1 := by
  have castA := u32_cast_nat a.toNat a.isLt
  have positive : a.toNat ≠ 0 := by
    intro zero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using zero)
  have zeroS : s32.cast 0 = 0 := by native_decide
  have zeroU : u32.cast 0 = 0 := by native_decide
  have castA' : u32.cast (a.toNat : Int) = (a.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using castA
  simp [gcdCondition, Expr.eval, gcdABC_read_a, zeroS, zeroU]
  rw [castA']
  simpa using positive

end Zag.Test.AutoCorres.CParser.ScalarSimpl
