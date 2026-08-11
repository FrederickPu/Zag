import Test.AutoCorres.CParser.ScalarSimpl.GcdLoopExecution

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def gcdInitial (a b : GcdWord32) : State :=
  match gcdFunction.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] with
  | .ok state => state
  | .error _ => {}

theorem gcd_declared_state (a b : GcdWord32) :
    (gcdInitial a b).resetReturn.clear 3 = gcdABState a b := by
  simp [gcdInitial, gcd_is_exact_resolved_function, expectedGcd, Function.enter,
    gcdABState, State.resetReturn, State.clear, State.write]

def gcdReturnedState (state : State) (value : GcdWord32) : State :=
  state.returnValue u32 (Int.ofNat value.toNat)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
