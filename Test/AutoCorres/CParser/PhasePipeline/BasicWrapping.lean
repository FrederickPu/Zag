import Test.AutoCorres.CParser.PhasePipeline.BasicFixture

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

def expressionState (a b c : BitVec 32) : State :=
  ((State.write {} 1 u32 (Int.ofNat a.toNat)).write
    2 u32 (Int.ofNat b.toNat)).write 3 u32 (Int.ofNat c.toNat)

/-- The exact fixture body denotes wrapping three-argument word addition. -/
theorem exact_body_wraps :
    expectedExpressionSupport.unsignedWordExpression.eval ()
      (expressionState (BitVec.ofNat 32 4294967295) 1 0) = 0 := by
  native_decide

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
