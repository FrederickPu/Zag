import Test.AutoCorres.CParser.PhasePipeline.BasicWrapping

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

def generatedExpressionEvidence :=
  ML.WordAbstract.Expr.transform
    expectedExpressionSupport.unsignedWordSupported

/-- Ordinary inputs satisfy every generated WordAbstract arithmetic guard. -/
theorem ordinary_inputs_pass_generated_guards :
    generatedExpressionEvidence.guard () (expressionState 3 4 5) := by
  simp [generatedExpressionEvidence, expectedExpressionSupport,
    AddExpression.unsignedWordSupported, AddExpression.unsignedWordExpression,
    expressionState, State.write, State.read?, u32, ScalarType.cast,
    ScalarType.unsignedValue, ScalarType.modulus, ML.WordAbstract.Expr.transform,
    WordAbstract.WordWidth.bits, WordAbstract.Kernel.Target.Expr.eval,
    WordAbstract.Kernel.Target.asNat, WordAbstract.Kernel.Target.maxFor,
    WordAbstract.UWORD_MAX]

/-- Overflow is not silently strengthened to unbounded addition. -/
theorem overflow_is_guarded :
    ¬generatedExpressionEvidence.guard ()
      (expressionState (BitVec.ofNat 32 4294967295) 1 0) := by
  simp [generatedExpressionEvidence, expectedExpressionSupport,
    AddExpression.unsignedWordSupported, AddExpression.unsignedWordExpression,
    expressionState, State.write, State.read?, u32, ScalarType.cast,
    ScalarType.unsignedValue, ScalarType.modulus, ML.WordAbstract.Expr.transform,
    WordAbstract.WordWidth.bits, WordAbstract.Kernel.Target.Expr.eval,
    WordAbstract.Kernel.Target.asNat, WordAbstract.Kernel.Target.maxFor,
    WordAbstract.UWORD_MAX]

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
