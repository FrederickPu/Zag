import Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVarsFixture

/-! # Signed generated behavior for parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

def expressionState (a b : Int) : State :=
  (State.write {} 1 s32 a).write 2 s32 b

def generatedExpressionEvidence :=
  ML.WordAbstract.Expr.transform expectedExpressionSupport.signedWordSupported

def generatedCertificate : WordAbstract.Kernel.Certificate
    (WordAbstract.Kernel.Source.Syntax.gets (exception := .unit)
      expectedExpressionSupport.signedWordExpression ["ret"]) :=
  ML.WordAbstract.transform
    (.gets (exception := .unit) expectedExpressionSupport.signedWordSupported ["ret"])

theorem exact_signed_body_wraps :
    expectedExpressionSupport.signedWordExpression.eval ()
      (expressionState 2147483647 1) = BitVec.ofInt 32 (-2147483648) := by
  native_decide

theorem signed_in_range_behavior :
    generatedExpressionEvidence.target.eval () (expressionState 19 23) = 42 ∧
      generatedExpressionEvidence.guard () (expressionState 19 23) := by
  simp [generatedExpressionEvidence, expectedExpressionSupport,
    AddExpression.signedWordSupported, AddExpression.signedWordExpression,
    expressionState, State.write, State.read?, s32, ScalarType.cast,
    ScalarType.unsignedValue, ScalarType.modulus,
    ML.WordAbstract.Expr.transform, WordAbstract.WordWidth.bits,
    WordAbstract.Kernel.Target.Expr.eval, WordAbstract.Kernel.Target.asInt,
    WordAbstract.signedBinaryGuard, WordAbstract.signedBinaryCDefined,
    WordAbstract.signedBinaryAbstractable, WordAbstract.signedBinary,
    WordAbstract.signedInRange, WordAbstract.SWORD_MIN,
    WordAbstract.SWORD_MAX] <;> native_decide

theorem signed_overflow_is_guarded :
    ¬generatedExpressionEvidence.guard ()
      (expressionState 2147483647 1) := by
  simp [generatedExpressionEvidence, expectedExpressionSupport,
    AddExpression.signedWordSupported, AddExpression.signedWordExpression,
    expressionState, State.write, State.read?, s32, ScalarType.cast,
    ScalarType.unsignedValue, ScalarType.modulus,
    ML.WordAbstract.Expr.transform, WordAbstract.WordWidth.bits,
    WordAbstract.Kernel.Target.Expr.eval, WordAbstract.Kernel.Target.asInt,
    WordAbstract.signedBinaryGuard, WordAbstract.signedBinaryCDefined,
    WordAbstract.signedBinaryAbstractable, WordAbstract.signedBinary,
    WordAbstract.signedInRange, WordAbstract.SWORD_MIN,
    WordAbstract.SWORD_MAX] <;> native_decide

theorem generated_target_has_signed_guard :
    generatedCertificate.target =
      WordAbstract.Kernel.Target.Syntax.seq
        (.guard generatedExpressionEvidence.guard)
        (fun _ => .gets generatedExpressionEvidence.target ["ret"]) := by
  rfl

theorem signed_overflow_target_fails :
    (generatedCertificate.target.denote ()
      (expressionState 2147483647 1)).failed := by
  rw [generated_target_has_signed_guard]
  simp [WordAbstract.Kernel.Target.Syntax.denote, L2.seq, L2.guard,
    signed_overflow_is_guarded, bindE, L2.failed_liftE,
    Zag.Lang.AutoCorres.guard]

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
