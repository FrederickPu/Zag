import Lang.AutoCorres.CParser.PhasePipeline.Scalar
import Test.AutoCorres.CParser.EmbeddedFixtures
import Test.AutoCorres.CParser.ScalarSimpl.Common

/-! # Certified fixture setup for generated parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Test.AutoCorres.CParser
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
run_refinement prepared from
  Scalar.prepare .arm EmbeddedFixtures.files "parse-tests/while_loop_no_vars.c" "foo"
success_by native_decide

abbrev certified := prepared.certified
abbrev support := prepared.supported

def addExpression : ScalarSimpl.Expr :=
  .binary s32 s32 .add (.variable s32 1) (.variable s32 2)

def expectedFunction : Function :=
  { name := "foo"
    returnType := s32
    parameters := [(1, s32), (2, s32)]
    locals := []
    body := .seq (.return s32 addExpression) .skip }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem exact_function_and_body : certified.function = expectedFunction := by
  native_decide

def expectedExpressionSupport :
    Scalar.AddExpression .signed .w32 [(1, s32), (2, s32)] addExpression := by
  derive_add_expression <;> simp [s32, Scalar.scalarType, WordAbstract.WordWidth.bits]

theorem recognized_from_exact_fixture :
    Scalar.recognizes certified.function = true := by
  rw [exact_function_and_body]
  native_decide

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
