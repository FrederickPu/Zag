import Lang.AutoCorres.CParser.PhasePipeline.Scalar
import Test.AutoCorres.CParser.EmbeddedFixtures
import Test.AutoCorres.CParser.ScalarSimpl.Common

/-! # Certified fixture setup for generated parse test `basic` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Test.AutoCorres.CParser
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
run_refinement prepared from
  Scalar.prepare .arm EmbeddedFixtures.files "parse-tests/basic.c" "add"
success_by native_decide

abbrev certified := prepared.certified
abbrev support := prepared.supported

def addExpression : ScalarSimpl.Expr :=
  .binary u32 u32 .add (.variable u32 1)
    (.binary u32 u32 .add (.variable u32 2) (.variable u32 3))

def expectedFunction : Function :=
  { name := "add"
    returnType := u32
    parameters := [(1, u32), (2, u32), (3, u32)]
    locals := []
    body := .seq (.return u32 addExpression) .skip }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem exact_function_and_body : certified.function = expectedFunction := by
  native_decide

def expectedExpressionSupport : Scalar.AddExpression .unsigned .w32
    [(1, u32), (2, u32), (3, u32)] addExpression := by
  derive_add_expression <;> simp [u32, Scalar.scalarType, WordAbstract.WordWidth.bits]

theorem recognized_from_exact_fixture :
    Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.recognizes
      certified.function = true := by
  rw [exact_function_and_body]
  native_decide

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
