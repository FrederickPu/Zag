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

def installation := ScalarSimpl.certifyFrontend .arm EmbeddedFixtures.files
  "parse-tests/basic.c" "add"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem installation_succeeds : installation.isOk := by native_decide

def certified : ScalarSimpl.Certified .arm EmbeddedFixtures.files
    "parse-tests/basic.c" "add" :=
  installation.toOption.get
    (except_toOption_isSome_of_isOk installation installation_succeeds)

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

def expectedExpressionSupport :
    Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.AddExpression .unsigned .w32
      [(1, u32), (2, u32), (3, u32)] addExpression :=
  .add (.parameter 1 (by
      simp [u32, Scalar.scalarType, WordAbstract.WordWidth.bits]))
      (.add (.parameter 2 (by
        simp [u32, Scalar.scalarType, WordAbstract.WordWidth.bits]))
        (.parameter 3 (by
          simp [u32, Scalar.scalarType, WordAbstract.WordWidth.bits])))

def expectedSupport :
    Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.Supported expectedFunction :=
  .returnedAdd "add" .w32 [(1, u32), (2, u32), (3, u32)] addExpression
    expectedExpressionSupport

def support : Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.Supported
    certified.function :=
  expectedSupport.transport exact_function_and_body.symm

theorem recognized_from_exact_fixture :
    Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.recognizes
      certified.function = true := by
  rw [exact_function_and_body]
  native_decide

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
