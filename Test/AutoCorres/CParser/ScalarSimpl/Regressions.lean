import Test.AutoCorres.CParser.ScalarSimpl.SelfInitializer

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

private def malformedOctalFiles : Preprocessor.FileMap :=
  [{ name := "malformed-octal.c", source := "unsigned bad(void) { return 09; }" }]

theorem malformed_octal_frontend_is_rejected :
    !(Frontend.preprocessAndAnalyze .arm malformedOctalFiles "malformed-octal.c").isSuccess := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem malformed_octal_cannot_certify :
    !(certifyFrontend .arm malformedOctalFiles "malformed-octal.c" "bad").isOk := by
  native_decide

private def shadowProgram : Option ProgramAnalysis.Program :=
  (Frontend.analyzeSource .arm "shadow.c" "
    int shadow(int x) {
      int y = x;
      { int x = 7; y = x; }
      return x;
    }").program

private def shadowResolved : Option Function := do
  let program ← shadowProgram
  (resolveIR program "shadow").toOption

theorem lexical_shadowing_uses_allocated_ids :
    shadowResolved.map Function.body = some
      (.seq (.declare 2 s32 (some (.variable s32 1)))
        (.seq
          (.seq
            (.seq (.declare 3 s32 (some (.literal s32 7)))
              (.seq (.assign 2 s32 (.variable s32 3)) .skip))
            .skip)
          (.seq (.return s32 (.variable s32 1)) .skip))) := by
  native_decide

private def globalReadResult (source : String) :
    Option (Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error Function) := do
  let program ← (Frontend.analyzeSource .arm "global.c" source).program
  pure (resolveIR program "read_global")

private def isRejectedGlobalRead :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error Function → Bool
  | .error (.unresolvedIdentifier _ "global") => true
  | _ => false

example : (globalReadResult "
    int global;
    int read_global(void) { return global; }").any isRejectedGlobalRead := by
  native_decide

example : (globalReadResult "
    int global = 7;
    int read_global(void) { return global; }").any isRejectedGlobalRead := by
  native_decide

private def minS32 : Int := -((2 : Int) ^ 31)

example : Expr.eval (.binary s32 s32 .add (.literal s32 2147483647) (.literal s32 1)) {} =
    none := by native_decide

example : Expr.eval (.binary s32 s32 .divide (.literal s32 1) (.literal s32 0)) {} =
    none := by native_decide

example : Expr.eval (.binary s32 s32 .modulus (.literal s32 1) (.literal s32 0)) {} =
    none := by native_decide

example : Expr.eval (.binary s32 s32 .divide (.literal s32 minS32) (.literal s32 (-1))) {} =
    none := by native_decide

example : Expr.eval (.binary s32 s32 .modulus (.literal s32 minS32) (.literal s32 (-1))) {} =
    none := by native_decide

example : Expr.eval (.binary s32 s32 .divide (.literal s32 (-7)) (.literal s32 3)) {} =
    some (-2) := by native_decide

example : Expr.eval (.binary s32 s32 .modulus (.literal s32 (-7)) (.literal s32 3)) {} =
    some (-1) := by native_decide

example : Expr.eval (.variable s32 17) {} = none := by native_decide

example : Stmt.Exec (.while (.variable s32 17) .skip) {} .fault :=
  .whileGuardFault (by native_decide)

example : Stmt.Exec
    (.while (.literal s32 1) (.return s32 (.literal s32 9))) {}
    (.returned (State.returnValue {} s32 9)) := by
  apply Stmt.Exec.whileRet (value := 1)
  · native_decide
  · decide
  · exact .ret (by native_decide)

private def mainFallthrough : Function :=
  { name := "main", returnType := s32, parameters := [], locals := [], body := .skip }

private def parsedMainCertifies : Bool :=
  match (Frontend.analyzeSource .arm "main.c" "int main(void) { }").program with
  | some program => (resolveIR program "main").isOk
  | none => false

example : parsedMainCertifies := by native_decide

example : mainFallthrough.Exec {} (.normal (State.returnValue {} s32 0)) := by
  simpa [mainFallthrough] using Function.Exec.fellOff (function := mainFallthrough)
    (state := {}) (result := {}) Stmt.Exec.skip

example : Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment mainFallthrough.command
    (.normal {}) (.normal (State.returnValue {} s32 0)) :=
  mainFallthrough.command_correct _ _ (by
    simpa [mainFallthrough] using Function.Exec.fellOff (function := mainFallthrough)
      (state := {}) (result := {}) Stmt.Exec.skip)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
