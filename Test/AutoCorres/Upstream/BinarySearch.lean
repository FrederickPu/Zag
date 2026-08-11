import Lang.AutoCorres.CParser.MemorySimpl
import Test.AutoCorres.CParser.EmbeddedFixtures

/-!
# Binary search fixture-derived lowering

This certifies the pinned C function through parsing, analysis, memory layout,
statement resolution, and the generated SIMPL correspondence. The upstream
sorted-array model and total-correctness theorem remain separate obligations.
-/

namespace Zag.Test.AutoCorres.Upstream.BinarySearch

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.MemorySimpl

def entry : String := "examples/binary_search.c"
def functionName : String := "binary_search"

def fixtureResult :=
  certifyFrontend .arm Zag.Test.AutoCorres.CParser.EmbeddedFixtures.files entry functionName

def frontendResult :=
  Frontend.preprocessAndAnalyze .arm Zag.Test.AutoCorres.CParser.EmbeddedFixtures.files entry

theorem frontend_succeeds : frontendResult.isSuccess := by
  native_decide

theorem generated_function_is_unique :
    frontendResult.program.map (fun program => (selectedFunctions program functionName).length) =
      some 1 := by
  native_decide

def isLogicalGuardBlocker : Except MemorySimpl.Error α → Bool
  | .error (.unsupportedExpression region description) =>
      region.left.file == entry && region.left.line == 17 && region.left.column == 11 &&
        description == "integer operator is not implemented"
  | _ => false

theorem lowering_reaches_line_17_operator_blocker :
    isLogicalGuardBlocker fixtureResult := by
  native_decide

end Zag.Test.AutoCorres.Upstream.BinarySearch
