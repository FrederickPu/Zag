import Lang.AutoCorres.CParser.MemorySimpl
import Test.AutoCorres.CParser.EmbeddedFixtures

/-!
# `BinarySearch` upstream fragment

Sources:

* [`binary_search.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/binary_search.c)
* [`BinarySearch.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/BinarySearch.thy)

The exact fixture passes the frontend and uniquely resolves `binary_search`.
Certified lowering then stops at the short-circuit loop guard, before an
AutoCorres function or the upstream array and total-correctness proofs exist.
-/

namespace Zag.Test.AutoCorres.Upstream.BinarySearch

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.MemorySimpl

def entry : String := "examples/binary_search.c"
def functionName : String := "binary_search"
abbrev Files := Zag.Test.AutoCorres.CParser.EmbeddedFixtures.files

def frontendResult :=
  Frontend.preprocessAndAnalyze .arm Files entry

theorem frontend_succeeds : frontendResult.isSuccess := by
  native_decide

theorem generated_function_is_unique :
    frontendResult.program.map (fun program => (selectedFunctions program functionName).length) =
      some 1 := by
  native_decide

def fixtureResult := certifyFrontend .arm Files entry functionName

def isLogicalGuardBlocker : Except MemorySimpl.Error α → Bool
  | .error (.unsupportedExpression region description) =>
      region == {
        left := { file := entry, line := 17, column := 11, offset := 341 }
        right := { file := entry, line := 17, column := 25, offset := 355 } } &&
        description == "integer operator is not implemented"
  | _ => false

theorem lowering_reaches_line_17_operator_blocker :
    isLogicalGuardBlocker fixtureResult := by
  native_decide

end Zag.Test.AutoCorres.Upstream.BinarySearch
