import Test.AutoCorres.Upstream.Types

/-!
# Upstream generated parse tests

The upstream Makefile generates one theory entry from every C file in
[`tests/parse-tests`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/parse-tests).
Zag's StrictC frontend parses the vendored fixtures. Complete generated tests
remain blocked until the generated WordAbstract and TypeStrengthen artifacts
are adjacent to the exact LVE endpoint rather than an identity side chain.
-/

namespace Zag.Test.AutoCorres.Upstream

private def parserUnavailable (name : String) : TestCase :=
  { name
    sessionEntry := s!"parse-tests/{name}"
    upstreamEntry := sourceFile s!"parse-tests/{name}.c"
    fixtures := []
    coverage := .blocked
    reason := "the generated theory requires full upstream parser installation, C-to-SIMPL lowering, and a complete AutoCorres run" }

def parseTests : List TestCase :=
  ["basic", "basic_recursion", "big_bit_ops", "bodyless_function", "heap_infer",
   "heap_lift_array", "l2_opt_invariant", "loop_test", "loop_test2",
   "mutual_recursion", "mutual_recursion2", "nested_break_cont",
   "read_global_array", "signed_ptr_ptr", "struct1", "struct_init",
     "unliftable_call", "voidptrptr", "while_loop_no_vars", "word_abs_exn",
   "write_to_global_array"].map parserUnavailable

def parseTestFiles : List SourceFile := referencedFiles parseTests

theorem parse_test_count : parseTests.length = 21 := by decide
theorem parse_test_file_count : parseTestFiles.length = 21 := by decide
theorem parse_test_complete_count :
    (parseTests.filter fun test => test.coverage.isComplete).length = 0 := by decide
theorem parse_test_blocked_count :
    (parseTests.filter fun test => test.coverage.isBlocked).length = 21 := by decide

end Zag.Test.AutoCorres.Upstream
