import Test.AutoCorres.Upstream.Types

/-!
# Upstream known-failing tests

The upstream Makefile excludes
[`tests/failing`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/failing)
from the `AutoCorresTest` session. These entries are recorded separately and
must never be reported as local passing tests.
-/

namespace Zag.Test.AutoCorres.Upstream

def knownFailingTests : List TestCase := [
  { knownFailingCase "dirty_frees" "failing/dirty_frees.thy"
      "four naming cases succeed before the final expected free-variable/name failure" with
    fixtures := [sourceFile "failing/dirty_frees.c"] },
  { knownFailingCase "jira_ver_591" "failing/jira_ver_591.thy"
      "upstream expects translation failure followed by a keep_going retry" with
    fixtures := [sourceFile "failing/jira_ver_591.c"] }
]

def knownFailingFiles : List SourceFile := referencedFiles knownFailingTests

theorem known_failing_test_count : knownFailingTests.length = 2 := by decide
theorem known_failing_file_count : knownFailingFiles.length = 4 := by decide

end Zag.Test.AutoCorres.Upstream
