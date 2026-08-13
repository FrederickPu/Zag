import Test.AutoCorres.Upstream.Examples
import Test.AutoCorres.Upstream.ParseTests
import Test.AutoCorres.Upstream.ProofTests
import Test.AutoCorres.Upstream.KnownFailing
import Test.AutoCorres.Upstream.AdditionalSessions

/-!
# Complete pinned AutoCorres test manifest

This manually audited snapshot was checked against the recursive tree at
[`seL4/l4v@bc2599a`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests).
The core `AutoCorresTest` suite has 64 logical theories: 26 examples, 21 parse
tests, and 17 proof tests. Two theories are excluded as known failures. The
broader regression specification adds three quickstart/documentation theories
and one whole-seL4 integration theory. The framework build is tracked as a
validation target, not inflated into the logical test count. Lean checks the
snapshot's counts and uniqueness but does not access the network.
-/

namespace Zag.Test.AutoCorres.Upstream

def activeTests : List TestCase := exampleTests ++ parseTests ++ proofTests

def allValidationTests : List TestCase := activeTests ++ additionalValidationTests

def allValidationTargets : List ValidationTarget :=
  validationTargets (activeTests.map TestCase.sessionEntry)

def committedFiles : List SourceFile :=
  sourceFile "README" ::
    (exampleFiles ++ parseTestFiles ++ proofTestFiles ++ knownFailingFiles)

def coreReferencedFiles : List SourceFile :=
  referencedFiles (activeTests ++ knownFailingTests)

def additionalReferencedFiles : List SourceFile :=
  referencedFiles additionalValidationTests

theorem active_test_count : activeTests.length = 64 := by decide
theorem core_plus_excluded_count : (activeTests ++ knownFailingTests).length = 66 := by decide
theorem committed_file_count : committedFiles.length = 111 := by native_decide
theorem all_validation_test_count : allValidationTests.length = 68 := by decide
theorem all_validation_file_count :
    (committedFiles ++ additionalValidationFiles).length = 123 := by native_decide
theorem all_validation_target_count : allValidationTargets.length = 4 := by decide

theorem active_test_entries_are_unique :
    (activeTests.map TestCase.id).Nodup := by
  native_decide

theorem all_validation_entries_are_unique :
    (allValidationTests.map TestCase.id).Nodup := by
  native_decide

theorem committed_files_are_unique :
    (committedFiles.map SourceFile.relativePath).Nodup := by
  native_decide

theorem core_references_are_committed :
    coreReferencedFiles.all (fun file => committedFiles.contains file) = true := by
  native_decide

theorem additional_references_are_committed :
    additionalReferencedFiles.all
      (fun file => additionalValidationFiles.contains file) = true := by
  native_decide

theorem core_fragment_test_count :
    (activeTests.filter fun test => test.coverage.isFragment).length = 4 := by
  native_decide

theorem core_blocked_test_count :
    (activeTests.filter fun test => test.coverage.isBlocked).length = 58 := by
  native_decide

theorem core_complete_test_count :
    (activeTests.filter fun test => test.coverage.isComplete).length = 2 := by
  native_decide

theorem active_tests_are_not_known_failures :
    activeTests.all (fun test => !test.coverage.isUpstreamKnownFailing) = true := by
  native_decide

theorem known_failures_are_disjoint :
    (activeTests.map fun test => test.upstreamEntry.relativePath).all
      (fun path =>
        !(knownFailingTests.map fun test => test.upstreamEntry.relativePath).contains path) = true := by
  native_decide

theorem broader_blocked_test_count :
    (allValidationTests.filter fun test => test.coverage.isBlocked).length = 61 := by
  native_decide

theorem broader_fragment_test_count :
    (allValidationTests.filter fun test => test.coverage.isFragment).length = 5 := by
  native_decide

theorem broader_complete_test_count :
    (allValidationTests.filter fun test => test.coverage.isComplete).length = 2 := by
  native_decide

theorem fragment_entries_have_anchors :
    (allValidationTests.filter fun test => test.coverage.isFragment).all
      (fun test => !test.coverage.anchors.isEmpty) = true := by
  native_decide

theorem complete_entries_have_anchors :
    (allValidationTests.filter fun test => test.coverage.isComplete).all
      (fun test => !test.coverage.anchors.isEmpty) = true := by
  native_decide

theorem blocked_entries_have_no_anchors :
    (allValidationTests.filter fun test => test.coverage.isBlocked).all
      (fun test => test.coverage.anchors.isEmpty) = true := by
  native_decide

end Zag.Test.AutoCorres.Upstream
