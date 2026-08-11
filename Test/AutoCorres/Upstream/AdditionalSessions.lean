import Test.AutoCorres.Upstream.Types

/-!
# Additional AutoCorres validation sessions

The repository regression specification registers four targets in
[`tools/tests.xml`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/tests.xml):
the framework build, core tests, quickstart documentation, and whole-seL4
integration. This file accounts for objectives outside `tools/autocorres/tests`.
-/

namespace Zag.Test.AutoCorres.Upstream

inductive ValidationKind where
  | framework
  | coreRegression
  | documentation
  | integration
  deriving DecidableEq, Repr

structure ValidationTarget where
  name : String
  kind : ValidationKind
  directEntries : List String
  deriving DecidableEq, Repr

private def quickstartCase (name theory fixture reason : String) : TestCase :=
  { name
    session := "AutoCorresQuickstart"
    sessionEntry := name
    upstreamEntry := autocorresFile s!"doc/quickstart/{theory}"
    fixtures := [autocorresFile s!"doc/quickstart/{fixture}"]
    coverage := .blocked
    reason }

private def quickstartComplete (name theory fixture reason leanEntry : String)
    (anchor : Lean.Name) (additionalAnchors : List Lean.Name := []) : TestCase :=
  { name
    session := "AutoCorresQuickstart"
    sessionEntry := name
    upstreamEntry := autocorresFile s!"doc/quickstart/{theory}"
    fixtures := [autocorresFile s!"doc/quickstart/{fixture}"]
    coverage := .complete { moduleName := leanEntry, anchor, additionalAnchors }
    reason }

def additionalValidationTests : List TestCase := [
  quickstartCase "Chapter1_MinMax" "Chapter1_MinMax.thy" "minmax.c"
    "C parsing, generated translation, and the tutorial min/max proofs are unavailable",
  quickstartComplete "Chapter2_HoareHeap" "Chapter2_HoareHeap.thy" "mult_by_add.c"
    "exact quickstart fixture certificate and function/body identity with the completed MultByAdd invariant, termination, generated total-correctness, and no-failure pipeline"
    "Test.AutoCorres.Upstream.Chapter2_HoareHeap"
    `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.fixture_file_map_entry_is_exact
    [`Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.fixture_source_is_not_examples_source,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.fixture_certifies,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.function_is_mult_by_add_pipeline,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.body_is_exact_pipeline_shape,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.invariant_initial,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.invariant_preserved,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.variant_decreases,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.raw_fixture_total_no_failure,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.final_correspondence_uses_quickstart_function,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.final_total_correctness,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.final_no_failure,
     `Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap.mult_by_add_correct],
  quickstartCase "Chapter3_HoareHeap" "Chapter3_HoareHeap.thy" "swap.c"
    "C parsing, typed pointer heaps, and the tutorial Hoare proof are unavailable",
  { name := "TestSEL4"
    session := "AutoCorresSEL4"
    sessionEntry := "TestSEL4"
    upstreamEntry := autocorresFile "test-seL4/TestSEL4.thy"
    fixtures := []
    coverage := .blocked
    reason := "the architecture-generated kernel_all.c_pp, full C parser, and whole-kernel translation are unavailable" }
]

def quickstartSupportFiles : List SourceFile :=
  ["ROOT", "document/root.tex", "document/root.bib", "document/comment.sty",
   "document/ulem.sty"].map fun path => autocorresFile s!"doc/quickstart/{path}"

def quickstartFiles : List SourceFile :=
  referencedFiles (additionalValidationTests.filter fun test =>
    test.session == "AutoCorresQuickstart") ++ quickstartSupportFiles

def additionalValidationFiles : List SourceFile :=
  referencedFiles additionalValidationTests ++ quickstartSupportFiles

def validationTargets (coreEntries : List String) : List ValidationTarget := [
  { name := "AutoCorres", kind := .framework,
    directEntries := ["DataStructures", "AutoCorres"] },
  { name := "AutoCorresTest", kind := .coreRegression,
    directEntries := coreEntries },
  { name := "AutoCorresDoc", kind := .documentation,
    directEntries := ["Chapter1_MinMax", "Chapter2_HoareHeap", "Chapter3_HoareHeap"] },
  { name := "AutoCorresSEL4", kind := .integration,
    directEntries := ["TestSEL4"] }
]

/-- Architectures recommended by the upstream development README. -/
def developmentArchitectures : List String := ["ARM", "X64"]

/-- Broader architecture matrix used by the optional release validation script. -/
def releaseArchitectures : List String :=
  ["ARM", "ARM_HYP", "X64", "RISCV64", "AARCH64"]

theorem additional_validation_test_count : additionalValidationTests.length = 4 := by decide
theorem additional_validation_file_count : additionalValidationFiles.length = 12 := by decide
theorem validation_target_count (coreEntries : List String) :
    (validationTargets coreEntries).length = 4 := by rfl

end Zag.Test.AutoCorres.Upstream
