import Test.AutoCorres.Upstream.Types

/-!
# Upstream proof tests

Every committed theory entry and supporting C fixture is inventoried from
[`tests/proof-tests`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/proof-tests).
These are blocked until their complete upstream objective can be represented;
availability of an isolated kernel rule is not counted as a port.
-/

namespace Zag.Test.AutoCorres.Upstream

private def proofBlocked (name theory fixture reason : String) : TestCase :=
  { blockedCase name s!"proof-tests/{theory}" reason with
    fixtures := [sourceFile s!"proof-tests/{fixture}"] }

private def proofComplete (name theory fixture reason leanEntry : String)
    (anchor : Lean.Name) (additionalAnchors : List Lean.Name) : TestCase :=
  { completeCase name s!"proof-tests/{theory}" reason leanEntry anchor additionalAnchors with
    fixtures := [sourceFile s!"proof-tests/{fixture}"] }

def proofTests : List TestCase := [
  proofBlocked "array_indirect_update" "array_indirect_update.thy" "array_indirect_update.c" "array descriptors and HeapLift calls are representable, but parser layouts, symbols, earlier-phase calls, and automatic indirect-update evidence are unavailable",
  proofBlocked "badnames" "badnames.thy" "badnames.c" "C parser generated-name, collision, and demangling behavior is unavailable",
  proofBlocked "CustomWordAbs" "CustomWordAbs.thy" "custom_word_abs.c" "the built-in signed, bitwise, shift, comparison, and modulo kernel exists, but mutable user-installed WA rules and generated C functions are unavailable",
  proofBlocked "global_array_update" "global_array_update.thy" "global_array_update.c" "certified bounded-memory lowering is implemented but not yet safely build-verified; HeapLift evidence and the upstream Hoare theorem remain unavailable",
  proofBlocked "heap_lift_force_prevent" "heap_lift_force_prevent.thy" "heap_lift_force_prevent.c" "mixed execution and certified calls exist; automatic per-function force/prevent options, eligibility, interfaces, and scheduling are unavailable",
  proofBlocked "nested_struct" "nested_struct.thy" "nested_struct.c" "explicit field obligations exist, but nested packed layout and field-address generation are unavailable",
  proofBlocked "prototyped_functions" "prototyped_functions.thy" "prototyped_functions.c" "carrier unknown/failure forms exist, but bodyless-function generation and call-graph integration are unavailable",
  proofBlocked "SignedWordAbsHeap" "SignedWordAbsHeap.thy" "signed_word_abs_heap.c" "typed signed state reads and scalar WA are available, but automatic signed HeapLift getter rules and parser-generated heap integration are unavailable",
  proofComplete "skip_heap_abs" "skip_heap_abs.thy" "skip_heap_abs.c" "the exact fixture is analyzed and lowered with bounded caller memory; generated persistent metadata omits HeapLift while retaining certified SimplConv/LVE and exact later-phase endpoints"
    "Test.AutoCorres.Upstream.SkipHeapAbs"
    `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.heap_lift_metadata_absent
    [`Zag.Test.AutoCorres.Upstream.SkipHeapAbs.exact_fixture_analyzed,
     `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.simpl_corresponds,
     `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.lve_corresponds,
     `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.word_abstract_corresponds,
     `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.type_strengthen_is_exact,
     `Zag.Test.AutoCorres.Upstream.SkipHeapAbs.behavioral_endpoint],
  proofComplete "struct" "struct.thy" "struct.c" "the exact external file is installed successfully with pinned source provenance, struct tag and canonical name, field and ARM layout metadata, exact by-value function signature, unique symbols, and stable generated type names"
    "Test.AutoCorres.Upstream.Struct"
    `Zag.Test.AutoCorres.Upstream.Struct.install_C_file_certificate
    [`Zag.Test.AutoCorres.Upstream.Struct.exact_source_provenance,
     `Zag.Test.AutoCorres.Upstream.Struct.install_C_file_succeeds,
     `Zag.Test.AutoCorres.Upstream.Struct.struct_tag_fields_are_exact,
     `Zag.Test.AutoCorres.Upstream.Struct.arm_size_alignment_layout_are_exact,
     `Zag.Test.AutoCorres.Upstream.Struct.by_value_signature_is_exact,
     `Zag.Test.AutoCorres.Upstream.Struct.installed_symbols_are_unique,
     `Zag.Test.AutoCorres.Upstream.Struct.generated_type_names_are_stable],
  proofBlocked "struct2" "struct2.thy" "struct2.c" "complex structure parsing and keep_going command behavior are unavailable",
  proofBlocked "struct3" "struct3.thy" "struct.c" "cross-theory parser state and generated type-name reuse are unavailable",
  proofBlocked "Test_Spec_Translation" "Test_Spec_Translation.thy" "test_spec_translation.c" "supplied heap/TS specs and HeapLift calls are representable, but LVE specs, C annotations, and generated earlier-phase calls are unavailable",
  proofBlocked "WhileLoopVarsPreserved" "WhileLoopVarsPreserved.thy" "while_loop_vars_preserved.c" "all-locals loops exist, but upstream per-variable liveness analysis and its regression objective are unavailable",
  proofBlocked "word_abs_cases" "word_abs_cases.thy" "word_abs_cases.c" "signed multiply, negation, and truncating modulo are certified locally, but WA calls, loops, heaps, SCC generation, and the fixture's optimization rules are unavailable",
  proofBlocked "word_abs_options" "word_abs_options.thy" "word_abs_options.c" "signed and unsigned scalar abstraction and identity paths exist, but automatic per-function option dispatch and generated definitions are unavailable",
  proofBlocked "WordAbsFnCall" "WordAbsFnCall.thy" "word_abs_fn_call.c" "heap mixed calls exist, but WA calls, mixed signatures, and per-function abstraction dispatch are unavailable"
]

def proofTestFiles : List SourceFile := referencedFiles proofTests

theorem proof_test_count : proofTests.length = 17 := by decide
theorem proof_test_file_count : proofTestFiles.length = 33 := by decide

end Zag.Test.AutoCorres.Upstream
