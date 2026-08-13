import Test.AutoCorres.Upstream.Types

/-!
# Upstream example tests

Every entry and fixture below links through `SourceFile.url` to the pinned
[`tests/examples`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples)
directory. `fragment` means this repository exercises only named phase-local
behavior, not the complete upstream theory. `complete` requires fixture-derived
coverage of every explicit inspection and theorem objective, including every
function on which those declarations depend; unreferenced generated artifacts
are not counted as theorem objectives.

Anchor names are symbolic here so inventory compilation does not load every
large proof pipeline into one Lean process. Their modules are registered and
compiled independently by the test targets.
-/

namespace Zag.Test.AutoCorres.Upstream

private def exampleBlocked (name theory reason : String)
    (fixtures : List String) : TestCase :=
  { blockedCase name s!"examples/{theory}" reason with
    fixtures := fixtures.map fun fixture => sourceFile s!"examples/{fixture}" }

private def exampleFragment (name theory reason leanEntry : String)
    (anchor : Lean.Name) (additionalAnchors : List Lean.Name)
    (fixtures : List String) : TestCase :=
  { fragmentCase name s!"examples/{theory}" reason leanEntry anchor additionalAnchors with
    fixtures := fixtures.map fun fixture => sourceFile s!"examples/{fixture}" }

private def exampleComplete (name theory reason leanEntry : String)
    (anchor : Lean.Name) (additionalAnchors : List Lean.Name)
    (fixtures : List String) : TestCase :=
  { completeCase name s!"examples/{theory}" reason leanEntry anchor additionalAnchors with
    fixtures := fixtures.map fun fixture => sourceFile s!"examples/{fixture}" }

def exampleTests : List TestCase := [
  exampleBlocked "AC_Rename" "AC_Rename.thy" "generated C and phase symbol renaming is unavailable" ["rename.c"],
  exampleBlocked "Alloc" "Alloc.thy" "header parsing, structs, linked heaps, casts, loops, calls, and generated allocator definitions are unavailable" ["alloc.c", "alloc.h"],
  exampleFragment "BinarySearch" "BinarySearch.thy" "the exact fixture passes frontend analysis and uniquely selects binary_search, but certified lowering stops at short-circuit conjunction; parameter-pointer indexing and bounds, typed array HeapLift, unsigned abstraction, nondeterministic strengthening, the array model, and total correctness remain unavailable"
    "Test.AutoCorres.Upstream.BinarySearch"
    `Zag.Test.AutoCorres.Upstream.BinarySearch.frontend_succeeds
    [`Zag.Test.AutoCorres.Upstream.BinarySearch.generated_function_is_unique,
     `Zag.Test.AutoCorres.Upstream.BinarySearch.lowering_reaches_line_17_operator_blocker]
    ["binary_search.c"],
  exampleBlocked "CList" "CList.thy" "typed pointer heaps, loop translation, and the list-model proofs are unavailable" ["list.c"],
  exampleBlocked "ConditionGuard" "ConditionGuard.thy" "parser-generated pointer and division guards plus generated definitions are unavailable" ["condition_guard.c"],
  exampleBlocked "FactorialTest" "FactorialTest.thy" "recursive SCC translation, option termination, call translation, and correctness proofs are unavailable" ["factorial.c"],
  exampleBlocked "FibProof" "FibProof.thy" "recursive SCC translation, unsigned abstraction, loop proofs, and call proofs are unavailable" ["fib.c"],
  exampleBlocked "FunctionInfoDemo" "FunctionInfoDemo.thy" "persistent phase and heap metadata registries are unavailable" ["function_info.c"],
  exampleBlocked "HeapWrap" "HeapWrap.thy" "heap_abs_syntax and generated typed-heap notation are unavailable" ["heap_wrap.c"],
  exampleBlocked "Incremental" "Incremental.thy" "persistent scoped translation state, option handling, dependency reuse, and generated wrappers are unavailable" ["type_strengthen.c"],
  exampleBlocked "IsPrime" "IsPrime.thy" "loops, multiplication/modulo abstraction, ts_rules nondet processing, and primality proofs are unavailable" ["is_prime.c"],
  exampleBlocked "Kmalloc" "Kmalloc.thy" "C parsing and parser/AutoCorres generated-definition checks are unavailable" ["kmalloc.c"],
  exampleBlocked "ListRev" "ListRev.thy" "typed pointer heaps, loop lifting, list models, and reversal proofs are unavailable" ["list_rev.c"],
  exampleBlocked "Memcpy" "Memcpy.thy" "raw byte-heap semantics, no_heap_abs dispatch, wrappers/calls, struct copying, and proofs are unavailable" ["memcpy.c"],
  exampleBlocked "Memset" "Memset.thy" "mixed raw-byte and lifted typed-heap behavior plus both correctness proofs are unavailable" ["memset.c"],
  exampleFragment "MultByAdd" "MultByAdd.thy" "fixture-derived body semantics, wrapping invariant and termination, and a certified manually assembled five-phase endpoint are present; the endpoint returns Nat at encoded internal state, the composed correspondence does not check termination, and the upstream SIMPL CALL/assignment Hoare theorem is absent"
    "Test.AutoCorres.Upstream.MultByAdd"
    `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_fixture_certifies
    [`Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_body_is_actual_initialized_loop,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_loop_body_has_actual_post_decrement,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_finite_execution_iff,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_invariant_initial,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_invariant_preserved,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_variant_decreases,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_simpl_partial_correctness,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.mult_by_add_total_no_failure,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.fixture_simpl_endpoint,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.lve_consumes_fixture_endpoint,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.heapLiftCorres,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.word_consumes_heap_endpoint,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.type_strengthen_consumes_word_endpoint,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.finalAcCorres,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.final_target_no_failure,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.mult_by_add_correct,
     `Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.mult_by_add_end_to_end,
     `Zag.Test.AutoCorres.Upstream.MultByAdd.SimplConv.manual_source_corres,
     `Zag.Test.AutoCorres.Upstream.MultByAdd.LocalVarExtract.manual_source_extracts,
     `Zag.Test.AutoCorres.Upstream.MultByAdd.TypeStrengthen.manual_phase_exact]
    ["mult_by_add.c"],
  exampleComplete "Plus" "Plus.thy" "the embedded source is reflected directly; `plus` and the forced-nondeterministic `plus2` target expose the upstream correctness and no-failure results"
    "Test.AutoCorres.Upstream.Plus"
    `Zag.Test.AutoCorres.Upstream.Plus.plus_three_plus_two
    [`Zag.Test.AutoCorres.Upstream.Plus.plus_correct,
       `Zag.Test.AutoCorres.Upstream.Plus.plus2'_ac_corres,
       `Zag.Test.AutoCorres.Upstream.Plus.plus2_correct,
       `Zag.Test.AutoCorres.Upstream.Plus.plus2_is_plus,
       `Zag.Test.AutoCorres.Upstream.Plus.plus2_valid]
    ["plus.c"],
  exampleBlocked "Quicksort" "Quicksort.thy" "recursive functions, pointer arrays, typed heaps, and sorting proofs are unavailable" ["quicksort.c"],
  exampleBlocked "SchorrWaite" "SchorrWaite.thy" "graph heap lifting, traversal, and the graph proof are unavailable" ["schorr_waite.c"],
  exampleFragment "Simple" "Simple.thy" "gcd has a fixture-derived certified endpoint for arbitrary u32 inputs, but the exact unsigned-abstracted gcd interface, universal gcd_wp, monad_to_gets, and gcd-to-return theorem are absent; max lacks a fixture-connected generated pure endpoint and max'_ac_corres"
    "Test.AutoCorres.Upstream.Simple"
    `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.final_target_exact
    [`Zag.Test.AutoCorres.CParser.ScalarSimpl.maxCertificate,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.max_finite_execution_iff,
      `Zag.Test.AutoCorres.Upstream.Simple.manual_source_corres,
      `Zag.Test.AutoCorres.Upstream.Simple.chooses_larger_argument,
      `Zag.Test.AutoCorres.Upstream.Simple.TypeStrengthen.manual_phase_exact,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.fixture_shape,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.finite_c_simpl_correspondence,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.invariant_preserved,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.variant_decreases,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.final_result,
      `Zag.Test.AutoCorres.Upstream.Simple.Gcd.word_abstract_guarded_map,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.fixture_simpl_endpoint,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.lve_consumes_fixture_endpoint,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.heapLiftCorres,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.word_consumes_heap_endpoint,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.type_strengthen_consumes_word_endpoint,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.finalAcCorres,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.final_target_pure_return,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.final_target_no_failure,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.final_target_returns_only_gcd,
      `Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline.final_target_valid]
    ["simple.c"],
  exampleBlocked "Str2Long" "Str2Long.thy" "string heaps and signed arithmetic are unavailable; upstream's draft Hoare goal ends in oops" ["str2long.c"],
  exampleBlocked "Suzuki" "Suzuki.thy" "pointer-rich typed heaps and the AutoCorres frame proof are unavailable" ["suzuki.c"],
  exampleBlocked "Swap" "Swap.thy" "typed pointer heaps and the swap correctness proof are unavailable" ["swap.c"],
  exampleBlocked "TraceDemo" "TraceDemo.thy" "phase, optimization, and registry trace output is unavailable" ["trace_demo.c"],
  exampleBlocked "type_strengthen_tricks" "type_strengthen_tricks.thy" "mutable TS rule deletion, selectable rule sets, forced tiers, and generated type checks are unavailable" ["type_strengthen.c"],
  exampleBlocked "WordAbs" "WordAbs.thy" "the scalar operation kernel is certified locally, but parser-to-L2 generation, per-function abstraction options, and the upstream Hoare matrix are unavailable" ["word_abs.c"]
]

def exampleFiles : List SourceFile := referencedFiles exampleTests

theorem example_test_count : exampleTests.length = 26 := by decide
theorem example_file_count : exampleFiles.length = 52 := by decide

end Zag.Test.AutoCorres.Upstream
