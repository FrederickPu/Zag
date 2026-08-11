import Lang.AutoCorres.CParser.Preprocessor

/-!
# Embedded StrictC fixture corpus

Every vendored C source and header is embedded at elaboration time. The
preprocessor and smoke runners therefore use the same virtual file map without
runtime filesystem access.
-/

namespace Zag.Test.AutoCorres.CParser.EmbeddedFixtures

open Zag.Lang.AutoCorres.CParser

inductive Kind where
  | cEntry
  | header
deriving DecidableEq

structure Fixture where
  name : String
  source : String
  kind : Kind

def fixtures : List Fixture := [
  { name := "examples/alloc.c", source := include_str "../Fixtures/examples/alloc.c",
    kind := .cEntry },
  { name := "examples/alloc.h", source := include_str "../Fixtures/examples/alloc.h",
    kind := .header },
  { name := "examples/binary_search.c",
    source := include_str "../Fixtures/examples/binary_search.c", kind := .cEntry },
  { name := "examples/condition_guard.c",
    source := include_str "../Fixtures/examples/condition_guard.c", kind := .cEntry },
  { name := "examples/factorial.c", source := include_str "../Fixtures/examples/factorial.c",
    kind := .cEntry },
  { name := "examples/fib.c", source := include_str "../Fixtures/examples/fib.c",
    kind := .cEntry },
  { name := "examples/function_info.c",
    source := include_str "../Fixtures/examples/function_info.c", kind := .cEntry },
  { name := "examples/heap_wrap.c", source := include_str "../Fixtures/examples/heap_wrap.c",
    kind := .cEntry },
  { name := "examples/is_prime.c", source := include_str "../Fixtures/examples/is_prime.c",
    kind := .cEntry },
  { name := "examples/kmalloc.c", source := include_str "../Fixtures/examples/kmalloc.c",
    kind := .cEntry },
  { name := "examples/list_rev.c", source := include_str "../Fixtures/examples/list_rev.c",
    kind := .cEntry },
  { name := "examples/list.c", source := include_str "../Fixtures/examples/list.c",
    kind := .cEntry },
  { name := "examples/memcpy.c", source := include_str "../Fixtures/examples/memcpy.c",
    kind := .cEntry },
  { name := "examples/memset.c", source := include_str "../Fixtures/examples/memset.c",
    kind := .cEntry },
  { name := "examples/mult_by_add.c",
    source := include_str "../Fixtures/examples/mult_by_add.c", kind := .cEntry },
  { name := "examples/plus.c", source := include_str "../Fixtures/examples/plus.c",
    kind := .cEntry },
  { name := "examples/quicksort.c", source := include_str "../Fixtures/examples/quicksort.c",
    kind := .cEntry },
  { name := "examples/rename.c", source := include_str "../Fixtures/examples/rename.c",
    kind := .cEntry },
  { name := "examples/schorr_waite.c",
    source := include_str "../Fixtures/examples/schorr_waite.c", kind := .cEntry },
  { name := "examples/simple.c", source := include_str "../Fixtures/examples/simple.c",
    kind := .cEntry },
  { name := "examples/str2long.c", source := include_str "../Fixtures/examples/str2long.c",
    kind := .cEntry },
  { name := "examples/suzuki.c", source := include_str "../Fixtures/examples/suzuki.c",
    kind := .cEntry },
  { name := "examples/swap.c", source := include_str "../Fixtures/examples/swap.c",
    kind := .cEntry },
  { name := "examples/trace_demo.c",
    source := include_str "../Fixtures/examples/trace_demo.c", kind := .cEntry },
  { name := "examples/type_strengthen.c",
    source := include_str "../Fixtures/examples/type_strengthen.c", kind := .cEntry },
  { name := "examples/word_abs.c", source := include_str "../Fixtures/examples/word_abs.c",
    kind := .cEntry },
  { name := "parse-tests/basic_recursion.c",
    source := include_str "../Fixtures/parse-tests/basic_recursion.c", kind := .cEntry },
  { name := "parse-tests/basic.c", source := include_str "../Fixtures/parse-tests/basic.c",
    kind := .cEntry },
  { name := "parse-tests/big_bit_ops.c",
    source := include_str "../Fixtures/parse-tests/big_bit_ops.c", kind := .cEntry },
  { name := "parse-tests/bodyless_function.c",
    source := include_str "../Fixtures/parse-tests/bodyless_function.c", kind := .cEntry },
  { name := "parse-tests/heap_infer.c",
    source := include_str "../Fixtures/parse-tests/heap_infer.c", kind := .cEntry },
  { name := "parse-tests/heap_lift_array.c",
    source := include_str "../Fixtures/parse-tests/heap_lift_array.c", kind := .cEntry },
  { name := "parse-tests/l2_opt_invariant.c",
    source := include_str "../Fixtures/parse-tests/l2_opt_invariant.c", kind := .cEntry },
  { name := "parse-tests/loop_test.c",
    source := include_str "../Fixtures/parse-tests/loop_test.c", kind := .cEntry },
  { name := "parse-tests/loop_test2.c",
    source := include_str "../Fixtures/parse-tests/loop_test2.c", kind := .cEntry },
  { name := "parse-tests/mutual_recursion.c",
    source := include_str "../Fixtures/parse-tests/mutual_recursion.c", kind := .cEntry },
  { name := "parse-tests/mutual_recursion2.c",
    source := include_str "../Fixtures/parse-tests/mutual_recursion2.c", kind := .cEntry },
  { name := "parse-tests/nested_break_cont.c",
    source := include_str "../Fixtures/parse-tests/nested_break_cont.c", kind := .cEntry },
  { name := "parse-tests/read_global_array.c",
    source := include_str "../Fixtures/parse-tests/read_global_array.c", kind := .cEntry },
  { name := "parse-tests/signed_ptr_ptr.c",
    source := include_str "../Fixtures/parse-tests/signed_ptr_ptr.c", kind := .cEntry },
  { name := "parse-tests/struct_init.c",
    source := include_str "../Fixtures/parse-tests/struct_init.c", kind := .cEntry },
  { name := "parse-tests/struct1.c",
    source := include_str "../Fixtures/parse-tests/struct1.c", kind := .cEntry },
  { name := "parse-tests/unliftable_call.c",
    source := include_str "../Fixtures/parse-tests/unliftable_call.c", kind := .cEntry },
  { name := "parse-tests/voidptrptr.c",
    source := include_str "../Fixtures/parse-tests/voidptrptr.c", kind := .cEntry },
  { name := "parse-tests/while_loop_no_vars.c",
    source := include_str "../Fixtures/parse-tests/while_loop_no_vars.c", kind := .cEntry },
  { name := "parse-tests/word_abs_exn.c",
    source := include_str "../Fixtures/parse-tests/word_abs_exn.c", kind := .cEntry },
  { name := "parse-tests/write_to_global_array.c",
    source := include_str "../Fixtures/parse-tests/write_to_global_array.c", kind := .cEntry },
  { name := "proof-tests/array_indirect_update.c",
    source := include_str "../Fixtures/proof-tests/array_indirect_update.c", kind := .cEntry },
  { name := "proof-tests/badnames.c",
    source := include_str "../Fixtures/proof-tests/badnames.c", kind := .cEntry },
  { name := "proof-tests/custom_word_abs.c",
    source := include_str "../Fixtures/proof-tests/custom_word_abs.c", kind := .cEntry },
  { name := "proof-tests/global_array_update.c",
    source := include_str "../Fixtures/proof-tests/global_array_update.c", kind := .cEntry },
  { name := "proof-tests/heap_lift_force_prevent.c",
    source := include_str "../Fixtures/proof-tests/heap_lift_force_prevent.c", kind := .cEntry },
  { name := "proof-tests/nested_struct.c",
    source := include_str "../Fixtures/proof-tests/nested_struct.c", kind := .cEntry },
  { name := "proof-tests/prototyped_functions.c",
    source := include_str "../Fixtures/proof-tests/prototyped_functions.c", kind := .cEntry },
  { name := "proof-tests/signed_word_abs_heap.c",
    source := include_str "../Fixtures/proof-tests/signed_word_abs_heap.c", kind := .cEntry },
  { name := "proof-tests/skip_heap_abs.c",
    source := include_str "../Fixtures/proof-tests/skip_heap_abs.c", kind := .cEntry },
  { name := "proof-tests/struct.c", source := include_str "../Fixtures/proof-tests/struct.c",
    kind := .cEntry },
  { name := "proof-tests/struct2.c", source := include_str "../Fixtures/proof-tests/struct2.c",
    kind := .cEntry },
  { name := "proof-tests/test_spec_translation.c",
    source := include_str "../Fixtures/proof-tests/test_spec_translation.c", kind := .cEntry },
  { name := "proof-tests/while_loop_vars_preserved.c",
    source := include_str "../Fixtures/proof-tests/while_loop_vars_preserved.c", kind := .cEntry },
  { name := "proof-tests/word_abs_cases.c",
    source := include_str "../Fixtures/proof-tests/word_abs_cases.c", kind := .cEntry },
  { name := "proof-tests/word_abs_fn_call.c",
    source := include_str "../Fixtures/proof-tests/word_abs_fn_call.c", kind := .cEntry },
  { name := "proof-tests/word_abs_options.c",
    source := include_str "../Fixtures/proof-tests/word_abs_options.c", kind := .cEntry },
  { name := "doc/quickstart/minmax.c",
    source := include_str "../Fixtures/doc/quickstart/minmax.c", kind := .cEntry },
  { name := "doc/quickstart/mult_by_add.c",
    source := include_str "../Fixtures/doc/quickstart/mult_by_add.c", kind := .cEntry },
  { name := "doc/quickstart/swap.c",
    source := include_str "../Fixtures/doc/quickstart/swap.c", kind := .cEntry },
  { name := "failing/dirty_frees.c",
    source := include_str "../Fixtures/failing/dirty_frees.c", kind := .cEntry },
  { name := "failing/jira_ver_591.c",
    source := include_str "../Fixtures/failing/jira_ver_591.c", kind := .cEntry }
]

def files : Preprocessor.FileMap :=
  fixtures.map fun fixture => { name := fixture.name, source := fixture.source }

def entries : List String :=
  fixtures.filterMap fun fixture =>
    if fixture.kind = .cEntry then some fixture.name else none

theorem file_count : files.length = 68 := by
  native_decide

theorem entry_count : entries.length = 67 := by
  native_decide

theorem virtual_names_are_unique :
    (fixtures.map Fixture.name).Nodup := by
  native_decide

theorem alloc_header_is_present :
    fixtures.any (fun fixture =>
      fixture.name == "examples/alloc.h" && fixture.kind == .header) = true := by
  native_decide

end Zag.Test.AutoCorres.CParser.EmbeddedFixtures
