import Test.AutoCorres.CParser.ScalarSimpl.PlusSource
import Test.AutoCorres.CParser.ScalarSimpl.Plus2Termination

/-!
# Complete `Plus` upstream port

Sources:

* [`plus.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/plus.c)
* [`Plus.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/Plus.thy)

`Test.AutoCorres.CParser.ScalarSimpl.PlusSource` stands in for the upstream
preamble `install_C_file "plus.c"` and `autocorres [ts_force nondet = plus2]
"plus.c"`: it embeds the fixture, records the installed call schedule, and
generates `plus'`, `plus2'`, the definitions an Isabelle user inspects with
`thm`, and both `ac_corres` theorems. This file is the `context plus` body and
holds only the lemmas of `Plus.thy`. The upstream total-correctness triple for
the nondeterministic `plus2'` is spelled out as its two obligations,
no-failure and result correctness, and recombined in `plus2_valid`.

The theory never names `main'`, inspects its definition, or uses it in a
lemma, and the exported schedule theorems record that `plus` and `plus2` are
independent non-recursive leaves that only `main` depends on. `main(int, char
**)` is therefore not translated: its pointer-bearing ABI is outside the
certified scalar slice, and replacing it with `main(void)` would not be a
faithful translation.
-/

namespace Zag.Test.AutoCorres.Upstream.Plus

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers
open Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusSource

/-! ## Installed file and generated declarations -/

export Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusSource
  (source plus' plus2'
   plusArtifact_function plus'_def plus'_ac_corres
   plus_l1_corres plus_l2_corres plus_heap_lift_corres
   plus_word_abstract_corres plus_type_strengthen_exact
   plus2Artifact_function plus2'_at_empty plus2'_ac_corres)

export Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusSource.FixtureSchedule
  (plus_and_plus2_are_nonrecursive_sccs only_main_depends_on_plus_and_plus2)

/-! ## `Plus.thy` -/

/-- `3 + 2` should be `5`, read off the generated definition by evaluation. -/
theorem plus_three_plus_two : plus' 3 2 = 5 := by native_decide

/-- `plus` does what it says on the box. -/
theorem plus_correct (a b : BitVec 32) : plus' a b = a + b := by
  rw [plus'_def, plus_add_expression_eval]
  change BitVec.ofInt 32
      (u32.cast (u32.cast (Int.ofNat a.toNat) + u32.cast (Int.ofNat b.toNat))) = a + b
  rw [bitvec_of_u32_cast, BitVec.ofInt_add,
    bitvec_of_u32_cast, bitvec_of_u32_cast,
    Int.ofNat_eq_natCast, Int.ofNat_eq_natCast,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  simp

/-- Result obligation of upstream's total triple for the generated loop. -/
theorem plus2_correct (a b : BitVec 32) :
    ∀ result post, (Except.ok result, post) ∈ (plus2' a b {}).results →
      result = a + b := by
  intro result post member
  have resultEq := congrArg (fun outcome => outcome.1) (plus2'_unique a b member)
  change Except.ok result = Except.ok (BitVec.ofInt 32 (plus2Result a b).result) at resultEq
  rw [Except.ok.inj resultEq, plus2_success_is_wrapping_add]

/-- No-failure obligation of the same triple: the generated loop terminates. -/
theorem plus2_no_failure (a b : BitVec 32) : ¬(plus2' a b {}).failed :=
  plus2'_no_failure a b

/-- Upstream `plus2_correct`, the total triple, as its two obligations. -/
theorem plus2_valid (a b : BitVec 32) :
    ¬(plus2' a b {}).failed ∧
      ∀ result post, (Except.ok result, post) ∈ (plus2' a b {}).results →
        result = a + b :=
  ⟨plus2_no_failure a b, plus2_correct a b⟩

/-- `plus2` is really `plus`. -/
theorem plus2_is_plus (a b : BitVec 32) :
    ∀ result post, (Except.ok result, post) ∈ (plus2' a b {}).results →
      result = plus' a b := by
  intro result post member
  rw [plus2_correct a b result post member, plus_correct]

/-- The source loop's own execution is retained in the generated results. -/
theorem plus2_generated_member (a b : BitVec 32) :
    (Except.ok (BitVec.ofInt 32 (plus2Result a b).result), plus2Result a b) ∈
      (plus2' a b {}).results :=
  plus2'_result_mem a b

/-! ## Correctness of the installed SIMPL programs

`ac_corres` only relates the generated target to `plus.command` and
`plus2.command`; it says nothing on its own about what those commands compute.
These are the statements about the installed SIMPL semantics, and below them
the raw-C fixture semantics they were certified against. -/

/-- Every SIMPL execution of the installed `plus` body returns `a + b`. -/
theorem plus_simpl_correct (a b : BitVec 32) (post : State)
    (execution : Simpl.Exec emptyEnvironment plus.command
      (.normal (plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat)))
      (.normal post)) :
    BitVec.ofInt 32 post.result = a + b := by
  have resolved := plus.command_complete execution
  have equality := resolved.deterministic
    (plus_resolved_executes (Int.ofNat a.toNat) (Int.ofNat b.toNat))
  have postEq : post = plusResult (Int.ofNat a.toNat) (Int.ofNat b.toNat) := by
    simpa using equality
  rw [postEq]
  exact (Zag.Test.AutoCorres.CParser.ScalarSimpl.plus2_is_plus a b).symm.trans
    (plus2_success_is_wrapping_add a b)

/-- Every SIMPL execution of the installed `plus2` loop returns `a + b`. -/
theorem plus2_simpl_correct (a b : BitVec 32) (post : State)
    (execution : Simpl.Exec emptyEnvironment plus2.command
      (.normal (plus2Initial a b)) (.normal post)) :
    BitVec.ofInt 32 post.result = a + b := by
  have resolved := plus2.command_complete execution
  have equality := resolved.deterministic (plus2_resolved_executes a b)
  have postEq : post = plus2Result a b := by simpa using equality
  rw [postEq]
  exact plus2_success_is_wrapping_add a b

export Zag.Test.AutoCorres.CParser.ScalarSimpl
  (plus_fixture_certifies plus2_fixture_certifies
   plus2_body_is_actual_loop
   plus_finite_execution_iff plus2_finite_execution_iff
   plus2_any_success_is_wrapping_add plus2_total_no_failure)

end Zag.Test.AutoCorres.Upstream.Plus
