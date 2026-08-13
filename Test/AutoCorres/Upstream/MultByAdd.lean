import Test.AutoCorres.CParser.ScalarSimpl.MultByAdd

/-!
# `MultByAdd` upstream port

Sources:

* [`mult_by_add.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/mult_by_add.c)
* [`MultByAdd.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/MultByAdd.thy)

Like the Isabelle theory, this port consists of fixture installation and
translation, one invariant-and-measure total-correctness proof, and one SIMPL
partial-correctness proof. The exact fixture and every generated phase remain
visible through the exports below.
-/

namespace Zag.Test.AutoCorres.Upstream.MultByAdd

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline
open FixtureHelpers

namespace SimplConv

theorem manual_source_corres :
    L1.L1Corres false emptyEnvironment generatedL1.denote multByAdd.command :=
  fixtureSimplCertificate.corres

end SimplConv

namespace LocalVarExtract

theorem manual_source_extracts (locals : MultByAddPipeline.Locals) :
    L2.L2Corres MultByAddPipeline.model.projectGlobals
      MultByAddPipeline.model.projectLocals MultByAddPipeline.model.projectLocals
      (fun state => MultByAddPipeline.model.projectLocals state = locals)
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        MultByAddPipeline.lveCertificate.target locals)
      generatedL1.denote :=
  MultByAddPipeline.lve_consumes_fixture_endpoint locals

end LocalVarExtract

namespace TypeStrengthen

theorem manual_phase_exact :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => (readResult (model.projectGlobals state)).toNat)
      (fun state => model.projectLocals state = false)
      finalTarget multByAdd.command :=
  finalAcCorres

end TypeStrengthen

abbrev installed := multByAddCertified
noncomputable abbrev translated := finalTarget

/-- Upstream total correctness, with its loop invariant and natural-number measure. -/
theorem total_correctness_with_invariant_and_measure (a b : MultByAddWord32) :
    multByAddInvariant a b a 0 ∧
      (∀ (remaining : Nat) (result : Int), remaining + 1 < 2 ^ 32 →
        multByAddInvariant a b (BitVec.ofNat 32 (remaining + 1))
            (BitVec.ofInt 32 result) →
          multByAddInvariant a b (BitVec.ofNat 32 remaining)
              (BitVec.ofInt 32 (u32.cast (result + Int.ofNat b.toNat))) ∧
            multByAddVariant (BitVec.ofNat 32 remaining) <
              multByAddVariant (BitVec.ofNat 32 (remaining + 1))) ∧
      ¬(translated (initialGlobals a b)).failed ∧
      ∀ result post,
        (Except.ok result, post) ∈ (translated (initialGlobals a b)).results →
          result = (a * b).toNat := by
  refine ⟨mult_by_add_invariant_initial a b, ?_,
    final_target_no_failure a b, mult_by_add_correct a b⟩
  intro remaining result bound invariant
  exact ⟨mult_by_add_invariant_preserved a b remaining result invariant,
    mult_by_add_variant_decreases remaining bound⟩

/-- Upstream's SIMPL partial-correctness statement at the exact generated command. -/
theorem simpl_partial_correctness (a b : MultByAddWord32) (post : State)
    (execution : Simpl.Exec emptyEnvironment multByAdd.command
      (.normal (multByAddInitial a b)) (.normal post)) :
    BitVec.ofInt 32 post.result = a * b :=
  mult_by_add_simpl_partial_correctness a b post execution

export Zag.Test.AutoCorres.CParser.ScalarSimpl
  (mult_by_add_fixture_certifies
   mult_by_add_body_is_actual_initialized_loop
   mult_by_add_loop_body_has_actual_post_decrement
   mult_by_add_finite_execution_iff
   mult_by_add_invariant_initial
   mult_by_add_invariant_preserved
   mult_by_add_variant_decreases
   mult_by_add_simpl_partial_correctness
   mult_by_add_total_no_failure)

export Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline
  (fixture_simpl_endpoint
   lve_consumes_fixture_endpoint
   heapLiftCorres
   word_consumes_heap_endpoint
   type_strengthen_consumes_word_endpoint
   finalAcCorres
   final_target_no_failure
   mult_by_add_correct
   mult_by_add_end_to_end)

end Zag.Test.AutoCorres.Upstream.MultByAdd
