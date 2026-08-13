import Test.AutoCorres.CParser.ScalarSimpl.Max
import Test.AutoCorres.CParser.ScalarSimpl.GcdCoreObstruction
import Test.AutoCorres.CParser.ScalarSimpl.GcdExecution
import Test.AutoCorres.CParser.ScalarSimpl.GcdPipelineFinal

/-!
# Fragment of upstream `Simple`

Sources:

* [`simple.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/simple.c)
* [`Simple.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/examples/Simple.thy)

The fixture frontend, resolved ASTs, finite C/Simpl semantics, Euclidean proof,
and the manually assembled `gcd` five-phase correspondence are exact. The
phase-local `max` checks are deliberately named `manual`: no generated chain
connects them to its fixture endpoint.

The remaining gap is infrastructure rather than a hidden proof: a generated
loop-capable phase chain, total-correctness `wp`, and monad extensionality are
needed before the Isabelle-shaped `gcd_wp` and `monad_to_gets` script exists.
-/

namespace Zag.Test.AutoCorres.Upstream.Simple

set_option linter.defProp false

export Zag.Test.AutoCorres.CParser.ScalarSimpl.MaxManual
  (keeps_condition manual_source_corres chooses_larger_argument)

namespace TypeStrengthen

export Zag.Test.AutoCorres.CParser.ScalarSimpl.MaxManual.TypeStrengthen
  (target_is_max manual_phase_exact)

end TypeStrengthen

namespace Max

open Zag.Test.AutoCorres.CParser.ScalarSimpl

def frontend := max_fixture_certifies
def ast := max_is_resolved_by_symbol_id
def semantics := max_finite_execution_iff
def arbitrary_inputs := max_resolved_executes

end Max

namespace Gcd

open Zag.Test.AutoCorres.CParser.ScalarSimpl

def frontend := gcd_fixture_certifies
def ast := gcd_is_exact_resolved_function
def fixture_shape := gcd_body_has_uninitialized_c_loop_mod_assignments_and_return
def finite_c_simpl_correspondence := gcd_finite_execution_iff
def invariant_initial := gcd_invariant_initial
def invariant_preserved := gcd_invariant_preserved
def variant_decreases := gcd_variant_strictly_decreases
def final_result := gcd_invariant_final
def recursive_result := gcdWord_toNat
def word_abstract_guarded_map := kernel_unsigned_int_guard
def simpl_endpoint := GcdPipeline.fixture_simpl_endpoint
def lve_endpoint := GcdPipeline.lve_consumes_fixture_endpoint
def heap_lift_endpoint := GcdPipeline.heapLiftCorres
def word_abstract_endpoint := GcdPipeline.word_consumes_heap_endpoint
def type_strengthen_endpoint := GcdPipeline.type_strengthen_consumes_word_endpoint
noncomputable def generated_chain := GcdPipeline.finalChain
def generated_correspondence := GcdPipeline.finalAcCorres
def generated_exact := GcdPipeline.final_target_exact
def generated_pure_return := GcdPipeline.final_target_pure_return
def generated_no_failure := GcdPipeline.final_target_no_failure
def generated_correct := GcdPipeline.final_target_returns_only_gcd
def generated_valid := GcdPipeline.final_target_valid

end Gcd

end Zag.Test.AutoCorres.Upstream.Simple
