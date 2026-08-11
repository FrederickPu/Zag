import Test.AutoCorres.Upstream.MultByAdd

/-!
# `Chapter2_HoareHeap` quickstart port

Sources:

* [`mult_by_add.c`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/doc/quickstart/mult_by_add.c)
* [`Chapter2_HoareHeap.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/doc/quickstart/Chapter2_HoareHeap.thy)

The quickstart fixture is certified at its own virtual path. Its independently
resolved function is then proved to be the exact function consumed by the
completed `MultByAdd` phase pipeline.
-/

namespace Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser
open Zag.Test.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline
open FixtureHelpers

def fixturePath : String := "doc/quickstart/mult_by_add.c"

def vendoredFixtureSource : String :=
  include_str "../Fixtures/doc/quickstart/mult_by_add.c"

private def examplesFixtureSource : String :=
  include_str "../Fixtures/examples/mult_by_add.c"

theorem fixture_file_map_entry_is_exact :
    EmbeddedFixtures.files.find? (fun file => file.name == fixturePath) =
      some { name := fixturePath, source := vendoredFixtureSource } := by
  native_decide

theorem fixture_source_is_not_examples_source :
    vendoredFixtureSource ≠ examplesFixtureSource := by
  native_decide

opaque certifiedResult :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error
      (Certified .arm EmbeddedFixtures.files fixturePath "mult_by_add") :=
  certifyFrontend .arm EmbeddedFixtures.files fixturePath "mult_by_add"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem fixture_certifies : certifiedResult.isOk := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def certified : Certified .arm EmbeddedFixtures.files fixturePath "mult_by_add" :=
  certifiedResult.toOption.get
    (except_toOption_isSome_of_isOk certifiedResult fixture_certifies)

def function : Function := certified.function

def certificate : Certificate .arm EmbeddedFixtures.files fixturePath
    "mult_by_add" function := certified.certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem function_is_mult_by_add_pipeline : function = multByAdd := by
  native_decide

theorem body_is_exact_pipeline_shape :
    function.body =
      .seq (.declare 3 u32 (some (.literal s32 0)))
        (.seq multByAddLoop (.seq (.return u32 (.variable u32 3)) .skip)) := by
  rw [function_is_mult_by_add_pipeline]
  exact mult_by_add_body_is_actual_initialized_loop

theorem command_is_mult_by_add_pipeline : function.command = multByAdd.command := by
  rw [function_is_mult_by_add_pipeline]

theorem invariant_initial (a b : MultByAddWord32) :
    multByAddInvariant a b a 0 :=
  mult_by_add_invariant_initial a b

theorem invariant_preserved (a b : MultByAddWord32) (remaining : Nat)
    (result : Int)
    (invariant : multByAddInvariant a b (BitVec.ofNat 32 (remaining + 1))
      (BitVec.ofInt 32 result)) :
    multByAddInvariant a b (BitVec.ofNat 32 remaining)
      (BitVec.ofInt 32 (u32.cast (result + Int.ofNat b.toNat))) :=
  mult_by_add_invariant_preserved a b remaining result invariant

theorem variant_decreases (remaining : Nat) (bound : remaining + 1 < 2 ^ 32) :
    multByAddVariant (BitVec.ofNat 32 remaining) <
      multByAddVariant (BitVec.ofNat 32 (remaining + 1)) :=
  mult_by_add_variant_decreases remaining bound

theorem raw_fixture_executes (a b : MultByAddWord32) :
    Raw.FunctionExec certificate.program "mult_by_add" certificate.functionInfo
      certificate.rawBody function.returnType (multByAddInitial a b)
      (.success (multByAddResult a b)) := by
  apply (certificate.finite_iff (multByAddInitial a b)
    (.success (multByAddResult a b))).2
  rw [command_is_mult_by_add_pipeline]
  exact mult_by_add_generated_simpl_executes a b

theorem raw_fixture_no_failure (a b : MultByAddWord32) :
    ¬Raw.FunctionExec certificate.program "mult_by_add" certificate.functionInfo
      certificate.rawBody function.returnType (multByAddInitial a b)
      .undefinedBehavior := by
  intro failed
  have resolvedFailure := certificate.resolution.rawToResolved
    (multByAddInitial a b) .undefinedBehavior failed
  have successful : function.Exec (multByAddInitial a b)
      (.normal (multByAddResult a b)) := by
    rw [function_is_mult_by_add_pipeline]
    exact mult_by_add_resolved_executes a b
  have equality := function_exec_deterministic function successful resolvedFailure
  cases equality

theorem raw_fixture_total_no_failure (a b : MultByAddWord32) :
    Raw.FunctionExec certificate.program "mult_by_add" certificate.functionInfo
        certificate.rawBody function.returnType (multByAddInitial a b)
        (.success (multByAddResult a b)) ∧
      ¬Raw.FunctionExec certificate.program "mult_by_add" certificate.functionInfo
        certificate.rawBody function.returnType (multByAddInitial a b)
        .undefinedBehavior :=
  ⟨raw_fixture_executes a b, raw_fixture_no_failure a b⟩

theorem final_correspondence_uses_quickstart_function :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => (readResult (model.projectGlobals state)).toNat)
      (fun state => model.projectLocals state = false)
      finalTarget function.command := by
  rw [command_is_mult_by_add_pipeline]
  exact finalAcCorres

noncomputable def multByAdd' (a b : MultByAddWord32) :
    L2.L2Program Globals Unit Nat :=
  fun _ => finalTarget (initialGlobals a b)

def ValidNF (precondition : Globals → Prop)
    (program : L2.L2Program Globals Unit Nat)
    (postcondition : Nat → Globals → Prop) : Prop :=
  ∀ state, precondition state →
    ¬(program state).failed ∧
      ∀ result post, (Except.ok result, post) ∈ (program state).results →
        postcondition result post

theorem final_total_correctness (a b : MultByAddWord32) :
    ∀ state, True →
      ∀ result post, (Except.ok result, post) ∈ (multByAdd' a b state).results →
        result = (a * b).toNat := by
  intro _ _ result post execution
  exact Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline.mult_by_add_correct
    a b result post execution

theorem final_no_failure (a b : MultByAddWord32) :
    ∀ state, True → ¬(multByAdd' a b state).failed := by
  intro _ _
  exact final_target_no_failure a b

/-- The chapter's `λs. True` total Hoare and no-failure objective. -/
theorem mult_by_add_correct (a b : MultByAddWord32) :
    ValidNF (fun _ => True) (multByAdd' a b)
      (fun result _ => result = (a * b).toNat) := by
  intro state precondition
  exact ⟨final_no_failure a b state precondition,
    final_total_correctness a b state precondition⟩

end Zag.Test.AutoCorres.Upstream.Chapter2_HoareHeap
