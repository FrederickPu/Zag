import Lang.AutoCorres.CParser.CallGraph
import Lang.AutoCorres.CParser.Frontend
import Lang.AutoCorres.CParser.PhasePipeline.Scalar
import Test.AutoCorres.CParser.ScalarSimpl.Plus2Correctness

/-!
# Installed `plus.c` and its generated AutoCorres artifacts

Lean counterpart of the upstream preamble

    external_file "plus.c"
    install_C_file "plus.c"
    autocorres [ts_force nondet = plus2] "plus.c"

Everything here is generated output: the embedded fixture, the analyzed call
schedule that decides which functions are translated, the certified
per-function artifacts, the abstracted callables `plus'` and `plus2'`, the
definitional facts an Isabelle user inspects with `thm`, and the per-function
`ac_corres` theorems. `Test.AutoCorres.Upstream.Plus` is the theory body and
states only the lemmas of `Plus.thy`.
-/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusSource

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Test.AutoCorres.CParser.ScalarSimpl
open Zag.Test.AutoCorres.CParser.ScalarSimpl.FixtureHelpers

set_option maxRecDepth 100000

/-- `external_file "plus.c"`: the upstream fixture, embedded verbatim. -/
def source : String :=
  include_str "../../Fixtures/examples/plus.c"

/-! ## Installed call schedule

`install_C_file` installs the whole translation unit, so the port records which
functions the file actually schedules before any of them is translated. -/

namespace FixtureSchedule

open ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.CallGraph

private def symbolName? (program : Program) (symbolId : Nat) : Option String :=
  (program.symbolById? symbolId).map (·.sourceName)

private def analyzed : Option Program :=
  (Frontend.preprocessAndAnalyze .arm (Scalar.sourceFiles "plus.c" source) "plus.c").program

def namedSCCs : Option (List (List String × Bool)) := do
  let program ← analyzed
  (build program).sccs.mapM fun component => do
    let names ← component.members.mapM (symbolName? program)
    return (names, component.recursive)

def namedEdges : Option (List (String × Option String)) := do
  let program ← analyzed
  (build program).edges.mapM fun edge => do
    let caller ← edge.caller.bind (symbolName? program)
    let callee := edge.callee.bind (symbolName? program)
    return (caller, callee)

/-- The installed file has two independent leaves; only `main` depends on them. -/
theorem plus_and_plus2_are_nonrecursive_sccs :
    namedSCCs.map (fun components =>
      components.contains (["plus"], false) &&
      components.contains (["plus2"], false)) = some true := by
  native_decide

theorem only_main_depends_on_plus_and_plus2 :
    namedEdges.map (fun edges =>
      edges.contains ("main", some "plus") &&
      edges.contains ("main", some "plus2") &&
      edges.all (fun edge => edge.1 = "main")) = some true := by
  native_decide

end FixtureSchedule

/-! ## `plus`: default pure type strengthening -/

private def plusSource : RefinementResult.Success
    (Scalar.certifySSA .arm source "plus.c" "plus") :=
  RefinementResult.success _ (by native_decide)

/-- The certified translation artifact `autocorres` produced for `plus`. -/
@[irreducible] def plusArtifact := plusSource.artifact

theorem plusArtifact_exact :
    Scalar.certifySSA .arm source "plus.c" "plus" = .ok plusArtifact :=
  by
    unfold plusArtifact
    exact plusSource.exact

/-- The generated pure callable, `plus'` of `autocorres "plus.c"`. -/
def plus' (a b : BitVec 32) : BitVec 32 :=
  Scalar.toSSA .arm source "plus.c" "plus" 32
    [Int.ofNat a.toNat, Int.ofNat b.toNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
/-- Upstream `thm plus_body_def`: the installed SIMPL function. -/
theorem plusArtifact_function : plusArtifact.function = plus := by
  native_decide

theorem plusArtifact_command :
    plusArtifact.prepared.certified.function.command = plus.command :=
  congrArg Function.command plusArtifact_function

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
private theorem plusArtifact_expression :
    plusArtifact.prepared.supported.expression =
      .binary u32 u32 .add (.variable u32 1) (.variable u32 2) := by
  native_decide +revert

private theorem plusArtifact_enter (a b : BitVec 32) :
    plusArtifact.function.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] =
      .ok (plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat)) := by
  rw [plusArtifact_function]
  exact plus_enter_eq _ _

private theorem plus'_eq_generated_expression (a b : BitVec 32) :
    plus' a b = BitVec.ofInt 32
      ((plusArtifact.prepared.supported.expression.eval
        (plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat))).getD 0) :=
  Scalar.toSSA_eq_invoke plusArtifact plusArtifact_exact 32
    [Int.ofNat a.toNat, Int.ofNat b.toNat] (plusArtifact_enter a b)

/-- Upstream `thm plus'_def`: the generated body is the recognized `a + b`. -/
theorem plus'_def (a b : BitVec 32) :
    plus' a b = BitVec.ofInt 32
      (((Expr.binary u32 u32 .add (.variable u32 1) (.variable u32 2)).eval
        (plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat))).getD 0) := by
  rw [plus'_eq_generated_expression, plusArtifact_expression]

noncomputable section

/-- Generated SimplConv certificate for `plus`. The source command is the
installed one by `plusArtifact_command`; the certificate is indexed by it, so
the equality cannot be rewritten into this statement. -/
theorem plus_l1_corres :
    L1.L1Corres false emptyEnvironment
      plusArtifact.prepared.translation.simpl.target.denote
      plusArtifact.prepared.certified.function.command :=
  plusArtifact.prepared.translation.simpl.corres

/-- Generated local-variable-extraction certificate consuming that SimplConv target. -/
theorem plus_l2_corres :
    L2.L2Corres id (Scalar.readWord plusArtifact.prepared.supported) (fun _ => ())
      (fun _ => True) plusArtifact.prepared.translation.l2
      plusArtifact.prepared.translation.simpl.target.denote :=
  plusArtifact.prepared.translation.l2Corres

/-- Identity HeapLift certificate: `plus` addresses no C objects. -/
theorem plus_heap_lift_corres :
    HeapLift.L2Tcorres id plusArtifact.prepared.translation.heap.target
      plusArtifact.prepared.translation.l2 :=
  plusArtifact.prepared.translation.heap.corres

/-- Identity WordAbstract certificate: `Plus.thy` requests no word abstraction. -/
theorem plus_word_abstract_corres :
    WordAbstract.corresTA (fun _ : State => True) id id
      plusArtifact.prepared.translation.heap.target
      plusArtifact.prepared.translation.l2 :=
  plusArtifact.prepared.translation.wordCorres

/-- Generated TypeStrengthen equality at the exact WordAbstract endpoint. -/
theorem plus_type_strengthen_exact :
    L2.call (Exception := Unit) plusArtifact.prepared.translation.heap.target =
      plusArtifact.prepared.translation.strengthen.target :=
  plusArtifact.prepared.translation.strengthen.exact

/-- Generated `plus'_ac_corres`, at the installed command. -/
theorem plus'_ac_corres :
    ac_corres id false emptyEnvironment
      (Scalar.readWord plusArtifact.prepared.supported) (fun _ => True)
      plusArtifact.prepared.translation.strengthen.target plus.command := by
  have generated := plusArtifact.prepared.finalCorres
  rwa [plusArtifact_command] at generated

end

/-! ## `plus2`: `ts_force nondet` -/

private def plus2Source : RefinementResult.Success
    (Scalar.certifyNondetSSA .arm source "plus.c" "plus2" 32) :=
  RefinementResult.success _ (by native_decide)

/-- The certified translation artifact `autocorres` produced for `plus2`. -/
@[irreducible] def plus2Artifact := plus2Source.artifact

theorem plus2Artifact_exact :
    Scalar.certifyNondetSSA .arm source "plus.c" "plus2" 32 = .ok plus2Artifact :=
  by
    unfold plus2Artifact
    exact plus2Source.exact

/-- The generated nondeterministic callable, `plus2'` of `ts_force nondet = plus2`. -/
noncomputable def plus2' (a b : BitVec 32) :
    L2.L2Program ScalarSimpl.State Unit (BitVec 32) :=
  Scalar.toNondetSSA .arm source "plus.c" "plus2" 32
    [Int.ofNat a.toNat, Int.ofNat b.toNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
/-- Upstream `thm plus2_body_def`: the installed SIMPL loop. -/
theorem plus2Artifact_function : plus2Artifact.function = plus2 := by
  native_decide

private theorem plus2Artifact_enter (a b : BitVec 32) :
    plus2Artifact.certified.function.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] =
      .ok (plus2Initial a b) := by
  change plus2Artifact.function.enter [Int.ofNat a.toNat, Int.ofNat b.toNat] = _
  rw [plus2Artifact_function]
  exact plus2_enter_eq a b

private theorem plus2Artifact_reenter (a b : BitVec 32) :
    plus2Artifact.certified.function.enter
        [Int.ofNat a.toNat, Int.ofNat b.toNat] (plus2Initial a b) =
      .ok (plus2Initial a b) := by
  change plus2Artifact.function.enter
      [Int.ofNat a.toNat, Int.ofNat b.toNat] (plus2Initial a b) = _
  rw [plus2Artifact_function, plus2_is_resolved_while_body]
  simp [plus2Initial, plus2_is_resolved_while_body, expectedPlus2,
    ScalarSimpl.Function.enter, ScalarSimpl.State.write]
  constructor <;> funext key <;>
    by_cases isTwo : key = 2 <;> by_cases isOne : key = 1 <;>
      simp [isTwo, isOne]

/-- Upstream `thm plus2'_def`: the generated program at a fresh caller state. -/
theorem plus2'_at_empty (a b : BitVec 32) :
    plus2' a b {} = plus2Artifact.translation.target (plus2Initial a b) := by
  rw [plus2', Scalar.toNondetSSA_eq_invoke plus2Artifact plus2Artifact_exact]
  unfold Scalar.SourceTranslation.invoke
  rw [plus2Artifact_enter]

theorem plus2'_at_initial (a b : BitVec 32) :
    plus2' a b (plus2Initial a b) =
      plus2Artifact.translation.target (plus2Initial a b) := by
  rw [plus2', Scalar.toNondetSSA_eq_invoke plus2Artifact plus2Artifact_exact]
  unfold Scalar.SourceTranslation.invoke
  rw [plus2Artifact_reenter]

private theorem plus2Artifact_executes (a b : BitVec 32) :
    Simpl.Exec ScalarSimpl.emptyEnvironment plus2Artifact.function.command
      (.normal (plus2Initial a b)) (.normal (plus2Result a b)) := by
  rw [plus2Artifact_function]
  exact plus2_generated_simpl_executes a b

/-- The source loop's normal execution survives into the generated target. -/
theorem plus2'_result_mem (a b : BitVec 32) :
    (Except.ok (BitVec.ofInt 32 (plus2Result a b).result), plus2Result a b) ∈
      (plus2' a b {}).results := by
  rw [plus2'_at_empty]
  exact Scalar.FunctionTranslation.translatedResultMem
    plus2Artifact.certified 32 (plus2Artifact_executes a b)

theorem plus2'_no_failure (a b : BitVec 32) : ¬(plus2' a b {}).failed := by
  rw [plus2'_at_empty]
  exact Scalar.FunctionTranslation.translatedNoFailure plus2Artifact.certified 32
    (plus2Artifact_executes a b)

/-- Generated `plus2'_ac_corres`, at the installed command. -/
theorem plus2'_ac_corres (a b : BitVec 32) :
    ac_corres id false ScalarSimpl.emptyEnvironment
      (fun state => BitVec.ofInt 32 state.result)
      (fun state => state = plus2Initial a b) (plus2' a b) plus2.command := by
  intro state hypothesis
  rcases hypothesis with ⟨rfl, noFailure⟩
  have generated := plus2Artifact.translation.corres (plus2Initial a b)
    ⟨trivial, by simpa [plus2'_at_initial] using noFailure⟩
  rw [show plus2Artifact.certified.function.command = plus2.command by
    exact congrArg ScalarSimpl.Function.command plus2Artifact_function] at generated
  simpa only [Scalar.FunctionTranslation.readResult, id_eq,
    plus2'_at_initial] using generated

/-- Only the result of `plus2'` is observable: the target is functional. -/
theorem plus2'_unique (a b : BitVec 32) {result : BitVec 32} {post : State}
    (member : ((Except.ok result : Except Unit (BitVec 32)), post) ∈
      (plus2' a b {}).results) :
    ((Except.ok result : Except Unit (BitVec 32)), post) =
      (Except.ok (BitVec.ofInt 32 (plus2Result a b).result), plus2Result a b) := by
  rw [plus2'_at_empty] at member
  exact plus2Artifact.translation.targetFunctional.unique (plus2Initial a b) member
    (Scalar.FunctionTranslation.translatedResultMem plus2Artifact.certified 32
      (plus2Artifact_executes a b))

end Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusSource
