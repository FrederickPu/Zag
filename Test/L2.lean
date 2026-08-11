import Lang.AutoCorres.ML.autocorres

/-!
# Certified L1 to L2 local-variable extraction

These tests exercise the current proof-producing all-locals extraction kernel.
L1 carries `Full` as monadic state. L2 receives `Locals` as an explicit value
and carries only `Globals` as monadic state.
-/

namespace Zag.Test.L2

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.ML.LocalVarExtract

structure Locals where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

structure Globals where
  heap : List Nat
  counter : Nat
  deriving DecidableEq, Repr

structure Full where
  locals : Locals
  globals : Globals
  deriving DecidableEq, Repr

def stateModel : StateModel Full Locals Globals where
  projectGlobals := Full.globals
  projectLocals := Full.locals
  assemble := fun locals globals => ⟨locals, globals⟩
  projectGlobals_assemble := fun _ _ => rfl
  projectLocals_assemble := fun _ _ => rfl
  assemble_project := fun _ => rfl

/-! ## Universe-polymorphic standalone extraction -/

universe u v

def higherUniverseModel : StateModel (Type u × Type v) (Type u) (Type v) where
  projectGlobals := Prod.snd
  projectLocals := Prod.fst
  assemble := fun locals globals => (locals, globals)
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; cases state; rfl

def higherUniverseUpdate (locals : Type u) (_globals : Type v) : Type u :=
  List locals

def higherUniverseSource : Source.Syntax (Type u × Type v) (Type u) (Type v) :=
  .seq (.modify (Source.localTransform higherUniverseModel higherUniverseUpdate))
    .skip

def higherUniverseSupported : Supported higherUniverseModel higherUniverseSource :=
  .seq (.localUpdate higherUniverseUpdate) .skip

theorem higher_universe_extraction_is_accepted :
    (extract higherUniverseModel higherUniverseSupported).target =
      Target.Syntax.seq (.localUpdate higherUniverseUpdate) .skip := by
  rfl

theorem higher_universe_extraction_updates_and_sequences
    (locals : Type u) (globals : Type v) :
    (Except.ok (List locals), globals) ∈
      ((extract higherUniverseModel higherUniverseSupported).target.denote
        locals globals).results := by
  simp [higherUniverseSupported, higherUniverseSource, extract,
    Target.Syntax.denote, higherUniverseUpdate, L2.seq, L2.gets]

def initialLocals : Locals := ⟨2, 3⟩
def initialGlobals : Globals := ⟨[7, 8], 5⟩
def initialFull : Full := ⟨initialLocals, initialGlobals⟩

def updateX (locals : Locals) (globals : Globals) : Locals :=
  { locals with x := locals.x + locals.y + globals.counter }

def updateGlobals (locals : Locals) (globals : Globals) : Globals :=
  { heap := locals.x :: globals.heap
    counter := globals.counter + locals.y }

def chooseLocal (locals : Locals) (globals : Globals) : Prop :=
  locals.x < globals.counter

def updatedLocals : Locals := ⟨10, 3⟩
def updatedGlobals : Globals := ⟨[2, 7, 8], 8⟩
def updatedGlobalsAfterLocal : Globals := ⟨[10, 7, 8], 8⟩

/-! ## Explicit locals and monadic globals -/

noncomputable def targetSkip : Locals -> L2.L2Program Globals Locals Locals :=
  Target.Syntax.denote .skip

noncomputable def sourceSkip : L1.L1Program Full :=
  Source.Syntax.denote (Locals := Locals) (Globals := Globals) .skip

theorem skip_preserves_locals_and_globals :
    (Except.ok initialLocals, initialGlobals) ∈
      (targetSkip initialLocals initialGlobals).results := by
  simp [targetSkip, Target.Syntax.denote, L2.gets]

theorem local_update_changes_only_locals :
    (Except.ok updatedLocals, initialGlobals) ∈
      (Target.Syntax.denote (Target.Syntax.localUpdate updateX)
        initialLocals initialGlobals).results := by
  simp [Target.Syntax.denote, L2.gets, updateX, initialLocals, initialGlobals,
    updatedLocals]

theorem source_local_update_preserves_globals :
    stateModel.projectGlobals
        (Source.localTransform stateModel updateX initialFull) = initialGlobals := by
  rfl

theorem global_update_preserves_locals_and_changes_globals :
    (Except.ok initialLocals, updatedGlobals) ∈
      (Target.Syntax.denote (Target.Syntax.globalUpdate updateGlobals)
        initialLocals initialGlobals).results := by
  simp [Target.Syntax.denote, L2.seq, L2.modify, L2.gets, updateGlobals,
    initialLocals, initialGlobals, updatedGlobals]

/-! ## Sequence, condition, and catch -/

def sequenceSource : Source.Syntax Full Locals Globals :=
  .seq (.modify (Source.localTransform stateModel updateX))
    (.modify (Source.globalTransform stateModel updateGlobals))

def sequenceSupported : Supported stateModel sequenceSource :=
  .seq (.localUpdate updateX) (.globalUpdate updateGlobals)

def sequenceCertificate := extract stateModel sequenceSupported
def sequenceCanonicalCertificate :=
  ML.LocalVarExtract.extractCanonical stateModel sequenceSupported

theorem sequence_target_shape :
    sequenceCertificate.target =
      Target.Syntax.seq (.localUpdate updateX) (.globalUpdate updateGlobals) :=
  rfl

theorem sequence_generic_and_canonical_targets_agree :
    sequenceCanonicalCertificate.target =
      ML.LocalVarExtract.CanonicalTarget.Syntax.ofGeneric
        sequenceCertificate.target := by
  rfl

theorem sequence_generic_and_canonical_denotations_agree (locals : Locals) :
    ML.LocalVarExtract.CanonicalTarget.Syntax.denote
        sequenceCanonicalCertificate.target locals =
      Target.Syntax.denote sequenceCertificate.target locals := by
  rw [sequence_generic_and_canonical_targets_agree]
  exact LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote_ofGeneric _ _

theorem sequence_threads_updated_locals :
    (Except.ok updatedLocals, updatedGlobalsAfterLocal) ∈
      (Target.Syntax.denote sequenceCertificate.target
        initialLocals initialGlobals).results := by
  simp [sequenceCertificate, sequenceSupported, sequenceSource, extract,
    Target.Syntax.denote, L2.seq, L2.modify, L2.gets, updateX, updateGlobals,
    initialLocals, initialGlobals, updatedLocals, updatedGlobalsAfterLocal]
  exact ⟨updatedLocals, initialGlobals, ⟨rfl, rfl⟩, rfl,
    ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-! ## Direct SIMPL to L2 pipeline -/

def pipelineEnv : Simpl.Body Full Unit Unit := fun _ => none

def pipelineSource : Simpl.Com Full Unit Unit :=
  .Seq (.Basic (Source.localTransform stateModel updateX))
    (.Cond
      (fun state => chooseLocal (stateModel.projectLocals state)
        (stateModel.projectGlobals state))
      .Skip
      (.Basic (Source.globalTransform stateModel updateGlobals)))

def pipelineSimplSupported :
    Zag.Lang.AutoCorres.SimplConv.Kernel.Supported pipelineSource :=
  .seq (.basic (Source.localTransform stateModel updateX))
    (.cond
      (fun state => chooseLocal (stateModel.projectLocals state)
        (stateModel.projectGlobals state))
      .skip (.basic (Source.globalTransform stateModel updateGlobals)))

def pipelineLveSupported :
    Zag.Lang.AutoCorres.LocalVarExtract.Kernel.Supported stateModel
      (ML.SimplConv.simplConv false pipelineEnv pipelineSimplSupported).target :=
  .seq (.localUpdate updateX)
    (.condition chooseLocal .skip (.globalUpdate updateGlobals))

def pipelineSupported :
    ML.AutoCorres.L1Supported false pipelineEnv pipelineSource stateModel where
  simplConv := pipelineSimplSupported
  localVarExtract := pipelineLveSupported

def pipelineTranslation :=
  ML.AutoCorres.translateL1Supported false pipelineEnv pipelineSource stateModel
    pipelineSupported

theorem pipeline_l1_target_shape :
    pipelineTranslation.l1.target =
      .seq (.modify (Source.localTransform stateModel updateX))
        (.condition
          (fun state => chooseLocal (stateModel.projectLocals state)
            (stateModel.projectGlobals state))
          .skip (.modify (Source.globalTransform stateModel updateGlobals))) := by
  rfl

theorem pipeline_l2_target_shape :
    pipelineTranslation.l2.target =
      Target.Syntax.seq (.localUpdate updateX)
        (.condition chooseLocal .skip (.globalUpdate updateGlobals)) := by
  rfl

theorem pipeline_certificates_share_l1 :
    Extracts stateModel pipelineTranslation.l2.target
      pipelineTranslation.l1.target :=
  pipelineTranslation.l2.corres

theorem pipeline_threads_local_and_global_updates :
    (Except.ok updatedLocals, updatedGlobalsAfterLocal) ∈
      (Target.Syntax.denote pipelineTranslation.l2.target
        initialLocals initialGlobals).results := by
  rw [pipeline_l2_target_shape]
  simp only [Target.Syntax.denote]
  unfold L2.seq bindE
  refine ⟨.ok updatedLocals, initialGlobals, local_update_changes_only_locals, ?_⟩
  simp [L2.condition, chooseLocal, updatedLocals, initialGlobals, L2.modify,
    L2.gets, updateGlobals, updatedGlobalsAfterLocal]
  exact ⟨.ok (), updatedGlobalsAfterLocal, ⟨⟨(), rfl⟩, rfl⟩,
    by simp [updatedGlobalsAfterLocal]⟩

/-! ## Direct SIMPL to heap-lift pipeline -/

def identityExprEvidence {Result : Type} (read : Globals -> Result) :
    HeapLift.Kernel.ExprEvidence id read where
  rewritePrecondition := fun _ => True
  rewritten := read
  abstractRewriteGuard := fun _ => True
  abstractExpressionGuard := fun _ => True
  abstract := read
  rewrite := by simp [HeapLift.struct_rewrite_expr]
  rewriteGuardAbstracts := by simp [HeapLift.abs_guard]
  expressionAbstracts := by simp [HeapLift.abs_expr]

def identityUpdateEvidence (update : Globals -> Globals) :
    HeapLift.Kernel.UpdateEvidence id update where
  rewritePrecondition := fun _ => True
  rewritten := update
  abstractRewriteGuard := fun _ => True
  abstractUpdateGuard := fun _ => True
  abstract := update
  rewrite := by simp [HeapLift.struct_rewrite_modifies]
  rewriteGuardAbstracts := by simp [HeapLift.abs_guard]
  updateAbstracts := by simp [HeapLift.abs_modifies]

def pipelineHeapSupported :
    HeapLift.Kernel.Supported id
      ((ML.LocalVarExtract.extractCanonical stateModel pipelineLveSupported).target
        initialLocals) :=
  .seq (.gets [] (identityExprEvidence (updateX initialLocals))) fun nextLocals =>
    .condition (identityExprEvidence (chooseLocal nextLocals))
      (.gets [] (identityExprEvidence fun _ => nextLocals))
      (.seq (.modify (identityUpdateEvidence (updateGlobals nextLocals))) fun _ =>
        .gets [] (identityExprEvidence fun _ => nextLocals))

def pipelineL2Supported :
    ML.AutoCorres.L2Supported false pipelineEnv pipelineSource stateModel Globals where
  l1 := pipelineSupported
  initialLocals := initialLocals
  stateMap := id
  heapLift := pipelineHeapSupported

def pipelineL2Translation :=
  ML.AutoCorres.translateL2Supported false pipelineEnv pipelineSource stateModel
    Globals pipelineL2Supported

theorem pipeline_heap_certificate_uses_selected_l2 :
    HeapLift.L2Tcorres pipelineL2Translation.stateMap
      pipelineL2Translation.heapLift.target.denote
      (ML.LocalVarExtract.CanonicalTarget.Syntax.denote
        pipelineL2Translation.l2.target pipelineL2Translation.initialLocals) :=
  pipelineL2Translation.heapLift.correctness

theorem pipeline_heap_generated_read_guard :
    match pipelineL2Translation.heapLift.target with
    | .seq (.guardedGets rewriteGuard expressionGuard _ _) _ =>
        rewriteGuard initialGlobals ∧ expressionGuard initialGlobals
    | _ => False := by
  simp [pipelineL2Translation, pipelineL2Supported, pipelineHeapSupported,
    pipelineSupported, pipelineLveSupported, identityExprEvidence,
    ML.AutoCorres.translateL2Supported, ML.HeapLift.transform]

def conditionSource : Source.Syntax Full Locals Globals :=
  .condition
    (fun state => chooseLocal (stateModel.projectLocals state)
      (stateModel.projectGlobals state))
    (.modify (Source.localTransform stateModel updateX))
    (.modify (Source.globalTransform stateModel updateGlobals))

def conditionSupported : Supported stateModel conditionSource :=
  .condition chooseLocal (.localUpdate updateX) (.globalUpdate updateGlobals)

def conditionCertificate := extract stateModel conditionSupported

theorem condition_target_shape :
    conditionCertificate.target = Target.Syntax.condition chooseLocal
      (.localUpdate updateX) (.globalUpdate updateGlobals) :=
  rfl

theorem condition_true_updates_locals :
    (Except.ok updatedLocals, initialGlobals) ∈
      (Target.Syntax.denote conditionCertificate.target
        initialLocals initialGlobals).results := by
  simp [conditionCertificate, conditionSupported, conditionSource, extract,
    Target.Syntax.denote, L2.condition, L2.gets, chooseLocal, updateX,
    initialLocals, initialGlobals, updatedLocals]

def lowGlobals : Globals := ⟨[7, 8], 1⟩
def lowGlobalsUpdated : Globals := ⟨[2, 7, 8], 4⟩

theorem condition_false_updates_globals :
    (Except.ok initialLocals, lowGlobalsUpdated) ∈
      (Target.Syntax.denote conditionCertificate.target
        initialLocals lowGlobals).results := by
  simp [conditionCertificate, conditionSupported, conditionSource, extract,
    Target.Syntax.denote, L2.condition, L2.seq, L2.modify, L2.gets,
    chooseLocal, updateGlobals, initialLocals, lowGlobals, lowGlobalsUpdated]

def catchSource : Source.Syntax Full Locals Globals :=
  .catch
    (.seq (.modify (Source.localTransform stateModel updateX)) .throw)
    (.modify (Source.globalTransform stateModel updateGlobals))

def catchSupported : Supported stateModel catchSource :=
  .catch (.seq (.localUpdate updateX) .throw) (.globalUpdate updateGlobals)

def catchCertificate := extract stateModel catchSupported
def catchCanonicalCertificate :=
  ML.LocalVarExtract.extractCanonical stateModel catchSupported

theorem catch_target_shape :
    catchCertificate.target = Target.Syntax.catch
      (.seq (.localUpdate updateX) .throw) (.globalUpdate updateGlobals) :=
  rfl

theorem catch_generic_and_canonical_targets_agree :
    catchCanonicalCertificate.target =
      ML.LocalVarExtract.CanonicalTarget.Syntax.ofGeneric
        catchCertificate.target := by
  rfl

theorem catch_generic_and_canonical_denotations_agree (locals : Locals) :
    ML.LocalVarExtract.CanonicalTarget.Syntax.denote
        catchCanonicalCertificate.target locals =
      Target.Syntax.denote catchCertificate.target locals := by
  rw [catch_generic_and_canonical_targets_agree]
  exact LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote_ofGeneric _ _

theorem catch_receives_exceptional_locals :
    (Except.ok updatedLocals, updatedGlobalsAfterLocal) ∈
      (Target.Syntax.denote catchCertificate.target
        initialLocals initialGlobals).results := by
  rw [catch_target_shape]
  simp only [Target.Syntax.denote]
  unfold L2.catch handle
  refine ⟨.error updatedLocals, initialGlobals, ?_, ?_⟩
  · unfold L2.seq bindE
    refine ⟨.ok updatedLocals, initialGlobals, ?_, ?_⟩
    · exact local_update_changes_only_locals
    · simp [L2.throw]
  · simp [L2.seq, L2.modify, L2.gets, updateGlobals, updatedLocals,
      initialGlobals, updatedGlobalsAfterLocal]

/-! ## Certified extraction and closed SSA endpoints -/

theorem sequence_extracts : Extracts stateModel sequenceCertificate.target sequenceSource :=
  sequenceCertificate.corres

theorem catch_extracts : Extracts stateModel catchCertificate.target catchSource :=
  catchCertificate.corres

theorem catch_l2corres :
    L2.L2Corres stateModel.projectGlobals stateModel.projectLocals
      stateModel.projectLocals
      (fun state => stateModel.projectLocals state = initialLocals)
       (Target.Syntax.denote catchCertificate.target initialLocals)
      catchSource.denote :=
  catchCertificate.corres initialLocals

noncomputable def catchSSARefinement := catch_l2corres.toSSA

theorem catch_ssa_refinement_maps_full_to_globals :
    catchSSARefinement.stateMap initialFull = initialGlobals :=
  rfl

theorem l1_closed_ssa_evaluates_exactly :
    cast (by simp only [SSABridge.outcomeTy_type])
        (Zag.Lang.SSA.SSAExpr.evalM?
          (L1.toSSA catchSource.denote).ctx [] SSABridge.outcomeTy
          (L1.toSSA catchSource.denote).expr) =
      some (SSABridge.suspend catchSource.denote) :=
  SSABridge.Refinement.source_eval_exact catchSSARefinement

theorem l2_closed_ssa_evaluates_exactly :
    cast (by simp only [SSABridge.outcomeTy_type])
        (Zag.Lang.SSA.SSAExpr.evalM?
           (L2.toSSA (Target.Syntax.denote catchCertificate.target
             initialLocals)).ctx []
          SSABridge.outcomeTy
           (L2.toSSA (Target.Syntax.denote catchCertificate.target
             initialLocals)).expr) =
      some (SSABridge.suspend
         (Target.Syntax.denote catchCertificate.target initialLocals)) :=
  SSABridge.Refinement.target_eval_exact catchSSARefinement

theorem l1_catch_endpoint_result :
    (Except.ok (), ⟨updatedLocals, updatedGlobalsAfterLocal⟩) ∈
      (catchSource.denote initialFull).results := by
  simp only [catchSource, Source.Syntax.denote, L1.Syntax.denote]
  unfold L1.catch handle
  refine ⟨.error (), ⟨updatedLocals, initialGlobals⟩, ?_, ?_⟩
  · unfold L1.seq bindE
    refine ⟨.ok (), ⟨updatedLocals, initialGlobals⟩, ?_, ?_⟩
    · simp [L1.modify, Source.localTransform, stateModel, updateX, initialFull,
        initialLocals, initialGlobals, updatedLocals]
    · simp [L1.throw]
  · simp [L1.modify, Source.globalTransform, stateModel, updateGlobals,
      updatedLocals, initialGlobals, updatedGlobalsAfterLocal]

theorem l2_catch_endpoint_result :
    (Except.ok updatedLocals, updatedGlobalsAfterLocal) ∈
      (Target.Syntax.denote catchCertificate.target
        initialLocals initialGlobals).results :=
  catch_receives_exceptional_locals

end Zag.Test.L2
