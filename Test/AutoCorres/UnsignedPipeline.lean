import Lang.AutoCorres.ML.autocorres

/-!
# Direct five-phase unsigned-addition pipeline

This test pins one actual generated endpoint at every phase. It is a closed
single-function path and does not claim call, SCC, or C-lowering support.
-/

namespace Zag.Test.AutoCorres.UnsignedPipeline

open Zag.Lang.AutoCorres

noncomputable section

abbrev Word32 := BitVec 32
abbrev Locals := Word32
abbrev Globals := Word32 × Word32
abbrev Full := Locals × Globals
abbrev Word := WordAbstract.Kernel.ValueType.word 32

private def w32 (value : Nat) : Word32 := BitVec.ofNat 32 value

def model : ML.LocalVarExtract.StateModel Full Locals Globals where
  projectGlobals := Prod.snd
  projectLocals := Prod.fst
  assemble := fun locals globals => (locals, globals)
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; cases state; rfl

def localUpdate (_ : Locals) (globals : Globals) : Locals :=
  globals.1 + globals.2

def fullUpdate : Full -> Full :=
  ML.LocalVarExtract.Source.localTransform model localUpdate

def env : Simpl.Body Full Unit Unit := fun _ => none
def source : Simpl.Com Full Unit Unit := .Basic fullUpdate

def l1Supported : ML.AutoCorres.L1Supported false env source model where
  simplConv := .basic fullUpdate
  localVarExtract := .localUpdate localUpdate

def initialLocals : Locals := 0
def stateMap : Globals -> Globals := id
def readAddition (globals : Globals) : Word32 := globals.1 + globals.2

def heapEvidence : HeapLift.Kernel.ExprEvidence stateMap readAddition where
  rewritePrecondition := fun _ => True
  rewritten := readAddition
  abstractRewriteGuard := fun _ => True
  abstractExpressionGuard := fun _ => True
  abstract := readAddition
  rewrite := by simp [HeapLift.struct_rewrite_expr]
  rewriteGuardAbstracts := by simp [HeapLift.abs_guard]
  expressionAbstracts := by simp [HeapLift.abs_expr, stateMap]

def heapSupported : HeapLift.Kernel.Supported stateMap
    ((ML.LocalVarExtract.extractCanonical model l1Supported.localVarExtract).target
      initialLocals) :=
  .gets [] heapEvidence

def l2Supported : ML.AutoCorres.L2Supported false env source model Globals where
  l1 := l1Supported
  initialLocals := initialLocals
  stateMap := stateMap
  heapLift := heapSupported

def wordExpression : ML.WordAbstract.Source.Expr .unit Globals Word :=
  .add (.state Word Prod.fst) (.state Word Prod.snd)

def heapToWordSupported : Pipeline.HeapToWord.Supported 32
    (ML.HeapLift.transform heapSupported).target :=
  .guardedGets wordExpression
    (by intro; trivial) (by intro; trivial) (by intro; rfl)

def heapAdapter := ML.Pipeline.HeapToWord.adapt heapToWordSupported

def expressionCertificate :=
  ML.WordAbstract.Expr.transform (ML.WordAbstract.Expr.supported wordExpression)

def overflowTest (globals : Globals) : Bool :=
  decide (globals.1.toNat + globals.2.toNat <= WordAbstract.UWORD_MAX 32)

theorem overflowTest_exact (globals : Globals) :
    overflowTest globals = true <-> expressionCertificate.guard () globals := by
  simp [overflowTest, expressionCertificate, wordExpression,
    ML.WordAbstract.Expr.supported, ML.WordAbstract.Expr.transform,
    WordAbstract.Kernel.Target.Expr.eval, WordAbstract.Kernel.Target.asNat,
    WordAbstract.Kernel.Target.maxFor]

def wordToStrengthenSupported : Pipeline.WordToStrengthen.Supported 32
    (ML.WordAbstract.transformSource heapAdapter.source).target :=
  .guardedGets overflowTest overflowTest_exact

def supported : ML.AutoCorres.UnsignedSupported 32 false env source model Globals where
  l2 := l2Supported
  heapToWord := heapToWordSupported
  wordToStrengthen := wordToStrengthenSupported

noncomputable def translation :=
  ML.AutoCorres.translateUnsignedSupported 32 false env source model Globals supported

/-! Every phase consumes the actual generated predecessor. -/

theorem simpl_shape : translation.l1.target = .modify fullUpdate := by rfl

theorem lve_shape : translation.l2.target initialLocals =
    .gets readAddition [] := by
  rfl

theorem heap_shape : translation.heapLift.target =
    .guardedGets (fun _ => True) (fun _ => True) readAddition [] := by
  rfl

theorem heap_adapter_shape : translation.heapAdapter.source =
    .gets wordExpression [] := by
  rfl

theorem heap_adapter_exact :
    translation.heapLift.target.denote =
      translation.heapAdapter.source.denote () :=
  translation.heapAdapter.exact

theorem word_shape : translation.wordAbstract.target =
    .seq (.guard expressionCertificate.guard) fun _ =>
      .gets expressionCertificate.target [] := by
  rfl

def expectedStrengthenSource :
    TypeStrengthen.Kernel.Source.Closed Globals Nat Nat :=
  .seq (.guard fun _ state => overflowTest state)
    (.gets (fun _ state => expressionCertificate.target.eval () state) [])

theorem strengthen_adapter_shape :
    translation.wordAdapter.source = expectedStrengthenSource := by
  rfl

theorem word_adapter_exact :
    translation.wordAbstract.target.denote () =
      translation.wordAdapter.source.denote () :=
  translation.wordAdapter.exact

def optionSupportIsGenerated :
    TypeStrengthen.Kernel.Supported .option translation.wordAdapter.source :=
  translation.wordAdapter.supported

def expectedOptionTarget :
    TypeStrengthen.Kernel.Target.Syntax .option Globals Nat :=
  .seq (.atom (oguard overflowTest)) fun _ =>
    .atom (ogets fun state => expressionCertificate.target.eval () state)

theorem type_strengthen_shape :
    translation.typeStrengthen.target = expectedOptionTarget := by
  rfl

/-! The final chain has no independently selectable maps, guards, or endpoints. -/

theorem chain_state_project_l2 :
    translation.chain.stateProjectL2 = model.projectGlobals := by
  rfl

theorem chain_state_project_heap :
    translation.chain.stateProjectHL = stateMap := by
  rfl

theorem chain_l2_precondition :
    translation.chain.preconditionL2 =
      (fun state => model.projectLocals state = translation.initialLocals) := by
  rfl

theorem chain_word_precondition :
    translation.chain.preconditionWA = (fun _ => True) := by
  rfl

theorem chain_result_maps :
    translation.chain.returnExtractL2 = model.projectLocals ∧
    translation.chain.exceptionExtractL2 = model.projectLocals ∧
    translation.chain.returnExtractWA = BitVec.toNat ∧
    translation.chain.exceptionExtractWA = BitVec.toNat := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem chain_endpoints :
    translation.chain.l1 = translation.l1.target.denote ∧
    translation.chain.l2 =
      ML.LocalVarExtract.CanonicalTarget.Syntax.denote translation.l2.target
        translation.initialLocals ∧
    translation.chain.heapLifted = translation.heapLift.target.denote ∧
    translation.chain.wordAbstracted = translation.wordAbstract.target.denote () := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem overflowTest_in_range : overflowTest (w32 3, w32 4) = true := by
  native_decide

theorem overflowTest_overflow : overflowTest (w32 4294967295, w32 1) = false := by
  native_decide

theorem abstract_expression_in_range :
    expressionCertificate.target.eval () (w32 3, w32 4) = 7 := by
  native_decide

theorem generated_l1_target_executes_addition :
    (Except.ok (), (w32 7, (w32 3, w32 4))) ∈
      (translation.l1.target.denote
        (initialLocals, (w32 3, w32 4))).results := by
  rw [simpl_shape]
  simp [SimplConv.Kernel.Target.denote, L1.modify, fullUpdate,
    ML.LocalVarExtract.Source.localTransform, model, localUpdate]
  native_decide

theorem generated_canonical_l2_target_returns_seven :
    (Except.ok (w32 7), (w32 3, w32 4)) ∈
      (ML.LocalVarExtract.CanonicalTarget.Syntax.denote translation.l2.target
        translation.initialLocals (w32 3, w32 4)).results := by
  change (Except.ok (w32 7), (w32 3, w32 4)) ∈
    ((translation.l2.target initialLocals).denote
      (w32 3, w32 4)).results
  rw [lve_shape]
  simp [L2.Syntax.denote, L2.gets, readAddition]
  native_decide

theorem option_target_in_range :
    translation.typeStrengthen.target.denote (w32 3, w32 4) = some 7 := by
  rw [type_strengthen_shape]
  simp [expectedOptionTarget, TypeStrengthen.Kernel.Target.Syntax.denote,
    obind, overflowTest_in_range, abstract_expression_in_range]

theorem option_target_overflow :
    translation.typeStrengthen.target.denote (w32 4294967295, w32 1) = none := by
  rw [type_strengthen_shape]
  simp [expectedOptionTarget, TypeStrengthen.Kernel.Target.Syntax.denote,
    obind, overflowTest_overflow]

theorem embedded_final_target_overflow_fails :
    (TypeStrengthen.Kernel.embed (Exception := Unit) .option
      translation.typeStrengthen.target.denote
      (w32 4294967295, w32 1)).failed := by
  simp [TypeStrengthen.Kernel.embed, TypeStrengthen.Kernel.denote,
    TypeStrengthen.Kernel.optionNondet, option_target_overflow]

theorem embedded_final_target_overflow_has_no_results
    (result : Except Unit Nat × Globals) :
    result ∉ (TypeStrengthen.Kernel.embed (Exception := Unit) .option
      translation.typeStrengthen.target.denote
      (w32 4294967295, w32 1)).results := by
  rcases result with ⟨outcome, post⟩
  change (outcome, post) ∉ (liftE (TypeStrengthen.Kernel.optionNondet
    translation.typeStrengthen.target.denote)
      (w32 4294967295, w32 1)).results
  rw [L2.mem_liftE_iff]
  rintro ⟨value, _, member⟩
  have optionRun : TypeStrengthen.Kernel.optionNondet
      translation.typeStrengthen.target.denote
        (w32 4294967295, w32 1) =
      (Zag.Lang.AutoCorres.fail (σ := Globals) (α := Nat)
        (w32 4294967295, w32 1)) := by
    simp [TypeStrengthen.Kernel.optionNondet, option_target_overflow]
  rw [optionRun] at member
  exact mem_fail member

def overflowFull : Full := (initialLocals, (w32 4294967295, w32 1))

theorem source_executes_normally_on_overflow :
    Simpl.Exec env source (.normal overflowFull)
      (.normal (w32 0, (w32 4294967295, w32 1))) := by
  have wraps : fullUpdate overflowFull =
      (w32 0, (w32 4294967295, w32 1)) := by
    native_decide
  rw [← wraps]
  exact .basic

/-! TypeStrengthen closes over a distinct inner exception type. -/

inductive InnerException where
  | rejected
  deriving Repr

inductive OuterException where
  | escaped
  deriving Repr

def closedExceptionSource :
    TypeStrengthen.Kernel.Source.Closed Nat InnerException Nat :=
  .seq (.guard fun _ state => decide (state < 10))
    (.gets (fun _ state => state + 1) [])

def closedExceptionSupported :
    TypeStrengthen.Kernel.Supported .option closedExceptionSource :=
  .optionSeq .optionGuard .optionRead

noncomputable def closedExceptionCertificate :=
  ML.TypeStrengthen.strengthenClosed closedExceptionSupported

theorem closed_exception_target_shape :
    closedExceptionCertificate.target =
      .seq (.atom (oguard fun state => decide (state < 10))) fun _ =>
        .atom (ogets fun state => state + 1) := by
  rfl

theorem closed_exception_exact_for_arbitrary_outer (Outer : Type) :
    L2.call (Exception := Outer) (closedExceptionSource.denote ()) =
      TypeStrengthen.Kernel.embed (Exception := Outer) .option
        closedExceptionCertificate.target.denote :=
  closedExceptionCertificate.exact Outer

theorem closed_exception_target_accepts_supported_state :
    closedExceptionCertificate.target.denote 4 = some 5 := by
  rw [closed_exception_target_shape]
  rfl

theorem closed_exception_target_rejects_guarded_state :
    closedExceptionCertificate.target.denote 10 = none := by
  rw [closed_exception_target_shape]
  rfl

theorem closed_exception_exact_for_distinct_outer :
    L2.call (Exception := OuterException) (closedExceptionSource.denote ()) =
      TypeStrengthen.Kernel.embed (Exception := OuterException) .option
        closedExceptionCertificate.target.denote :=
  closed_exception_exact_for_arbitrary_outer OuterException

/-! The generated closed bridge endpoints are exact primitive-call packages. -/

theorem generated_l1_closed_ssa_endpoint_exact :
    cast (by simp only [SSABridge.outcomeTy_type])
        (Zag.Lang.SSA.SSAExpr.evalM?
          (L1.toSSA translation.l1.target.denote).ctx [] SSABridge.outcomeTy
          (L1.toSSA translation.l1.target.denote).expr) =
      some (SSABridge.suspend translation.l1.target.denote) :=
  L1.toSSA_eval translation.l1.target.denote

theorem generated_l2_closed_ssa_endpoint_exact :
    cast (by simp only [SSABridge.outcomeTy_type])
        (Zag.Lang.SSA.SSAExpr.evalM?
          (L2.toSSA (ML.LocalVarExtract.CanonicalTarget.Syntax.denote
            translation.l2.target translation.initialLocals)).ctx []
          SSABridge.outcomeTy
          (L2.toSSA (ML.LocalVarExtract.CanonicalTarget.Syntax.denote
            translation.l2.target translation.initialLocals)).expr) =
      some (SSABridge.suspend
        (ML.LocalVarExtract.CanonicalTarget.Syntax.denote
          translation.l2.target translation.initialLocals)) :=
  L2.toSSA_eval _

/-! Indexed adapter support rejects HeapLift targets with false guards. -/

def falseRewriteGuardTarget :
    HeapLift.Kernel.Target Unit (BitVec 8) (BitVec 8) :=
  .guardedGets (fun _ => False) (fun _ => True) (fun _ => 0) []

theorem false_rewrite_guard_has_no_heap_to_word_support :
    ∀ _ : Pipeline.HeapToWord.Supported 8 falseRewriteGuardTarget, False := by
  intro supported
  cases supported with
  | guardedGets _ rewriteHolds _ _ => exact rewriteHolds ()

def falseExpressionGuardTarget :
    HeapLift.Kernel.Target Unit (BitVec 8) (BitVec 8) :=
  .guardedGets (fun _ => True) (fun _ => False) (fun _ => 0) []

theorem false_expression_guard_has_no_heap_to_word_support :
    ∀ _ : Pipeline.HeapToWord.Supported 8 falseExpressionGuardTarget, False := by
  intro supported
  cases supported with
  | guardedGets _ _ expressionHolds _ => exact expressionHolds ()

def mismatchedHeapReadTarget :
    HeapLift.Kernel.Target Unit (BitVec 8) (BitVec 8) :=
  .guardedGets (fun _ => True) (fun _ => True) (fun _ => 0) []

def mismatchedHeapExpression :
    WordAbstract.Kernel.Source.Expr .unit Unit (.word 8) :=
  .word 8 (BitVec.ofNat 8 1)

def heapSupportExpression
    (supported : Pipeline.HeapToWord.Supported 8 mismatchedHeapReadTarget) :
    WordAbstract.Kernel.Source.Expr .unit Unit (.word 8) :=
  match supported with
  | .guardedGets expression _ _ _ => expression

theorem mismatched_expression_cannot_be_the_heap_support_witness
    (supported : Pipeline.HeapToWord.Supported 8 mismatchedHeapReadTarget) :
    heapSupportExpression supported ≠ mismatchedHeapExpression := by
  intro equality
  cases supported with
  | guardedGets expression _ _ expressionExact =>
      change expression = mismatchedHeapExpression at equality
      subst expression
      have impossible := expressionExact ()
      have notEqual : mismatchedHeapExpression.eval () () ≠ (0 : BitVec 8) := by
        native_decide
      exact notEqual impossible

theorem false_test_is_not_exact_for_true_guard :
    ¬(∀ _state : Unit, false = true ↔ True) := by
  simp

def finalChain : ChainCertificate
    (L2State := Globals) (L2Exception := Word32) (L2Result := Word32)
    (HLState := Globals) (WAException := Nat)
    false env source
    (TypeStrengthen.Kernel.embed (Exception := Unit) .option
      translation.typeStrengthen.target.denote) :=
  translation.chain

theorem finalAcCorres :
    ac_corres
      (translation.chain.stateProjectHL ∘ translation.chain.stateProjectL2)
      false env
      (translation.chain.returnExtractWA ∘ translation.chain.returnExtractL2)
      (fun state => translation.chain.preconditionL2 state ∧
        translation.chain.preconditionWA
          (translation.chain.stateProjectHL
            (translation.chain.stateProjectL2 state)))
      (TypeStrengthen.Kernel.embed (Exception := Unit) .option
        translation.typeStrengthen.target.denote) source :=
  translation.chain.acCorres

def initialFull : Full := (initialLocals, (w32 3, w32 4))

theorem concrete_target_result_under_precondition :
    (translation.chain.preconditionL2 initialFull ∧
      translation.chain.preconditionWA
        (translation.chain.stateProjectHL
          (translation.chain.stateProjectL2 initialFull))) ∧
    (Except.ok 7, (w32 3, w32 4)) ∈
      (TypeStrengthen.Kernel.embed (Exception := Unit) .option
        translation.typeStrengthen.target.denote (w32 3, w32 4)).results ∧
    ¬(TypeStrengthen.Kernel.embed (Exception := Unit) .option
      translation.typeStrengthen.target.denote (w32 3, w32 4)).failed := by
  constructor
  · constructor <;> trivial
  · change (Except.ok 7, (w32 3, w32 4)) ∈
        (liftE (TypeStrengthen.Kernel.optionNondet
          translation.typeStrengthen.target.denote) (w32 3, w32 4)).results ∧
      ¬(liftE (TypeStrengthen.Kernel.optionNondet
        translation.typeStrengthen.target.denote) (w32 3, w32 4)).failed
    have optionRun : TypeStrengthen.Kernel.optionNondet
        translation.typeStrengthen.target.denote (w32 3, w32 4) =
        pure 7 (w32 3, w32 4) := by
      simp [TypeStrengthen.Kernel.optionNondet, option_target_in_range]
    unfold liftE Zag.Lang.AutoCorres.bind
    rw [optionRun]
    simp [returnOk, Zag.Lang.AutoCorres.pure]
    exact ⟨7, w32 3, w32 4, rfl, rfl⟩

end
end Zag.Test.AutoCorres.UnsignedPipeline
