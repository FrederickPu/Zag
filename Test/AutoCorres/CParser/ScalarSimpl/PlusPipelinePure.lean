import Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline
import Lang.AutoCorres.CParser.CallGraph
import Lang.AutoCorres.CParser.Frontend

/-! # Exact pure endpoint for the fixture-derived `plus` translation -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

namespace FixtureSchedule

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.CallGraph

private def symbolName? (program : Program) (symbolId : Nat) : Option String :=
  (program.symbolById? symbolId).map (·.sourceName)

def namedSCCs : Option (List (List String × Bool)) := do
  let program ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files
    "examples/plus.c").program
  (build program).sccs.mapM fun component => do
    let names ← component.members.mapM (symbolName? program)
    return (names, component.recursive)

def namedEdges : Option (List (String × Option String)) := do
  let program ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files
    "examples/plus.c").program
  (build program).edges.mapM fun edge => do
    let caller ← edge.caller.bind (symbolName? program)
    let callee := edge.callee.bind (symbolName? program)
    return (caller, callee)

/-- The fixture schedule has two independent leaves; only `main` depends on them. -/
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

noncomputable section

abbrev PlusWord32 := BitVec 32

private theorem pure_behavior_ext {S R : Type} {left right : Behavior S R}
    (results : left.results = right.results) (failed : left.failed = right.failed) :
    left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

private theorem pure_bind_return_left {S A B : Type} (value : A)
    (next : A -> Nondet S B) (state : S) :
    Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.pure value) next state =
      next value state := by
  apply pure_behavior_ext
  · funext result
    apply propext
    constructor
    · rintro ⟨source, middle, equality, member⟩
      change (source, middle) = (value, state) at equality
      cases equality
      exact member
    · intro member
      exact ⟨value, state, rfl, member⟩
  · apply propext
    constructor
    · rintro (failed | ⟨source, middle, equality, failed⟩)
      · exact False.elim failed
      · change (source, middle) = (value, state) at equality
        cases equality
        exact failed
    · intro failed
      exact Or.inr ⟨value, state, rfl, failed⟩

private theorem pure_liftE_at {S E R : Type} (value : R) (state : S) :
    Zag.Lang.AutoCorres.liftE (ε := E) (Zag.Lang.AutoCorres.pure value) state =
      Zag.Lang.AutoCorres.returnOk value state := by
  unfold Zag.Lang.AutoCorres.liftE
  exact pure_bind_return_left value _ state

private theorem pure_bindE_return_left {S E A B : Type} (value : A)
    (next : A -> L2.L2Program S E B) (state : S) :
    Zag.Lang.AutoCorres.bindE (Zag.Lang.AutoCorres.returnOk value) next state =
      next value state := by
  unfold Zag.Lang.AutoCorres.bindE Zag.Lang.AutoCorres.returnOk
  exact pure_bind_return_left (Except.ok value) _ state

private theorem pure_l2_gets_at {S E R : Type} (read : S -> R)
    (names : List String) (state : S) :
    L2.gets (Exception := E) read names state =
      Zag.Lang.AutoCorres.returnOk (read state) state := by
  unfold L2.gets Zag.Lang.AutoCorres.gets
  exact pure_liftE_at (read state) state

private theorem pure_l2_guard_at {S E : Type} (test : S -> Prop) (state : S)
    (holds : test state) :
    L2.guard (Exception := E) test state =
      Zag.Lang.AutoCorres.returnOk () state := by
  unfold L2.guard
  have guardEq : Zag.Lang.AutoCorres.guard test state =
      Zag.Lang.AutoCorres.pure () state := by
    apply pure_behavior_ext
    · funext result
      apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
    · apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
  unfold Zag.Lang.AutoCorres.liftE Zag.Lang.AutoCorres.bind
  rw [guardEq]
  exact pure_liftE_at () state

private theorem pure_l2_catch_throw_at {S E F R : Type} (exception : E)
    (names : List String) (handler : E -> L2.L2Program S F R) (state : S) :
    L2.catch (L2.throw exception names) handler state = handler exception state := by
  unfold L2.catch L2.throw Zag.Lang.AutoCorres.handle
  exact pure_bind_return_left (Except.error exception) _ state

private theorem pure_l2_catch_throw {S E F R : Type} (exception : E)
    (names : List String) (handler : E -> L2.L2Program S F R) :
    L2.catch (L2.throw exception names) handler = handler exception := by
  funext state
  exact pure_l2_catch_throw_at exception names handler state

private theorem u32_cast_add (left right : Int) :
    u32.cast (u32.cast left + u32.cast right) = u32.cast (left + right) := by
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus,
    Int.add_emod]

abbrev PureLocals := State
abbrev PureGlobals := Unit

/-- `plus` has no C globals, so its complete function state is extracted as locals. -/
def pureModel : ML.LocalVarExtract.StateModel State PureLocals PureGlobals where
  projectGlobals := fun _ => ()
  projectLocals := id
  assemble := fun locals _ => locals
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; rfl

def pureReset (locals : PureLocals) (_ : PureGlobals) : PureLocals :=
  locals.resetReturn

def pureReturn (locals : PureLocals) (_ : PureGlobals) : PureLocals :=
  returnUpdate locals

def pureFinalize (locals : PureLocals) (_ : PureGlobals) : PureLocals :=
  expectedFunction.finalize locals

def pureExpressionValid (locals : PureLocals) (_ : PureGlobals) : Prop :=
  expressionValid locals

def pureReturned (locals : PureLocals) (_ : PureGlobals) : Prop :=
  locals.returned = true

def pureNormalizedL1 : L1.Syntax State :=
  .seq (.modify (ML.LocalVarExtract.Source.localTransform pureModel pureReset))
    (.seq
      (.catch
        (.seq
          (.seq (.guard fun state =>
              pureExpressionValid (pureModel.projectLocals state)
                (pureModel.projectGlobals state))
            (.seq
              (.modify (ML.LocalVarExtract.Source.localTransform pureModel pureReturn))
              .throw))
          .skip)
        .skip)
      (.seq
        (.modify (ML.LocalVarExtract.Source.localTransform pureModel pureFinalize))
        (.seq (.guard fun state =>
          pureReturned (pureModel.projectLocals state)
            (pureModel.projectGlobals state)) .skip)))

/-- The all-locals normalization denotes the exact fixture-generated SimplConv target. -/
theorem pure_normalized_fixture_endpoint :
    fixtureSimplCertificate.target.denote = pureNormalizedL1.denote := by
  rw [fixture_simpl_target_eq, simpl_generated_shape]
  rfl

def pureLveSupported : ML.LocalVarExtract.Supported pureModel pureNormalizedL1 :=
  .seq (.localUpdate pureReset)
    (.seq
      (.catch
        (.seq
          (.seq (.guard pureExpressionValid)
            (.seq (.localUpdate pureReturn) .throw))
          .skip)
        .skip)
      (.seq (.localUpdate pureFinalize)
        (.seq (.guard pureReturned) .skip)))

def pureLveCertificate :=
  ML.LocalVarExtract.extractCanonical pureModel pureLveSupported

/-- Adjacent LVE certificate consuming the exact fixture endpoint. -/
theorem pure_lve_consumes_fixture_endpoint (locals : PureLocals) :
    L2.L2Corres pureModel.projectGlobals pureModel.projectLocals
      pureModel.projectLocals
      (fun state => pureModel.projectLocals state = locals)
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        pureLveCertificate.target locals)
      fixtureSimplCertificate.target.denote := by
  rw [pure_normalized_fixture_endpoint]
  exact pureLveCertificate.corres locals

def pureInitial (a b : PlusWord32) : PureLocals :=
  plusInitial (Int.ofNat a.toNat) (Int.ofNat b.toNat)

def pureReadResult (locals : PureLocals) : PlusWord32 :=
  BitVec.ofInt 32 locals.result

def pureProjectedL2Syntax (a b : PlusWord32) :
    L2.Syntax PureGlobals PureLocals PlusWord32 :=
  .seq (pureLveCertificate.target (pureInitial a b)) fun locals =>
    .gets (fun _ => pureReadResult locals) []

def pureProjectedL2 (a b : PlusWord32) :
    L2.L2Program PureGlobals PureLocals PlusWord32 :=
  (pureProjectedL2Syntax a b).denote

private theorem pureProjectCorres (locals : PureLocals) :
    CorresXF id (fun result _ => pureReadResult result)
      (fun exception _ => exception) (fun _ => True)
      (L2.seq
        (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
          pureLveCertificate.target locals)
        fun result => L2.gets (fun _ => pureReadResult result) [])
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        pureLveCertificate.target locals) := by
  intro state hypothesis
  constructor
  · intro result post member
    cases result with
    | error exception => exact ⟨Except.error exception, post, member, rfl⟩
    | ok value =>
        refine ⟨Except.ok value, post, member, ?_⟩
        simp [L2.gets]
  · intro failed
    exact hypothesis.2 (Or.inl failed)

/-- Adjacent projection certificate from generated LVE output to the word result. -/
theorem pure_projected_l2_corres (a b : PlusWord32) :
    L2.L2Corres pureModel.projectGlobals
      (fun state => pureReadResult (pureModel.projectLocals state))
      pureModel.projectLocals
      (fun state => pureModel.projectLocals state = pureInitial a b)
      (pureProjectedL2 a b) fixtureSimplCertificate.target.denote := by
  rw [pure_normalized_fixture_endpoint]
  have merged := CorresXF.merge (pureLveCertificate.corres (pureInitial a b))
    (pureProjectCorres (pureInitial a b))
  change CorresXF pureModel.projectGlobals
    (fun _ state => pureReadResult (pureModel.projectLocals state))
    (fun _ state => pureModel.projectLocals state)
    (fun state => pureModel.projectLocals state = pureInitial a b)
    (pureProjectedL2 a b) pureNormalizedL1.denote
  simpa only [pureProjectedL2, pureProjectedL2Syntax, L2.Syntax.denote,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote,
    Function.comp_apply, Function.comp_def, id_eq, and_true] using merged

theorem pure_initial_expression (a b : PlusWord32) :
    plusExpression.eval (pureInitial a b).resetReturn =
      some (u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat)) := by
  simp [pureInitial, plusInitial, plus_eq_expected, expectedFunction,
    Function.enter, plusExpression, Expr.eval, State.resetReturn, State.read?,
    State.write, u32_checked, u32_cast_add]

private theorem bitvec_of_u32_cast (value : Int) :
    BitVec.ofInt 32 (u32.cast value) = BitVec.ofInt 32 value := by
  apply BitVec.eq_of_toFin_eq
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus,
    BitVec.ofInt]

theorem pure_initial_sum (a b : PlusWord32) :
    BitVec.ofInt 32 (u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat)) = a + b := by
  rw [bitvec_of_u32_cast, BitVec.ofInt_add, Int.ofNat_eq_natCast,
    Int.ofNat_eq_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  simp

theorem pure_initial_valid (a b : PlusWord32) :
    pureExpressionValid (pureReset (pureInitial a b) ()) () := by
  refine ⟨u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat), ?_⟩
  exact pure_initial_expression a b

private theorem pure_initial_guard (a b : PlusWord32) :
    pureExpressionValid (State.resetReturn (pureInitial a b)) = fun _ => True := by
  funext state
  apply propext
  exact iff_true_intro (pure_initial_valid a b)

def pureResultLocals (a b : PlusWord32) : PureLocals :=
  (pureInitial a b).resetReturn.returnValue u32
    (u32.cast (Int.ofNat a.toNat + Int.ofNat b.toNat))

theorem pure_result_returned (a b : PlusWord32) :
    pureReturned (pureResultLocals a b) = fun _ => True := by
  funext state
  apply propext
  simp [pureReturned, pureResultLocals, State.returnValue]

theorem pure_finalize_result (a b : PlusWord32) :
    pureFinalize (pureResultLocals a b) () = pureResultLocals a b := by
  simp [pureFinalize, pureResultLocals, Function.finalize,
    State.returnValue]

theorem pure_result_sum (a b : PlusWord32) :
    pureReadResult (pureResultLocals a b) = a + b := by
  simp only [pureReadResult, pureResultLocals, State.returnValue]
  rw [u32_cast_idempotent, pure_initial_sum]

/-- The generated all-locals endpoint is exactly a state-independent wrapping add. -/
theorem pure_projected_l2_exact (a b : PlusWord32) :
    pureProjectedL2 a b = L2.gets (fun _ : PureGlobals => a + b) [] := by
  funext state
  cases state
  simp only [pureProjectedL2, pureProjectedL2Syntax, pureLveCertificate,
    pureLveSupported, ML.LocalVarExtract.extractCanonical,
    ML.LocalVarExtract.extract, LocalVarExtract.Kernel.Certificate.close,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric,
    L2.Syntax.denote]
  simp only [PlusPipeline.l2_seq_assoc, PlusPipeline.l2_seq_gets,
    pureReset, pureReturn, returnUpdate, expressionValue,
    pure_initial_expression, Option.getD_some]
  rw [pure_initial_guard]
  rw [PlusPipeline.l2_seq_true_guard, PlusPipeline.l2_seq_throw,
    pure_l2_catch_throw]
  rw [PlusPipeline.l2_seq_gets]
  change L2.seq
      (L2.seq (L2.guard (pureReturned (pureResultLocals a b)))
        (fun _ => L2.gets (fun _ => pureResultLocals a b) []))
      (fun value => L2.gets (fun _ => pureReadResult value) []) () = _
  rw [pure_result_returned, PlusPipeline.l2_seq_true_guard,
    PlusPipeline.l2_seq_gets]
  exact congrArg (fun value =>
    L2.gets (Exception := PureLocals) (fun _ : PureGlobals => value) [] ())
      (pure_result_sum a b)

/-- Identity HeapLift certificate: `plus` has no heap state. -/
theorem pure_heap_lift_corres (a b : PlusWord32) :
    HeapLift.L2Tcorres id (pureProjectedL2 a b) (pureProjectedL2 a b) :=
  HeapLift.L2Tcorres_id _

/-- Identity WordAbstract certificate, matching `Plus.thy` without `unsigned_word_abs`. -/
theorem pure_word_abstract_corres (a b : PlusWord32) :
    WordAbstract.corresTA (fun _ : PureGlobals => True) id id
      (pureProjectedL2 a b) (pureProjectedL2 a b) :=
  CorresXF.refl (fun _ => True) _

abbrev PureArguments := PlusWord32 × PlusWord32

def pureStrengthenSource :
    TypeStrengthen.Kernel.Source.Term PureArguments PureGlobals PureLocals PlusWord32 :=
  .pure (fun arguments => pureReadResult
    (pureResultLocals arguments.1 arguments.2)) ["ret"]

def pureStrengthenSupported :
    TypeStrengthen.Kernel.Supported .pure pureStrengthenSource :=
  .pureValue

def pureStrengthenCertificate (arguments : PureArguments) :=
  ML.TypeStrengthen.strengthenAt pureStrengthenSupported arguments

/-- The generated pure TypeStrengthen target, exposed as a two-argument function. -/
def generatedPlus (a b : PlusWord32) : PlusWord32 :=
  (pureStrengthenCertificate (a, b)).target.denote

theorem generated_plus_eq_wrapping_add :
    generatedPlus = fun a b => a + b := by
  funext a b
  change pureReadResult (pureResultLocals a b) = a + b
  exact pure_result_sum a b

/-- Fixture-connected counterpart of upstream `plus_correct`. -/
theorem plus_correct (a b : PlusWord32) : generatedPlus a b = a + b := by
  rw [generated_plus_eq_wrapping_add]

/-- Fixture-connected counterpart of the concrete upstream 3+2 theorem. -/
theorem plus_three_plus_two : generatedPlus 3 2 = 5 := by
  rw [plus_correct]
  native_decide

def pureFinalTarget (a b : PlusWord32) :
    L2.L2Program PureGlobals Unit PlusWord32 :=
  TypeStrengthen.Kernel.embed .pure
    (pureStrengthenCertificate (a, b)).target.denote

/-- The generated TypeStrengthen program is exactly pure wrapping word addition. -/
theorem pure_final_target_exact (a b : PlusWord32) :
    pureFinalTarget a b = TypeStrengthen.TS_return (a + b) := by
  set_option maxRecDepth 100000 in
    change TypeStrengthen.TS_return
        (pureReadResult (pureResultLocals a b)) =
      TypeStrengthen.TS_return (a + b)
  rw [pure_result_sum]

theorem pure_final_target_no_failure (a b : PlusWord32) :
    ¬(pureFinalTarget a b ()).failed := by
  rw [pure_final_target_exact]
  simp [TypeStrengthen.TS_return, L2.failed_liftE,
    Zag.Lang.AutoCorres.pure]

/-- Adjacent TypeStrengthen equality from the exact no-op WordAbstract endpoint. -/
theorem pure_type_strengthen_consumes_word_endpoint (a b : PlusWord32) :
    L2.call (Exception := Unit) (pureProjectedL2 a b) = pureFinalTarget a b := by
  rw [pure_projected_l2_exact]
  have sourceExact : pureStrengthenSource.denote (a, b) =
      L2.gets (fun _ : PureGlobals => a + b) [] := by
    simp only [pureStrengthenSource, TypeStrengthen.Kernel.Source.Term.denote]
    exact congrArg (fun value =>
      L2.gets (Exception := PureLocals) (fun _ : PureGlobals => value) [])
        (pure_result_sum a b)
  rw [← sourceExact]
  change L2.call (Exception := Unit)
      (pureStrengthenSource.denote (a, b)) = pureFinalTarget a b
  rw [(pureStrengthenCertificate (a, b)).equality]
  exact (TypeStrengthen.L2_call_embed_exact
    (InnerException := PureLocals) (Exception := Unit) .pure
    (pureStrengthenCertificate (a, b)).target.denote).eq

def pureFinalChain (a b : PlusWord32) : ChainCertificate
    (L2State := PureGlobals) (L2Exception := PureLocals) (L2Result := PlusWord32)
    (HLState := PureGlobals) (WAException := PureLocals)
    false emptyEnvironment plus.command (pureFinalTarget a b) :=
  { stateProjectL2 := pureModel.projectGlobals
    returnExtractL2 := fun state => pureReadResult (pureModel.projectLocals state)
    exceptionExtractL2 := pureModel.projectLocals
    preconditionL2 := fun state => pureModel.projectLocals state = pureInitial a b
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := id
    exceptionExtractWA := id
    l1 := fixtureSimplCertificate.target.denote
    l1Corres := fixtureSimplCertificate.corres
    l2 := pureProjectedL2 a b
    l2Corres := pure_projected_l2_corres a b
    heapLifted := pureProjectedL2 a b
    heapLiftCorres := pure_heap_lift_corres a b
    wordAbstracted := pureProjectedL2 a b
    wordAbstractCorres := pure_word_abstract_corres a b
    typeStrengthen := pure_type_strengthen_consumes_word_endpoint a b }

theorem pure_final_chain_endpoints (a b : PlusWord32) :
    (pureFinalChain a b).l1 = fixtureSimplCertificate.target.denote ∧
      (pureFinalChain a b).l2 = pureProjectedL2 a b ∧
      (pureFinalChain a b).heapLifted = pureProjectedL2 a b ∧
      (pureFinalChain a b).wordAbstracted = pureProjectedL2 a b := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pure_final_ac_corres (a b : PlusWord32) :
    ac_corres pureModel.projectGlobals false emptyEnvironment
      (fun state => pureReadResult (pureModel.projectLocals state))
      (fun state => pureModel.projectLocals state = pureInitial a b)
      (pureFinalTarget a b) plus.command := by
  simpa [pureFinalChain, Function.comp_def] using (pureFinalChain a b).acCorres

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline
