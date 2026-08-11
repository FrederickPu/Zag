import Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipelineWord
import Test.AutoCorres.CParser.ScalarSimpl.Plus2PipelineFinal

/-! # Fixture-derived `mult_by_add` through TypeStrengthen and final `ac_corres` -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

abbrev DeclarationContext := (((Unit × Bool) × Unit) × Unit) × Unit

def strengthenLoopBody :
    TypeStrengthen.Kernel.Source.Term (DeclarationContext × Bool) Globals Bool Bool :=
  .seq (.exactGuard fun input state => splitValid multByAddCondition input.2 state)
    (.seq (.exactGuard fun input state => splitValid multByAddResultIncrement input.1.2 state)
      (.seq (.modify fun input state => updateExpression 3 u32 multByAddResultIncrement
          input.1.1.2 state)
        (.seq (.exactGuard fun input state => splitValid multByAddDecrement
            input.1.1.1.2 state)
          (.seq (.modify fun input state => updateExpression 1 u32 multByAddDecrement
              input.1.1.1.1.2 state)
            (.pure (fun input => input.1.1.1.1.1.2) [])))))

def strengthenCatchBody :
    TypeStrengthen.Kernel.Source.Term (Unit × Bool) Globals Bool Bool :=
  .seq (.modify fun input state => clearSlot 3 input.2 state)
    (.seq (.exactGuard fun input state => splitValid (.literal s32 0) input.1.2 state)
      (.seq (.modify fun input state => updateExpression 3 u32 (.literal s32 0)
          input.1.1.2 state)
        (.seq
          (.while (fun _ locals state => propositionBool (splitLoopTest locals state))
            strengthenLoopBody (fun input => input.1.1.1.2) [])
          (.seq (.exactGuard fun input state =>
              splitValid (.variable u32 3) input.2 state)
            (.seq (.modify fun input state => setResult input.1.2 state)
              (.throw (fun _ => true) []))))))

def strengthenHandler :
    TypeStrengthen.Kernel.Source.Term ((Unit × Bool) × Bool)
      Globals Bool Bool :=
  .pure (fun input => input.2) []

def strengthenRest :
    TypeStrengthen.Kernel.Source.Term ((Unit × Bool) × Bool)
      Globals Bool Nat :=
  .seq (.exactGuard fun input state => splitReturned input.2 state)
    (.gets (fun _ state => (readResult state).toNat) [])

def strengthenSource : TypeStrengthen.Kernel.Source.Closed Globals Bool Nat :=
  .seq (.pure (fun _ => false) [])
    (.seq (.catchHandlers strengthenCatchBody strengthenHandler) strengthenRest)

def strengthenSupported :
    TypeStrengthen.Kernel.Supported .nondet strengthenSource :=
  .nondetSeq .nondetValue
    (.nondetSeq (.nondetCatchHandlers .nondetValue)
      (.nondetSeq .nondetExactGuard .nondetRead))

def strengthenCertificate := ML.TypeStrengthen.strengthenClosed strengthenSupported

private theorem loop_test_function :
    (fun locals state => propositionBool (splitLoopTest locals state) = true) =
      splitLoopTest := by
  funext locals state
  exact propext (propositionBool_exact _)

private theorem simplified_loop_body (argument : DeclarationContext) (locals : Bool) :
    strengthenLoopBody.denote (argument, locals) = (exactLoopBody locals).denote := by
  simp only [strengthenLoopBody, TypeStrengthen.Kernel.Source.Term.denote,
    exactLoopBody, lveLoopBodySupported, ML.LocalVarExtract.extractCanonical,
    ML.LocalVarExtract.extract, LocalVarExtract.Kernel.Certificate.close,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric, L2.Syntax.denote]
  simp [PlusPipeline.l2_seq_assoc, PlusPipeline.l2_seq_gets]

theorem word_to_strengthen_call_exact :
    L2.call (Exception := Unit) (wordCertificate.target.denote ()) =
      L2.call (Exception := Unit) (strengthenSource.denote ()) := by
  dsimp [wordCertificate, ML.WordAbstract.transformSource,
    ML.WordAbstract.transform, ML.WordAbstract.transformRaw,
    ML.WordAbstract.supported, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform, wordSource, wordLveSource, wordCatchBody,
    wordDeclaration, wordReturnTail, wordGuard, wordSkip, wordGlobalUpdate,
    strengthenSource, strengthenCatchBody, strengthenHandler, strengthenRest]
  simp only [WordAbstract.Kernel.Target.Syntax.denote,
    WordAbstract.Kernel.Target.Expr.eval,
    WordAbstract.Kernel.TypeMap.concretize,
    TypeStrengthen.Kernel.Source.Term.denote]
  rw [loop_test_function]
  simp only [WordAbstract.Kernel.ExactValueType.type,
    WordAbstract.Kernel.typeMap, WordAbstract.Kernel.TypeMap.concretize,
    WordAbstract.valid_typ_abs_fn_id, id_eq]
  simp [PlusPipeline.l2_seq_assoc, PlusPipeline.l2_seq_true_guard,
    PlusPipeline.l2_seq_gets, PlusPipeline.l2_seq_throw,
    simplified_loop_body]

theorem type_strengthen_consumes_word_endpoint :
    L2.call (Exception := Unit) (wordCertificate.target.denote ()) =
      TypeStrengthen.Kernel.embed (Exception := Unit) .nondet
        strengthenCertificate.target.denote := by
  rw [word_to_strengthen_call_exact]
  exact strengthenCertificate.exact Unit

def finalTarget : L2.L2Program Globals Unit Nat :=
  TypeStrengthen.Kernel.embed .nondet strengthenCertificate.target.denote

def finalChain : ChainCertificate
    (L2State := Globals) (L2Exception := Bool) (L2Result := BitVec 32)
    (HLState := Globals) (WAException := Bool)
    false emptyEnvironment multByAdd.command finalTarget :=
  { stateProjectL2 := model.projectGlobals
    returnExtractL2 := fun state => readResult (model.projectGlobals state)
    exceptionExtractL2 := model.projectLocals
    preconditionL2 := fun state => model.projectLocals state = false
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := BitVec.toNat
    exceptionExtractWA := id
    l1 := generatedL1.denote
    l1Corres := fixtureSimplCertificate.corres
    l2 := projectedL2
    l2Corres := projectedL2Corres
    heapLifted := projectedL2
    heapLiftCorres := heapLiftCorres
    wordAbstracted := wordCertificate.target.denote ()
    wordAbstractCorres := word_consumes_heap_endpoint
    typeStrengthen := type_strengthen_consumes_word_endpoint }

theorem final_chain_endpoints :
    finalChain.l1 = generatedL1.denote ∧
    finalChain.l2 = projectedL2 ∧
    finalChain.heapLifted = projectedL2 ∧
    finalChain.wordAbstracted = wordCertificate.target.denote () := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finalAcCorres :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => (readResult (model.projectGlobals state)).toNat)
      (fun state => model.projectLocals state = false)
      finalTarget multByAdd.command := by
  simpa [finalChain, Function.comp_def] using finalChain.acCorres

def initialGlobals (a b : MultByAddWord32) : Globals :=
  model.projectGlobals (multByAddInitial a b)

theorem initial_locals (a b : MultByAddWord32) :
    model.projectLocals (multByAddInitial a b) = false := by
  simp [multByAddInitial, mult_by_add_is_resolved_body, expectedMultByAdd,
    Function.enter, model, Plus2Pipeline.model, State.write, State.clear]

private def loopGlobals (remaining : Nat) (b : MultByAddWord32) (result : Int) : Globals :=
  model.projectGlobals (multByAddState remaining b result)

private theorem assemble_loop_globals (remaining : Nat) (b : MultByAddWord32)
    (result : Int) :
    model.assemble false (loopGlobals remaining b result) =
      multByAddState remaining b result := by
  rfl

private theorem assemble_initial_globals (a b : MultByAddWord32) :
    model.assemble false (initialGlobals a b) = multByAddInitial a b := by
  rw [← initial_locals a b]
  exact model.assemble_project _

private theorem initializer_valid (a b : MultByAddWord32) :
    splitValid (.literal s32 0) false (clearSlot 3 false (initialGlobals a b)) := by
  refine ⟨0, ?_⟩
  simp [Expr.eval]

private theorem initializer_update (a b : MultByAddWord32) :
    updateExpression 3 u32 (.literal s32 0) false
        (clearSlot 3 false (initialGlobals a b)) =
      loopGlobals a.toNat b 0 := by
  unfold updateExpression loopGlobals
  change model.projectGlobals
      ((model.assemble false (clearSlot 3 false (initialGlobals a b))).write 3 u32
        (expressionValue (.literal s32 0)
          (model.assemble false (clearSlot 3 false (initialGlobals a b))))) = _
  have assembledClear :
      model.assemble false (clearSlot 3 false (initialGlobals a b)) =
        (multByAddInitial a b).clear 3 := by
    unfold clearSlot
    rw [show model.assemble false (initialGlobals a b) = multByAddInitial a b by
      exact assemble_initial_globals a b]
    have locals : model.projectLocals ((multByAddInitial a b).clear 3) = false := by
      simpa [model, Plus2Pipeline.model, State.clear] using initial_locals a b
    rw [← locals]
    exact model.assemble_project _
  rw [assembledClear]
  simp [expressionValue, Plus2Pipeline.expressionValue, Expr.eval]
  have resetEq : (multByAddInitial a b).resetReturn = multByAddInitial a b := by
    simp [multByAddInitial, mult_by_add_is_resolved_body, expectedMultByAdd,
      Function.enter, State.resetReturn, State.clear, State.write]
  have initialized := mult_by_add_local_initializer_state a b
  rw [resetEq] at initialized
  exact congrArg model.projectGlobals initialized

private theorem loop_condition_valid (remaining : Nat) (b : MultByAddWord32)
    (result : Int) (bound : remaining < 2 ^ 32) :
    splitValid multByAddCondition false (loopGlobals remaining b result) := by
  change ∃ value, multByAddCondition.eval
    (model.assemble false (loopGlobals remaining b result)) = some value
  rw [assemble_loop_globals]
  rcases remaining with _ | remaining
  · exact ⟨0, multByAddCondition_zero b result⟩
  · exact ⟨1, multByAddCondition_succ remaining b result bound⟩

private theorem loop_increment_valid (remaining : Nat) (b : MultByAddWord32)
    (result : Int) :
    splitValid multByAddResultIncrement false (loopGlobals remaining b result) := by
  exact ⟨u32.cast (result + Int.ofNat b.toNat), by
    change multByAddResultIncrement.eval
      (model.assemble false (loopGlobals remaining b result)) = _
    rw [assemble_loop_globals]
    exact multByAddResultIncrement_eval remaining b result⟩

private theorem loop_decrement_valid (remaining : Nat) (b : MultByAddWord32)
    (result : Int) (bound : remaining + 1 < 2 ^ 32) :
    splitValid multByAddDecrement false (loopGlobals (remaining + 1) b result) := by
  exact ⟨Int.ofNat remaining, by
    change multByAddDecrement.eval
      (model.assemble false (loopGlobals (remaining + 1) b result)) = _
    rw [assemble_loop_globals]
    exact multByAddDecrement_eval remaining b result bound⟩

private theorem loop_increment_update (remaining : Nat) (b : MultByAddWord32)
    (result : Int) :
    updateExpression 3 u32 multByAddResultIncrement false
        (loopGlobals remaining b result) =
      loopGlobals remaining b (u32.cast (result + Int.ofNat b.toNat)) := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue loopGlobals
  rw [show Plus2Pipeline.model.assemble false (model.projectGlobals
      (multByAddState remaining b result)) = multByAddState remaining b result by rfl,
    multByAddResultIncrement_eval, Option.getD_some, multByAdd_result_update]
  rfl

private theorem loop_decrement_update (remaining : Nat) (b : MultByAddWord32)
    (result : Int) (bound : remaining + 1 < 2 ^ 32) :
    updateExpression 1 u32 multByAddDecrement false
        (loopGlobals (remaining + 1) b result) = loopGlobals remaining b result := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue loopGlobals
  rw [show Plus2Pipeline.model.assemble false (model.projectGlobals
      (multByAddState (remaining + 1) b result)) =
        multByAddState (remaining + 1) b result by rfl]
  rw [multByAddDecrement_eval remaining b result bound, Option.getD_some,
    multByAdd_decrement_update]
  rfl

private def declarationContext : DeclarationContext := (((((), false), ()), ()), ())

private theorem strengthen_loop_body_exact (remaining : Nat) (b : MultByAddWord32)
    (result : Int) (bound : remaining + 1 < 2 ^ 32) :
    strengthenLoopBody.denote (declarationContext, false)
        (loopGlobals (remaining + 1) b result) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals remaining b (u32.cast (result + Int.ofNat b.toNat))) := by
  simp only [strengthenLoopBody, TypeStrengthen.Kernel.Source.Term.denote, L2.seq]
  rw [Plus2Pipeline.bindE_guard_left _ _ _
    (loop_condition_valid (remaining + 1) b result bound)]
  rw [Plus2Pipeline.bindE_guard_left _ _ _
    (loop_increment_valid (remaining + 1) b result)]
  rw [Plus2Pipeline.bindE_modify_left, loop_increment_update]
  rw [Plus2Pipeline.bindE_guard_left _ _ _
    (loop_decrement_valid remaining b _ bound)]
  rw [Plus2Pipeline.bindE_modify_left, loop_decrement_update _ _ _ bound]
  exact Plus2Pipeline.l2_gets_eq _ _ _

private def strengthenWhileTest (result : Except Bool Bool) (state : Globals) : Prop :=
  match result with
  | .error _ => False
  | .ok value => (fun locals state =>
      propositionBool (splitLoopTest locals state) = true) value state

private def strengthenWhileBody : Except Bool Bool → Nondet Globals (Except Bool Bool) :=
  whileLoopEBody fun locals => strengthenLoopBody.denote (declarationContext, locals)

private def generatedLoop : L2.L2Program Globals Bool Bool :=
  whileLoop strengthenWhileTest strengthenWhileBody (Except.ok false)

private theorem generated_loop_is_l2 :
    L2.while (fun locals state => propositionBool (splitLoopTest locals state) = true)
      (fun locals => strengthenLoopBody.denote (declarationContext, locals)) false [] =
      generatedLoop := by
  unfold L2.while whileLoopE generatedLoop strengthenWhileTest strengthenWhileBody
  apply congrArg (fun test => whileLoop test
    (whileLoopEBody fun locals => strengthenLoopBody.denote (declarationContext, locals))
    (Except.ok false))
  funext result state
  cases result <;> rfl

private theorem generated_loop_test_zero (b : MultByAddWord32) (result : Int) :
    ¬ propositionBool (splitLoopTest false (loopGlobals 0 b result)) = true := by
  rw [propositionBool_exact]
  simp [splitLoopTest, assemble_loop_globals, multByAddCondition_zero]

private theorem generated_loop_test_succ (remaining : Nat) (b : MultByAddWord32)
    (result : Int) (bound : remaining + 1 < 2 ^ 32) :
    propositionBool (splitLoopTest false (loopGlobals (remaining + 1) b result)) = true := by
  rw [propositionBool_exact]
  simp [splitLoopTest, assemble_loop_globals, multByAddCondition_succ, bound]

private theorem generated_loop_exact (a b : MultByAddWord32) (remaining : Nat)
    (result : Int) (bound : remaining < 2 ^ 32)
    (invariant : multByAddInvariant a b (BitVec.ofNat 32 remaining)
      (BitVec.ofInt 32 result)) :
    generatedLoop (loopGlobals remaining b result) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals 0 b (multByAddAccumulate b remaining result)) := by
  induction remaining using Nat.strongRecOn generalizing result with
  | ind remaining induction =>
      rcases remaining with _ | remaining
      · apply Plus2Pipeline.behavior_ext
        · funext outcome
          apply propext
          constructor
          · intro member
            change WhileResult _ _ (some (Except.ok false, loopGlobals 0 b result))
                (some outcome) at member
            cases member with
            | stop _ => simp [multByAddAccumulate, Zag.Lang.AutoCorres.returnOk,
                Zag.Lang.AutoCorres.pure]
            | step holds _ _ => exact False.elim (generated_loop_test_zero b result holds)
          · intro member
            have equality : outcome = (Except.ok false, loopGlobals 0 b result) := by
              simpa [multByAddAccumulate, Zag.Lang.AutoCorres.returnOk,
                Zag.Lang.AutoCorres.pure] using member
            cases equality
            exact WhileResult.stop (generated_loop_test_zero b result)
        · apply propext
          constructor
          · rintro (finite | notTerminates)
            · change WhileResult _ _ (some (Except.ok false, loopGlobals 0 b result)) none
                at finite
              cases finite with
              | bodyFailure holds _ => exact generated_loop_test_zero b result holds
              | step holds _ _ => exact generated_loop_test_zero b result holds
            · exact notTerminates (.stop (generated_loop_test_zero b result))
          · intro failed
            exact False.elim failed
      · have testHolds := generated_loop_test_succ remaining b result bound
        have bodyExact := strengthen_loop_body_exact remaining b result bound
        have nextInvariant := mult_by_add_invariant_preserved a b remaining result invariant
        have variantDecreases := mult_by_add_variant_decreases remaining bound
        have restExact := induction remaining (Nat.lt_succ_self remaining)
          (result := u32.cast (result + Int.ofNat b.toNat)) (by omega) nextInvariant
        apply Plus2Pipeline.behavior_ext
        · funext outcome
          apply propext
          constructor
          · intro member
            change WhileResult _ _ (some (Except.ok false,
                loopGlobals (remaining + 1) b result)) (some outcome) at member
            cases member with
            | stop stopped => exact False.elim (stopped testHolds)
            | step _ bodyMember rest =>
                simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                rw [bodyExact] at bodyMember
                simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                have restMember : outcome ∈
                    (generatedLoop (loopGlobals remaining b
                      (u32.cast (result + Int.ofNat b.toNat)))).results := rest
                rw [restExact] at restMember
                rw [multByAddAccumulate]
                exact restMember
          · intro member
            have expectedMember :
                (Except.ok false, loopGlobals 0 b
                  (multByAddAccumulate b remaining
                    (u32.cast (result + Int.ofNat b.toNat)))) ∈
                (generatedLoop (loopGlobals remaining b
                  (u32.cast (result + Int.ofNat b.toNat)))).results := by
              rw [restExact]
              exact mem_returnOk.mpr ⟨rfl, rfl⟩
            rcases outcome with ⟨outcome, post⟩
            change (outcome, post) = (Except.ok false,
              loopGlobals 0 b (multByAddAccumulate b (remaining + 1) result)) at member
            cases member
            exact @WhileResult.step Globals (Except Bool Bool)
              strengthenWhileTest strengthenWhileBody
              (Except.ok false) (loopGlobals (remaining + 1) b result)
              (Except.ok false) (loopGlobals remaining b
                (u32.cast (result + Int.ofNat b.toNat)))
              (some (Except.ok false,
                loopGlobals 0 b (multByAddAccumulate b (remaining + 1) result)))
              testHolds (by
                simp only [strengthenWhileBody, whileLoopEBody]
                rw [bodyExact]
                exact mem_returnOk.mpr ⟨rfl, rfl⟩)
              (by
                change WhileResult _ _ (some (Except.ok false,
                  loopGlobals remaining b (u32.cast (result + Int.ofNat b.toNat))))
                  (some (Except.ok false, loopGlobals 0 b
                    (multByAddAccumulate b remaining
                      (u32.cast (result + Int.ofNat b.toNat))))) at expectedMember
                simpa only [multByAddAccumulate] using expectedMember)
        · apply propext
          constructor
          · rintro (finite | notTerminates)
            · change WhileResult _ _ (some (Except.ok false,
                loopGlobals (remaining + 1) b result)) none at finite
              cases finite with
              | bodyFailure _ bodyFailed =>
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyFailed
                  rw [bodyExact] at bodyFailed
                  exact Plus2Pipeline.returnOk_not_failed false _ bodyFailed
              | step _ bodyMember rest =>
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                  rw [bodyExact] at bodyMember
                  simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                  rcases bodyMember with ⟨rfl, rfl⟩
                  have restFailed :
                      (generatedLoop (loopGlobals remaining b
                        (u32.cast (result + Int.ofNat b.toNat)))).failed := Or.inl rest
                  rw [restExact] at restFailed
                  exact Plus2Pipeline.returnOk_not_failed false _ restFailed
            · apply notTerminates
              exact @WhileTerminates.step Globals (Except Bool Bool)
                strengthenWhileTest strengthenWhileBody
                (Except.ok false) (loopGlobals (remaining + 1) b result) testHolds
                (by
                  intro next nextState bodyMember
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                  rw [bodyExact] at bodyMember
                  simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                  rcases bodyMember with ⟨rfl, rfl⟩
                  exact Classical.byContradiction fun restDoesNotTerminate => by
                    have restFailed :
                        (generatedLoop (loopGlobals remaining b
                          (u32.cast (result + Int.ofNat b.toNat)))).failed :=
                      Or.inr restDoesNotTerminate
                    rw [restExact] at restFailed
                    exact Plus2Pipeline.returnOk_not_failed false _ restFailed)
          · intro failed
            exact False.elim failed

private def resultGlobals (b : MultByAddWord32) (value : Int) : Globals :=
  model.projectGlobals
    ((multByAddState 0 b value).returnValue u32 (u32.cast value))

private theorem loop_result_valid (b : MultByAddWord32) (value : Int) :
    splitValid (.variable u32 3) false (loopGlobals 0 b value) := by
  refine ⟨u32.cast value, ?_⟩
  change (Expr.variable u32 3).eval
    (model.assemble false (loopGlobals 0 b value)) = some (u32.cast value)
  rw [assemble_loop_globals]
  simp [Expr.eval, multByAddState_read_result]

private theorem set_loop_result (b : MultByAddWord32) (value : Int) :
    setResult false (loopGlobals 0 b value) = resultGlobals b value := by
  unfold setResult expressionValue Plus2Pipeline.expressionValue resultGlobals loopGlobals
  rw [show model.assemble false (model.projectGlobals (multByAddState 0 b value)) =
    multByAddState 0 b value by rfl]
  simp [Expr.eval, multByAddState_read_result]

private theorem generated_catch_exact (a b : MultByAddWord32) :
    strengthenCatchBody.denote ((), false) (initialGlobals a b) =
      Zag.Lang.AutoCorres.throw true
        (resultGlobals b (multByAddAccumulate b a.toNat 0)) := by
  have initialInvariant : multByAddInvariant a b (BitVec.ofNat 32 a.toNat)
      (BitVec.ofInt 32 0) := by
    simpa using mult_by_add_invariant_initial a b
  have loopExact := generated_loop_exact a b a.toNat 0 a.isLt initialInvariant
  simp only [strengthenCatchBody, TypeStrengthen.Kernel.Source.Term.denote, L2.seq]
  rw [Plus2Pipeline.bindE_modify_left]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (initializer_valid a b)]
  rw [Plus2Pipeline.bindE_modify_left, initializer_update]
  have loopEq :
      L2.while (fun locals state => propositionBool (splitLoopTest locals state) = true)
        (fun locals => strengthenLoopBody.denote ((((((), false), ()), ()), ()), locals))
        false [] = generatedLoop := by
    simpa [declarationContext] using generated_loop_is_l2
  rw [loopEq]
  rw [Plus2Pipeline.bindE_replace_returnOk _ _ _ _ loopExact]
  rw [Plus2Pipeline.bindE_guard_left _ _ _
    (loop_result_valid b (multByAddAccumulate b a.toNat 0))]
  rw [Plus2Pipeline.bindE_modify_left, set_loop_result]
  rfl

private theorem generated_nondet_catch_exact (a b : MultByAddWord32) :
    TypeStrengthen.Kernel.nondetCatch
        (strengthenCatchBody.denote ((), false))
        (fun exception => Zag.Lang.AutoCorres.pure exception)
        (initialGlobals a b) =
      Zag.Lang.AutoCorres.pure true
        (resultGlobals b (multByAddAccumulate b a.toNat 0)) := by
  unfold TypeStrengthen.Kernel.nondetCatch
  exact Plus2Pipeline.bind_replace_pure _ _ _ _ (generated_catch_exact a b)

private def generatedFinalNondet : Nondet Globals Nat :=
  Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.pure false) fun locals =>
    Zag.Lang.AutoCorres.bind
      (TypeStrengthen.Kernel.nondetCatch
        (strengthenCatchBody.denote ((), locals)) fun exception =>
          Zag.Lang.AutoCorres.pure exception) fun locals =>
      Zag.Lang.AutoCorres.bind
        (Zag.Lang.AutoCorres.guard (splitReturned locals)) fun _ =>
          Zag.Lang.AutoCorres.gets fun state => (readResult state).toNat

private theorem final_target_is_generated :
    finalTarget = Zag.Lang.AutoCorres.liftE generatedFinalNondet := by
  rfl

private theorem generated_final_exact (a b : MultByAddWord32) :
    generatedFinalNondet (initialGlobals a b) =
      Zag.Lang.AutoCorres.pure
        ((readResult (resultGlobals b (multByAddAccumulate b a.toNat 0))).toNat)
        (resultGlobals b (multByAddAccumulate b a.toNat 0)) := by
  unfold generatedFinalNondet
  rw [Plus2Pipeline.bind_pure_left_at]
  rw [Plus2Pipeline.bind_replace_pure _ _ _ _ (generated_nondet_catch_exact a b)]
  rw [Plus2Pipeline.bind_guard_left _ _ _
    (show splitReturned true
      (resultGlobals b (multByAddAccumulate b a.toNat 0)) by rfl)]
  rfl

private theorem input_result_globals (a b : MultByAddWord32) :
    resultGlobals b (multByAddAccumulate b a.toNat 0) =
      model.projectGlobals (multByAddResult a b) := by
  rfl

private theorem input_result_value (a b : MultByAddWord32) :
    (readResult
      (resultGlobals b (multByAddAccumulate b a.toNat 0))).toNat =
        (a * b).toNat := by
  rw [input_result_globals]
  change (BitVec.ofInt 32 (multByAddResult a b).result).toNat = (a * b).toNat
  rw [mult_by_add_success_is_wrapping_product]

/-- Exact generated TypeStrengthen behavior for every pair of u32 inputs. -/
theorem final_target_exact (a b : MultByAddWord32) :
    finalTarget (initialGlobals a b) =
      Zag.Lang.AutoCorres.returnOk (ε := Unit) (a * b).toNat
        (model.projectGlobals (multByAddResult a b)) := by
  rw [final_target_is_generated]
  rw [Plus2Pipeline.liftE_replace_pure _ _ _ (generated_final_exact a b)]
  rw [input_result_value, input_result_globals]

/-- The generated final target is total and has no failure branch on arbitrary inputs. -/
theorem final_target_no_failure (a b : MultByAddWord32) :
    ¬(finalTarget (initialGlobals a b)).failed := by
  rw [final_target_exact]
  exact Plus2Pipeline.returnOk_not_failed _ _

theorem final_preserves_arbitrary_wrapping_product (a b : MultByAddWord32) :
    (Except.ok (a * b).toNat, model.projectGlobals (multByAddResult a b)) ∈
      (finalTarget (initialGlobals a b)).results := by
  rw [final_target_exact]
  exact mem_returnOk.mpr ⟨rfl, rfl⟩

/-- Generated-endpoint total correctness, matching upstream `mult_by_add'`. -/
theorem mult_by_add_correct (a b : MultByAddWord32) :
    ∀ result post,
      (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
        result = (a * b).toNat := by
  intro result post member
  rw [final_target_exact, mem_returnOk] at member
  exact member.1

theorem mult_by_add_valid (a b : MultByAddWord32) :
    ¬(finalTarget (initialGlobals a b)).failed ∧
      ∀ result post,
        (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
          result = (a * b).toNat :=
  ⟨final_target_no_failure a b, mult_by_add_correct a b⟩

theorem source_total_no_failure_connected (a b : MultByAddWord32) :
    Raw.FunctionExec multByAddCertificate.program "mult_by_add"
        multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
        (multByAddInitial a b) (.success (multByAddResult a b)) ∧
      ¬Raw.FunctionExec multByAddCertificate.program "mult_by_add"
        multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
        (multByAddInitial a b) .undefinedBehavior :=
  mult_by_add_total_no_failure a b

theorem mult_by_add_end_to_end (a b : MultByAddWord32) :
    (Raw.FunctionExec multByAddCertificate.program "mult_by_add"
          multByAddCertificate.functionInfo multByAddCertificate.rawBody
          multByAdd.returnType (multByAddInitial a b)
            (.success (multByAddResult a b)) ∧
        ¬Raw.FunctionExec multByAddCertificate.program "mult_by_add"
          multByAddCertificate.functionInfo multByAddCertificate.rawBody
          multByAdd.returnType (multByAddInitial a b) .undefinedBehavior) ∧
      ¬(finalTarget (initialGlobals a b)).failed ∧
        (Except.ok (a * b).toNat, model.projectGlobals (multByAddResult a b)) ∈
          (finalTarget (initialGlobals a b)).results :=
  ⟨source_total_no_failure_connected a b,
    final_target_no_failure a b,
    final_preserves_arbitrary_wrapping_product a b⟩

end


end Zag.Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipeline
