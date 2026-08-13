import Test.AutoCorres.CParser.ScalarSimpl.Plus2PipelineWord
import Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline

/-! # Fixture-derived `plus2` through TypeStrengthen and final `ac_corres` -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.Plus2Pipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

theorem behavior_ext {State Result : Type}
    {left right : Behavior State Result}
    (results : left.results = right.results)
    (failed : left.failed = right.failed) : left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

theorem bindE_returnOk_left {State Exception Alpha Beta : Type}
    (value : Alpha) (next : Alpha → L2.L2Program State Exception Beta)
    (state : State) :
    Zag.Lang.AutoCorres.bindE (Zag.Lang.AutoCorres.returnOk value) next state =
      next value state := by
  apply behavior_ext
  · funext result
    apply propext
    constructor
    · rintro ⟨source, middle, equality, member⟩
      change (source, middle) = (Except.ok value, state) at equality
      cases equality
      exact member
    · intro member
      exact ⟨Except.ok value, state, rfl, member⟩
  · apply propext
    constructor
    · rintro (failed | ⟨source, middle, equality, failed⟩)
      · exact False.elim failed
      · change (source, middle) = (Except.ok value, state) at equality
        cases equality
        exact failed
    · intro failed
      exact Or.inr ⟨Except.ok value, state, rfl, failed⟩

theorem liftE_pure_at {State Exception Result : Type}
    (value : Result) (state : State) :
    Zag.Lang.AutoCorres.liftE (Zag.Lang.AutoCorres.pure value) state =
      Zag.Lang.AutoCorres.returnOk (ε := Exception) value state := by
  apply behavior_ext
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

theorem returnOk_not_failed {State Exception Result : Type}
    (value : Result) (state : State) :
    ¬(Zag.Lang.AutoCorres.returnOk (ε := Exception) value state).failed := by
  exact id

theorem liftE_replace_pure {State Exception Result : Type}
    {program : Nondet State Result} (state post : State) (value : Result)
    (equality : program state = Zag.Lang.AutoCorres.pure value post) :
    Zag.Lang.AutoCorres.liftE (ε := Exception) program state =
      Zag.Lang.AutoCorres.returnOk value post := by
  unfold Zag.Lang.AutoCorres.liftE Zag.Lang.AutoCorres.bind
  rw [equality]
  exact liftE_pure_at value post

theorem l2_guard_eq {State Exception : Type} {test : State → Prop}
    {state : State} (holds : test state) :
    L2.guard (Exception := Exception) test state =
      Zag.Lang.AutoCorres.returnOk () state := by
  have sourceEq : Zag.Lang.AutoCorres.guard test state =
      Zag.Lang.AutoCorres.pure () state := by
    apply behavior_ext
    · funext result
      apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
    · apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
  unfold L2.guard
  rw [show Zag.Lang.AutoCorres.liftE (Zag.Lang.AutoCorres.guard test) state =
    Zag.Lang.AutoCorres.liftE (Zag.Lang.AutoCorres.pure ()) state by
      unfold Zag.Lang.AutoCorres.liftE Zag.Lang.AutoCorres.bind
      rw [sourceEq]]
  exact liftE_pure_at () state

theorem l2_modify_eq {State Exception : Type} (update : State → State)
    (state : State) :
    L2.modify (Exception := Exception) update state =
      Zag.Lang.AutoCorres.returnOk () (update state) := by
  unfold L2.modify
  change Zag.Lang.AutoCorres.liftE (Zag.Lang.AutoCorres.pure ())
      (update state) = _
  exact liftE_pure_at () (update state)

theorem l2_gets_eq {State Exception Result : Type} (read : State → Result)
    (names : List String) (state : State) :
    L2.gets (Exception := Exception) read names state =
      Zag.Lang.AutoCorres.returnOk (read state) state := by
  unfold L2.gets
  change Zag.Lang.AutoCorres.liftE (Zag.Lang.AutoCorres.pure (read state))
      state = _
  exact liftE_pure_at (read state) state

theorem bindE_guard_left {State Exception Beta : Type}
    (test : State → Prop) (next : Unit → L2.L2Program State Exception Beta)
    (state : State) (holds : test state) :
    Zag.Lang.AutoCorres.bindE (L2.guard test) next state = next () state := by
  unfold Zag.Lang.AutoCorres.bindE Zag.Lang.AutoCorres.bind
  rw [l2_guard_eq holds]
  exact bindE_returnOk_left () next state

theorem bindE_modify_left {State Exception Beta : Type}
    (update : State → State) (next : Unit → L2.L2Program State Exception Beta)
    (state : State) :
    Zag.Lang.AutoCorres.bindE (L2.modify update) next state =
      next () (update state) := by
  unfold Zag.Lang.AutoCorres.bindE Zag.Lang.AutoCorres.bind
  rw [l2_modify_eq]
  exact bindE_returnOk_left () next (update state)

theorem bindE_congr_left {State Exception Alpha Beta : Type}
    {first second : L2.L2Program State Exception Alpha}
    (next : Alpha → L2.L2Program State Exception Beta) (state : State)
    (equality : first state = second state) :
    Zag.Lang.AutoCorres.bindE first next state =
      Zag.Lang.AutoCorres.bindE second next state := by
  unfold Zag.Lang.AutoCorres.bindE Zag.Lang.AutoCorres.bind
  rw [equality]

theorem bindE_replace_returnOk {State Exception Alpha Beta : Type}
    {first : L2.L2Program State Exception Alpha}
    (next : Alpha → L2.L2Program State Exception Beta) (state post : State)
    (value : Alpha)
    (equality : first state = Zag.Lang.AutoCorres.returnOk value post) :
    Zag.Lang.AutoCorres.bindE first next state = next value post := by
  unfold Zag.Lang.AutoCorres.bindE Zag.Lang.AutoCorres.bind
  rw [equality]
  exact bindE_returnOk_left value next post

theorem bind_pure_left_at {State Alpha Beta : Type}
    (value : Alpha) (next : Alpha → Nondet State Beta) (state : State) :
    Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.pure value) next state =
      next value state := by
  apply behavior_ext
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

theorem bind_congr_left {State Alpha Beta : Type}
    {first second : Nondet State Alpha} (next : Alpha → Nondet State Beta)
    (state : State) (equality : first state = second state) :
    Zag.Lang.AutoCorres.bind first next state =
      Zag.Lang.AutoCorres.bind second next state := by
  unfold Zag.Lang.AutoCorres.bind
  rw [equality]

theorem bind_replace_pure {State Alpha Beta : Type}
    {first : Nondet State Alpha} (next : Alpha → Nondet State Beta)
    (state post : State) (value : Alpha)
    (equality : first state = Zag.Lang.AutoCorres.pure value post) :
    Zag.Lang.AutoCorres.bind first next state = next value post := by
  unfold Zag.Lang.AutoCorres.bind
  rw [equality]
  exact bind_pure_left_at value next post

theorem bind_guard_left {State Beta : Type} (test : State → Prop)
    (next : Unit → Nondet State Beta) (state : State) (holds : test state) :
    Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.guard test) next state =
      next () state := by
  have guardEq : Zag.Lang.AutoCorres.guard test state =
      Zag.Lang.AutoCorres.pure () state := by
    apply behavior_ext
    · funext result
      apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
    · apply propext
      simp [Zag.Lang.AutoCorres.guard, Zag.Lang.AutoCorres.pure, holds]
  exact bind_replace_pure next state state () guardEq

def strengthenLoopBody :
    TypeStrengthen.Kernel.Source.Term ((Unit × Bool) × Bool)
      Globals Bool Bool :=
  .seq (.exactGuard fun input state => splitValid plus2Condition input.2 state)
    (.seq (.exactGuard fun input state => splitValid plus2Increment input.1.2 state)
      (.seq (.modify fun input state => updateExpression 1 u32 plus2Increment
          input.1.1.2 state)
        (.seq (.exactGuard fun input state => splitValid plus2Decrement
            input.1.1.1.2 state)
          (.seq (.modify fun input state => updateExpression 2 u32 plus2Decrement
              input.1.1.1.1.2 state)
            (.pure (fun input => input.1.1.1.1.1.2) [])))))

def strengthenCatchBody :
    TypeStrengthen.Kernel.Source.Term (Unit × Bool) Globals Bool Bool :=
  .seq
    (.while (fun _ locals state => propositionBool (splitLoopTest locals state))
      strengthenLoopBody (fun input => input.2) [])
    (.seq (.exactGuard fun input state =>
        splitValid (.variable u32 1) input.2 state)
      (.seq (.modify fun input state => setResult input.1.2 state)
        (.throw (fun _ => true) [])))

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

def strengthenCertificate :=
  ML.TypeStrengthen.strengthenClosed strengthenSupported

/-! The pinned `Plus.thy` does not request unsigned word abstraction for
`plus2`. Keep the result word-valued through the default generated chain. -/

private theorem loop_test_function :
    (fun locals state => propositionBool (splitLoopTest locals state) = true) =
      splitLoopTest := by
  funext locals state
  exact propext (propositionBool_exact _)

private theorem simplified_loop_body (argument : Unit × Bool) (locals : Bool) :
    strengthenLoopBody.denote (argument, locals) =
      (exactLoopBody locals).denote := by
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
    wordReturnTail, wordGuard, wordSkip, wordGlobalUpdate, strengthenSource,
    strengthenCatchBody, strengthenHandler, strengthenRest]
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

/-- Source-faithful generated endpoint for default word abstraction. -/
def wordFinalTarget : L2.L2Program Globals Unit (BitVec 32) :=
  L2.call projectedL2

theorem word_type_strengthen_consumes_heap_endpoint :
    L2.call (Exception := Unit) projectedL2 = wordFinalTarget := by
  rfl

def wordFinalChain : ChainCertificate
    (L2State := Globals) (L2Exception := Bool) (L2Result := BitVec 32)
    (HLState := Globals) (WAException := Bool)
    false emptyEnvironment plus2.command wordFinalTarget :=
  { stateProjectL2 := model.projectGlobals
    returnExtractL2 := fun state => readResult (model.projectGlobals state)
    exceptionExtractL2 := model.projectLocals
    preconditionL2 := fun state => model.projectLocals state = false
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := id
    exceptionExtractWA := id
    l1 := generatedL1.denote
    l1Corres := fixtureSimplCertificate.corres
    l2 := projectedL2
    l2Corres := projectedL2Corres
    heapLifted := projectedL2
    heapLiftCorres := heapLiftCorres
    wordAbstracted := projectedL2
    wordAbstractCorres := CorresXF.refl (fun _ => True) projectedL2
    typeStrengthen := word_type_strengthen_consumes_heap_endpoint }

theorem wordFinalAcCorres :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => readResult (model.projectGlobals state))
      (fun state => model.projectLocals state = false)
      wordFinalTarget plus2.command := by
  simpa [wordFinalChain, Function.comp_def] using wordFinalChain.acCorres

def finalChain : ChainCertificate
    (L2State := Globals) (L2Exception := Bool) (L2Result := BitVec 32)
    (HLState := Globals) (WAException := Bool)
    false emptyEnvironment plus2.command finalTarget :=
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
      finalTarget plus2.command := by
  simpa [finalChain, Function.comp_def] using finalChain.acCorres

def initialGlobals (a b : Word32) : Globals := model.projectGlobals (plus2Initial a b)

theorem initial_locals (a b : Word32) :
    model.projectLocals (plus2Initial a b) = false := by
  simp [plus2_initial_eq_state, plus2State, model, State.write]

private def loopGlobals (a : Int) (b : Nat) : Globals :=
  model.projectGlobals (plus2State a b)

private theorem initial_globals_eq (a b : Word32) :
    initialGlobals a b = loopGlobals (Int.ofNat a.toNat) b.toNat := by
  simp [initialGlobals, loopGlobals, plus2_initial_eq_state]

private theorem assemble_loop_globals (a : Int) (b : Nat) :
    model.assemble false (loopGlobals a b) = plus2State a b := by
  rfl

private theorem loop_condition_valid (a : Int) (b : Nat) (bound : b < 2 ^ 32) :
    splitValid plus2Condition false (loopGlobals a b) := by
  unfold splitValid expressionValid
  rw [assemble_loop_globals]
  rcases b with _ | b
  · exact ⟨0, plus2Condition_zero a⟩
  · exact ⟨1, plus2Condition_succ a b bound⟩

private theorem loop_increment_valid (a : Int) (b : Nat) :
    splitValid plus2Increment false (loopGlobals a b) := by
  exact ⟨u32.cast (a + 1), by
    simpa [splitValid, expressionValid, assemble_loop_globals] using
      plus2Increment_eval a b⟩

private theorem loop_decrement_valid (a : Int) (b : Nat)
    (bound : b + 1 < 2 ^ 32) :
    splitValid plus2Decrement false (loopGlobals a (b + 1)) := by
  exact ⟨Int.ofNat b, by
    simpa [splitValid, expressionValid, assemble_loop_globals] using
      plus2Decrement_eval a b bound⟩

private theorem loop_increment_update (a : Int) (b : Nat) :
    updateExpression 1 u32 plus2Increment false (loopGlobals a b) =
      loopGlobals (a + 1) b := by
  unfold updateExpression expressionValue loopGlobals
  rw [show model.assemble false (model.projectGlobals (plus2State a b)) =
    plus2State a b by rfl, plus2Increment_eval, Option.getD_some,
    plus2_increment_state]

private theorem loop_decrement_update (a : Int) (b : Nat)
    (bound : b + 1 < 2 ^ 32) :
    updateExpression 2 u32 plus2Decrement false (loopGlobals a (b + 1)) =
      loopGlobals a b := by
  unfold updateExpression expressionValue loopGlobals
  rw [show model.assemble false (model.projectGlobals (plus2State a (b + 1))) =
    plus2State a (b + 1) by rfl, plus2Decrement_eval a b bound,
    Option.getD_some, plus2_decrement_state]

private theorem strengthen_loop_body_exact (a : Int) (b : Nat)
    (bound : b + 1 < 2 ^ 32) :
    strengthenLoopBody.denote (((), false), false) (loopGlobals a (b + 1)) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals (a + 1) b) := by
  simp only [strengthenLoopBody, TypeStrengthen.Kernel.Source.Term.denote,
    L2.seq]
  rw [bindE_guard_left _ _ _ (loop_condition_valid a (b + 1) bound)]
  rw [bindE_guard_left _ _ _ (loop_increment_valid a (b + 1))]
  rw [bindE_modify_left, loop_increment_update]
  rw [bindE_guard_left _ _ _ (loop_decrement_valid (a + 1) b bound)]
  rw [bindE_modify_left, loop_decrement_update (a + 1) b bound, l2_gets_eq]

private def strengthenWhileTest (result : Except Bool Bool) (state : Globals) : Prop :=
  match result with
  | .error _ => False
  | .ok value => (fun locals state =>
      propositionBool (splitLoopTest locals state) = true) value state

private def strengthenWhileBody : Except Bool Bool →
    Nondet Globals (Except Bool Bool) :=
  whileLoopEBody fun locals => strengthenLoopBody.denote (((), false), locals)

private def generatedLoop : L2.L2Program Globals Bool Bool :=
  whileLoop strengthenWhileTest strengthenWhileBody (Except.ok false)

private theorem generated_loop_is_l2 :
    L2.while (fun locals state =>
        propositionBool (splitLoopTest locals state) = true)
      (fun locals => strengthenLoopBody.denote (((), false), locals)) false [] =
      generatedLoop := by
  unfold L2.while whileLoopE generatedLoop strengthenWhileTest strengthenWhileBody
  apply congrArg (fun test => whileLoop test
    (whileLoopEBody fun locals => strengthenLoopBody.denote (((), false), locals))
    (Except.ok false))
  funext result state
  cases result <;> rfl

private theorem generated_loop_test_zero (a : Int) :
    ¬ propositionBool (splitLoopTest false (loopGlobals a 0)) = true := by
  rw [propositionBool_exact]
  simp [splitLoopTest, assemble_loop_globals, plus2Condition_zero]

private theorem generated_loop_test_succ (a : Int) (b : Nat)
    (bound : b + 1 < 2 ^ 32) :
    propositionBool (splitLoopTest false (loopGlobals a (b + 1))) = true := by
  rw [propositionBool_exact]
  simp [splitLoopTest, assemble_loop_globals, plus2Condition_succ, bound]

private theorem generated_loop_exact (originalA originalB currentA : Int)
    (currentB : Nat) (bound : currentB < 2 ^ 32)
    (invariant : plus2Invariant originalA originalB currentA (Int.ofNat currentB)) :
    generatedLoop (loopGlobals currentA currentB) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals (currentA + Int.ofNat currentB) 0) := by
  induction currentB using Nat.strongRecOn generalizing currentA with
  | ind currentB induction =>
      rcases currentB with _ | currentB
      · apply behavior_ext
        · funext result
          apply propext
          constructor
          · intro member
            change WhileResult _ _ (some (Except.ok false, loopGlobals currentA 0))
                (some result) at member
            cases member with
            | stop _ => simp [Zag.Lang.AutoCorres.returnOk,
                Zag.Lang.AutoCorres.pure]
            | step holds _ _ => exact False.elim (generated_loop_test_zero currentA holds)
          · intro member
            have equality : result = (Except.ok false, loopGlobals currentA 0) := by
              simpa [Zag.Lang.AutoCorres.returnOk,
                Zag.Lang.AutoCorres.pure] using member
            cases equality
            exact WhileResult.stop (generated_loop_test_zero currentA)
        · apply propext
          constructor
          · rintro (finite | notTerminates)
            · change WhileResult _ _ (some (Except.ok false,
                loopGlobals currentA 0)) none at finite
              cases finite with
              | bodyFailure holds _ => exact generated_loop_test_zero currentA holds
              | step holds _ _ => exact generated_loop_test_zero currentA holds
            · exact notTerminates (.stop (generated_loop_test_zero currentA))
          · intro failed
            exact False.elim failed

      · have testHolds := generated_loop_test_succ currentA currentB bound
        have bodyExact := strengthen_loop_body_exact currentA currentB bound
        have nextInvariant := plus2_invariant_preserved originalA originalB currentA
          currentB invariant
        have decreases : plus2Variant currentB < plus2Variant (currentB + 1) :=
          plus2_variant_decreases currentB
        have restExact := induction currentB (by exact decreases)
          (currentA := currentA + 1) (by omega) nextInvariant
        have finalStateEq :
            loopGlobals (currentA + 1 + Int.ofNat currentB) 0 =
              loopGlobals (currentA + Int.ofNat (currentB + 1)) 0 := by
          have sumEq : currentA + 1 + Int.ofNat currentB =
              currentA + Int.ofNat (currentB + 1) := by
            simp [Int.natCast_add]
            omega
          rw [sumEq]
        apply behavior_ext
        · funext result
          apply propext
          constructor
          · intro member
            change WhileResult _ _ (some (Except.ok false,
                loopGlobals currentA (currentB + 1))) (some result) at member
            cases member with
            | stop stopped => exact False.elim (stopped testHolds)
            | step _ bodyMember rest =>
                simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                rw [bodyExact] at bodyMember
                simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                have restMember : result ∈
                    (generatedLoop (loopGlobals (currentA + 1) currentB)).results := rest
                rw [restExact] at restMember
                rw [← finalStateEq]
                exact restMember
          · intro member
            have expectedMember :
                (Except.ok false, loopGlobals (currentA + 1 + Int.ofNat currentB) 0) ∈
                  (generatedLoop (loopGlobals (currentA + 1) currentB)).results := by
              rw [restExact]
              exact mem_returnOk.mpr ⟨rfl, rfl⟩
            rcases result with ⟨result, post⟩
            change (result, post) = (Except.ok false,
              loopGlobals (currentA + Int.ofNat (currentB + 1)) 0) at member
            cases member
            change WhileResult _ _ (some (Except.ok false,
              loopGlobals currentA (currentB + 1))) (some _)
            exact @WhileResult.step Globals (Except Bool Bool)
              strengthenWhileTest strengthenWhileBody
              (Except.ok false) (loopGlobals currentA (currentB + 1))
              (Except.ok false) (loopGlobals (currentA + 1) currentB)
              (some (Except.ok false,
                loopGlobals (currentA + Int.ofNat (currentB + 1)) 0))
              testHolds (by
                simp only [strengthenWhileBody, whileLoopEBody]
                rw [bodyExact]
                exact mem_returnOk.mpr ⟨rfl, rfl⟩)
              (by
                change WhileResult _ _ (some (Except.ok false,
                  loopGlobals (currentA + 1) currentB)) (some _)
                  at expectedMember
                rw [finalStateEq] at expectedMember
                exact expectedMember)
        · apply propext
          constructor
          · rintro (finite | notTerminates)
            · change WhileResult _ _ (some (Except.ok false,
                loopGlobals currentA (currentB + 1))) none at finite
              cases finite with
              | bodyFailure _ bodyFailed =>
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyFailed
                  rw [bodyExact] at bodyFailed
                  exact (returnOk_not_failed false _ bodyFailed)
              | step _ bodyMember rest =>
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                  rw [bodyExact] at bodyMember
                  simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                  rcases bodyMember with ⟨rfl, rfl⟩
                  have restFailed :
                      (generatedLoop (loopGlobals (currentA + 1) currentB)).failed :=
                    Or.inl rest
                  rw [restExact] at restFailed
                  exact returnOk_not_failed false _ restFailed
            · apply notTerminates
              exact @WhileTerminates.step Globals (Except Bool Bool)
                strengthenWhileTest strengthenWhileBody
                (Except.ok false) (loopGlobals currentA (currentB + 1)) testHolds
                (by
                  intro next nextState bodyMember
                  simp only [strengthenWhileBody, whileLoopEBody] at bodyMember
                  rw [bodyExact] at bodyMember
                  simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                  rcases bodyMember with ⟨rfl, rfl⟩
                  exact Classical.byContradiction fun restDoesNotTerminate => by
                    have restFailed :
                        (generatedLoop (loopGlobals (currentA + 1) currentB)).failed :=
                      Or.inr restDoesNotTerminate
                    rw [restExact] at restFailed
                    exact returnOk_not_failed false _ restFailed)
          · intro failed
            exact False.elim failed

private def resultGlobals (value : Int) : Globals :=
  model.projectGlobals
    ((plus2State value 0).returnValue u32 (u32.cast value))

private theorem loop_result_valid (value : Int) :
    splitValid (.variable u32 1) false (loopGlobals value 0) := by
  refine ⟨u32.cast value, ?_⟩
  simp [assemble_loop_globals, Expr.eval, plus2State_read_a]

private theorem set_loop_result (value : Int) :
    setResult false (loopGlobals value 0) = resultGlobals value := by
  unfold setResult expressionValue resultGlobals loopGlobals
  rw [show model.assemble false (model.projectGlobals (plus2State value 0)) =
    plus2State value 0 by rfl]
  simp [Expr.eval, plus2State_read_a]

private theorem generated_catch_exact (a : Int) (b : Nat)
    (bound : b < 2 ^ 32) :
    strengthenCatchBody.denote ((), false) (loopGlobals a b) =
      Zag.Lang.AutoCorres.throw true
        (resultGlobals (a + Int.ofNat b)) := by
  have loopExact := generated_loop_exact a (Int.ofNat b) a b bound
    (plus2_invariant_initial a b)
  simp only [strengthenCatchBody, TypeStrengthen.Kernel.Source.Term.denote,
    L2.seq]
  rw [generated_loop_is_l2]
  rw [bindE_replace_returnOk _ _ _ _ loopExact]
  rw [bindE_guard_left _ _ _ (loop_result_valid (a + Int.ofNat b))]
  rw [bindE_modify_left, set_loop_result]
  rfl

private theorem generated_nondet_catch_exact (a : Int) (b : Nat)
    (bound : b < 2 ^ 32) :
    TypeStrengthen.Kernel.nondetCatch
        (strengthenCatchBody.denote ((), false))
        (fun exception => Zag.Lang.AutoCorres.pure exception)
        (loopGlobals a b) =
      Zag.Lang.AutoCorres.pure true
        (resultGlobals (a + Int.ofNat b)) := by
  unfold TypeStrengthen.Kernel.nondetCatch
  exact bind_replace_pure _ _ _ _ (generated_catch_exact a b bound)

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

private theorem generated_final_exact (a : Int) (b : Nat)
    (bound : b < 2 ^ 32) :
    generatedFinalNondet (loopGlobals a b) =
      Zag.Lang.AutoCorres.pure
        ((readResult (resultGlobals (a + Int.ofNat b))).toNat)
        (resultGlobals (a + Int.ofNat b)) := by
  unfold generatedFinalNondet
  rw [bind_pure_left_at]
  rw [bind_replace_pure _ _ _ _ (generated_nondet_catch_exact a b bound)]
  rw [bind_guard_left _ _ _ (show splitReturned true
    (resultGlobals (a + Int.ofNat b)) by rfl)]
  rfl

private theorem input_result_globals (a b : Word32) :
    resultGlobals (Int.ofNat a.toNat + Int.ofNat b.toNat) =
      model.projectGlobals (plus2Result a b) := by
  rfl

private theorem input_result_value (a b : Word32) :
    (readResult
      (resultGlobals (Int.ofNat a.toNat + Int.ofNat b.toNat))).toNat =
        (a + b).toNat := by
  rw [input_result_globals]
  change (BitVec.ofInt 32 (plus2Result a b).result).toNat = (a + b).toNat
  rw [plus2_success_is_wrapping_add]

/-- Exact generated TypeStrengthen endpoint behavior for every pair of u32 inputs. -/
theorem final_target_exact (a b : Word32) :
    finalTarget (initialGlobals a b) =
      Zag.Lang.AutoCorres.returnOk (ε := Unit) (a + b).toNat
        (model.projectGlobals (plus2Result a b)) := by
  rw [final_target_is_generated, initial_globals_eq]
  rw [liftE_replace_pure _ _ _
    (generated_final_exact (Int.ofNat a.toNat) b.toNat b.isLt)]
  rw [input_result_value, input_result_globals]

/-- The generated final target is total and has no failure branch on any u32 inputs. -/
theorem final_target_no_failure (a b : Word32) :
    ¬(finalTarget (initialGlobals a b)).failed := by
  rw [final_target_exact]
  exact returnOk_not_failed _ _

theorem word_final_target_no_failure (a b : Word32) :
    ¬(wordFinalTarget (initialGlobals a b)).failed := by
  have finalNoFail := final_target_no_failure a b
  have wordCallNoFail : ¬(L2.call (Exception := Unit)
      (wordCertificate.target.denote ()) (initialGlobals a b)).failed := by
    rw [type_strengthen_consumes_word_endpoint]
    exact finalNoFail
  have wordNoFail : ¬((wordCertificate.target.denote ())
      (initialGlobals a b)).failed := fun failed =>
    wordCallNoFail (TypeStrengthen.failed_call.mpr (Or.inl failed))
  have correspondence := word_consumes_heap_endpoint (initialGlobals a b)
    ⟨True.intro, wordNoFail⟩
  rw [wordFinalTarget, TypeStrengthen.failed_call]
  rintro (failed | ⟨exception, post, member⟩)
  · exact correspondence.2 failed
  · have mapped := correspondence.1 (Except.error exception) post member
    exact wordCallNoFail (TypeStrengthen.failed_call.mpr
      (Or.inr ⟨exception, post, mapped⟩))

theorem final_preserves_arbitrary_wrapping_result (a b : Word32) :
    (Except.ok (a + b).toNat, model.projectGlobals (plus2Result a b)) ∈
      (finalTarget (initialGlobals a b)).results := by
  rw [final_target_exact]
  exact mem_returnOk.mpr ⟨rfl, rfl⟩

/-- Generated-endpoint counterpart of upstream `plus2_correct`. -/
theorem plus2_correct (a b : Word32) :
    ∀ result post,
      (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
        result = (a + b).toNat := by
  intro result post member
  rw [final_target_exact, mem_returnOk] at member
  exact member.1

theorem word_plus2_correct (a b : Word32) :
    ∀ result post,
      (Except.ok result, post) ∈
          (wordFinalTarget (initialGlobals a b)).results →
        result = a + b := by
  intro result post member
  have finalNoFail := final_target_no_failure a b
  have wordCallNoFail : ¬(L2.call (Exception := Unit)
      (wordCertificate.target.denote ()) (initialGlobals a b)).failed := by
    rw [type_strengthen_consumes_word_endpoint]
    exact finalNoFail
  have wordNoFail : ¬((wordCertificate.target.denote ())
      (initialGlobals a b)).failed := fun failed =>
    wordCallNoFail (TypeStrengthen.failed_call.mpr (Or.inl failed))
  have correspondence := word_consumes_heap_endpoint (initialGlobals a b)
    ⟨True.intro, wordNoFail⟩
  have projectedMember : (Except.ok result, post) ∈
      (projectedL2 (initialGlobals a b)).results := by
    exact TypeStrengthen.mem_call_ok.mp member
  have mapped := correspondence.1 (Except.ok result) post projectedMember
  have finalMember : (Except.ok result.toNat, post) ∈
      (finalTarget (initialGlobals a b)).results := by
    change (Except.ok result.toNat, post) ∈
      (TypeStrengthen.Kernel.embed .nondet strengthenCertificate.target.denote
        (initialGlobals a b)).results
    rw [← type_strengthen_consumes_word_endpoint]
    exact TypeStrengthen.mem_call_ok.mpr mapped
  have naturalEquality := plus2_correct a b result.toNat post finalMember
  exact BitVec.toNat_inj.mp naturalEquality

/-- Generated-endpoint counterpart of upstream `plus2_is_plus`. -/
theorem plus2_is_plus (a b : Word32) :
    ∀ result post,
      (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
        result = (BitVec.ofInt 32
          (plusResult (Int.ofNat a.toNat) (Int.ofNat b.toNat)).result).toNat := by
  intro result post member
  have sourceEqualsPlus :=
    Zag.Test.AutoCorres.CParser.ScalarSimpl.plus2_is_plus a b
  have sumEqualsPlus : a + b = BitVec.ofInt 32
      (plusResult (Int.ofNat a.toNat) (Int.ofNat b.toNat)).result :=
    (plus2_success_is_wrapping_add a b).symm.trans sourceEqualsPlus
  exact (plus2_correct a b result post member).trans
    (congrArg BitVec.toNat sumEqualsPlus)

/-- Generated-endpoint total validity, matching upstream `plus2_valid`. -/
theorem plus2_valid (a b : Word32) :
    ¬(finalTarget (initialGlobals a b)).failed ∧
      ∀ result post,
        (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
          result = (a + b).toNat :=
  ⟨final_target_no_failure a b, plus2_correct a b⟩

theorem source_total_no_failure_connected (a b : Word32) :
    Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
        plus2Certificate.rawBody plus2.returnType (plus2Initial a b)
          (.success (plus2Result a b)) ∧
      ¬Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
        plus2Certificate.rawBody plus2.returnType (plus2Initial a b)
          .undefinedBehavior :=
  plus2_total_no_failure a b

theorem plus2_end_to_end (a b : Word32) :
    (Raw.FunctionExec plus2Certificate.program "plus2" plus2Certificate.functionInfo
          plus2Certificate.rawBody plus2.returnType (plus2Initial a b)
            (.success (plus2Result a b)) ∧
        ¬Raw.FunctionExec plus2Certificate.program "plus2"
          plus2Certificate.functionInfo plus2Certificate.rawBody plus2.returnType
          (plus2Initial a b) .undefinedBehavior) ∧
      ¬(finalTarget (initialGlobals a b)).failed ∧
        (Except.ok (a + b).toNat, model.projectGlobals (plus2Result a b)) ∈
          (finalTarget (initialGlobals a b)).results :=
  ⟨source_total_no_failure_connected a b,
    final_target_no_failure a b,
    final_preserves_arbitrary_wrapping_result a b⟩

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.Plus2Pipeline
