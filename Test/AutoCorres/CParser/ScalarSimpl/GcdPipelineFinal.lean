import Test.AutoCorres.CParser.ScalarSimpl.GcdPipelineWord
import Test.AutoCorres.CParser.ScalarSimpl.GcdCorrectnessModel
import Test.AutoCorres.CParser.ScalarSimpl.MultByAddPipelineFinal

/-! # Fixture-derived `gcd` through nondet TypeStrengthen and final `ac_corres` -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

abbrev DeclarationContext (Prefix : Type) := (Prefix × Bool) × Unit

def propositionBool (proposition : Prop) : Bool :=
  @ite Bool proposition (Classical.propDecidable _) true false

theorem propositionBool_exact (proposition : Prop) :
    propositionBool proposition = true ↔ proposition := by
  simp [propositionBool]

def strengthenCBody (Prefix : Type) :
    TypeStrengthen.Kernel.Source.Term (DeclarationContext Prefix × Bool)
      Globals Bool Bool :=
  .seq (.exactGuard fun input state => splitValid gcdCondition input.2 state)
    (.seq (.exactGuard fun input state => splitValid (.variable u32 1) input.1.2 state)
      (.seq (.modify fun input state => updateExpression 3 u32 (.variable u32 1)
          input.1.1.2 state)
        (.seq (.exactGuard fun input state => splitValid gcdRemainder
            input.1.1.1.2 state)
          (.seq (.modify fun input state => updateExpression 1 u32 gcdRemainder
              input.1.1.1.1.2 state)
            (.seq (.exactGuard fun input state => splitValid (.variable u32 3)
                input.1.1.1.1.1.2 state)
              (.seq (.modify fun input state => updateExpression 2 u32 (.variable u32 3)
                  input.1.1.1.1.1.1.2 state)
                (.pure (fun input => input.1.1.1.1.1.1.1.2) [])))))))

def strengthenCatchBody (Prefix : Type) :
    TypeStrengthen.Kernel.Source.Term (Prefix × Bool) Globals Bool Bool :=
  .seq (.modify fun input state => clearSlot 3 input.2 state)
    (.seq
      (.while (fun _ locals state => propositionBool (splitLoopTest locals state))
        (strengthenCBody Prefix) (fun input => input.1.2) [])
      (.seq (.exactGuard fun input state => splitValid (.variable u32 2) input.2 state)
        (.seq (.modify fun input state => setResult input.1.2 state)
          (.throw (fun _ => true) []))))

def strengthenHandler (Prefix : Type) :
    TypeStrengthen.Kernel.Source.Term ((Prefix × Bool) × Bool) Globals Bool Bool :=
  .pure (fun input => input.2) []

def strengthenProjectedRest (Prefix : Type) :
    TypeStrengthen.Kernel.Source.Term ((Prefix × Bool) × Bool) Globals Bool Nat :=
  .seq (.exactGuard fun input state => splitReturned input.2 state)
    (.gets (fun _ state => WordAbstract.Kernel.abstractUnsignedInt 32 (readResult state)) [])

def strengthenProjected (Prefix : Type) :
    TypeStrengthen.Kernel.Source.Term Prefix Globals Bool Nat :=
  .seq (.pure (fun _ => false) [])
    (.seq (.catchHandlers (strengthenCatchBody Prefix) (strengthenHandler Prefix))
      (strengthenProjectedRest Prefix))

abbrev BeforeProjected := (Unit × (Nat × Nat)) × Unit
abbrev ProjectedContext := BeforeProjected × Unit
abbrev BeforeGcdLoop := (ProjectedContext × Nat) × Unit
abbrev GcdNatBodyContext := BeforeGcdLoop × (Nat × Nat)

def mappedNatPair (pair : Nat × Nat) : Nat × Nat :=
  (WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.2) %
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.1),
    WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.1))

def reabstractNatPair (pair : Nat × Nat) : Nat × Nat :=
  (WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.1),
    WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.2))

def strengthenGcdBody :
    TypeStrengthen.Kernel.Source.Term GcdNatBodyContext
      Globals Bool (Nat × Nat) :=
  .seq (.exactGuard fun input _ =>
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat input.2.2) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat input.2.1) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat input.2.1) ≠ 0)
    (.seq (.pure (fun input => mappedNatPair input.1.2) [])
      (.seq (.exactGuard fun input _ =>
          input.2.1 < 2 ^ 32 /\ input.2.2 < 2 ^ 32)
        (.pure (fun input => input.1.2) [])))

def strengthenSource : TypeStrengthen.Kernel.Source.Closed Globals Bool Nat :=
  .seq (.gets (fun _ state =>
      (WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).1,
        WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).2)) [])
    (.seq (.exactGuard fun input _ => input.2.1 < 2 ^ 32 /\ input.2.2 < 2 ^ 32)
      (.seq (.exactGuard fun input _ => canonicalPair
          (Int.ofNat input.1.2.1, Int.ofNat input.1.2.2))
        (.seq (strengthenProjected (BeforeProjected × Unit))
          (.seq (.exactGuard fun input _ => input.2 < 2 ^ 32 /\
              (reabstractNatPair input.1.1.1.2).1 < 2 ^ 32 /\
                (reabstractNatPair input.1.1.1.2).2 < 2 ^ 32)
            (.seq
          (.while (fun _ pair _ => propositionBool (pair.1 ≠ 0))
            strengthenGcdBody
              (fun input => reabstractNatPair input.1.1.1.1.2) ["gcd"])
              (.seq (.exactGuard fun input _ =>
                  input.2.1 < 2 ^ 32 /\ input.2.2 < 2 ^ 32)
                (.seq (.exactGuard fun input _ =>
                    Int.ofNat input.1.2.2 = Int.ofNat input.1.1.1.2)
                  (.pure (fun input =>
                    WordAbstract.Kernel.abstractUnsignedInt 32
                      (Int.ofNat input.1.1.2.2)) []))))))))

def strengthenSupported : TypeStrengthen.Kernel.Supported .nondet strengthenSource :=
  .nondetSeq .nondetRead
    (.nondetSeq .nondetExactGuard
      (.nondetSeq .nondetExactGuard
        (.nondetSeq
          (.nondetSeq .nondetValue
            (.nondetSeq (.nondetCatchHandlers .nondetValue)
              (.nondetSeq .nondetExactGuard .nondetRead)))
          (.nondetSeq .nondetExactGuard
            (.nondetSeq
              (.nondetWhile
                (.nondetSeq .nondetExactGuard
                  (.nondetSeq .nondetValue
                    (.nondetSeq .nondetExactGuard .nondetValue))))
              (.nondetSeq .nondetExactGuard
                (.nondetSeq .nondetExactGuard .nondetValue)))))))

def strengthenCertificate := ML.TypeStrengthen.strengthenClosed strengthenSupported

private theorem loop_test_function :
    (fun pair state => propositionBool (pair.1 ≠ 0) = true) =
      (fun pair : Nat × Nat => fun _ : Globals => pair.1 ≠ 0) := by
  funext pair state
  exact propext (propositionBool_exact _)

private theorem c_loop_test_function :
    (fun locals state => propositionBool (splitLoopTest locals state) = true) =
      splitLoopTest := by
  funext locals state
  exact propext (propositionBool_exact _)

private theorem simplified_c_body (Prefix : Type)
    (argument : DeclarationContext Prefix) (locals : Bool) :
    (strengthenCBody Prefix).denote (argument, locals) = (exactLoopBody locals).denote := by
  simp only [strengthenCBody, TypeStrengthen.Kernel.Source.Term.denote,
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
    ML.WordAbstract.Expr.transform, wordSource, wordProjectedSource, wordLveSource,
    wordCatchBody, wordReturnTail, wordGuard, wordSkip, wordGlobalUpdate,
    gcdPairLoop, gcdPairBody, strengthenSource, strengthenProjected,
    strengthenCatchBody, strengthenHandler, strengthenProjectedRest,
    strengthenGcdBody]
  simp only [WordAbstract.Kernel.Target.Syntax.denote,
    WordAbstract.Kernel.Target.Expr.eval,
    TypeStrengthen.Kernel.Source.Term.denote]
  rw [c_loop_test_function, loop_test_function]
  simp only [WordAbstract.Kernel.ExactValueType.type,
    WordAbstract.Kernel.typeMap, WordAbstract.Kernel.TypeMap.concretize,
    WordAbstract.Kernel.TypeMap.abstract,
    WordAbstract.Kernel.valid_typ_abs_fn_unsignedInt,
    WordAbstract.valid_typ_abs_fn_prod,
    WordAbstract.valid_typ_abs_fn_id, id_eq]
  simp [PlusPipeline.l2_seq_assoc, PlusPipeline.l2_seq_true_guard,
    PlusPipeline.l2_seq_gets, PlusPipeline.l2_seq_throw,
    simplified_c_body, mappedNatPair, reabstractNatPair,
    gcdPairTest,
    WordAbstract.Kernel.abstractUnsignedInt,
    WordAbstract.Kernel.intUnsignedCanonical]

theorem type_strengthen_consumes_word_endpoint :
    L2.call (Exception := Unit) (wordCertificate.target.denote ()) =
      TypeStrengthen.Kernel.embed (Exception := Unit) .nondet
        strengthenCertificate.target.denote := by
  rw [word_to_strengthen_call_exact]
  exact strengthenCertificate.exact Unit

def finalTarget : L2.L2Program Globals Unit Nat :=
  TypeStrengthen.Kernel.embed .nondet strengthenCertificate.target.denote

def finalChain : ChainCertificate
    (L2State := Globals) (L2Exception := Bool) (L2Result := Int)
    (HLState := Globals) (WAException := Bool)
    false emptyEnvironment gcdFunction.command finalTarget :=
  { stateProjectL2 := model.projectGlobals
    returnExtractL2 := fun state => readResult (model.projectGlobals state)
    exceptionExtractL2 := model.projectLocals
    preconditionL2 := fun state => model.projectLocals state = false
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := WordAbstract.Kernel.abstractUnsignedInt 32
    exceptionExtractWA := id
    l1 := generatedL1.denote
    l1Corres := fixtureSimplCertificate.corres
    l2 := projectedL2
    l2Corres := projectedL2Corres
    heapLifted := wordSource.denote ()
    heapLiftCorres := heapLiftCorres
    wordAbstracted := wordCertificate.target.denote ()
    wordAbstractCorres := word_consumes_heap_endpoint
    typeStrengthen := type_strengthen_consumes_word_endpoint }

theorem final_chain_endpoints :
    finalChain.l1 = generatedL1.denote /\
    finalChain.l2 = projectedL2 /\
    finalChain.heapLifted = wordSource.denote () /\
    finalChain.wordAbstracted = wordCertificate.target.denote () := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finalAcCorres :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => WordAbstract.Kernel.abstractUnsignedInt 32
        (readResult (model.projectGlobals state)))
      (fun state => model.projectLocals state = false)
      finalTarget gcdFunction.command := by
  simpa [finalChain, Function.comp_def] using finalChain.acCorres

def initialGlobals (a b : GcdWord32) : Globals :=
  model.projectGlobals (gcdInitial a b)

theorem initial_locals (a b : GcdWord32) :
    model.projectLocals (gcdInitial a b) = false := by
  simp [gcdInitial, gcd_is_exact_resolved_function, expectedGcd,
    Function.enter, model, Plus2Pipeline.model, State.write, State.clear]

theorem initial_readPair (a b : GcdWord32) :
    readPair (initialGlobals a b) = pairOfWords a b := by
  apply Prod.ext
  · simp [readPair, initialGlobals, gcdInitial, gcd_is_exact_resolved_function,
      expectedGcd, Function.enter, model, Plus2Pipeline.model, pairOfWords,
      State.write, State.clear]
    exact u32_cast_nat a.toNat a.isLt
  · simp [readPair, initialGlobals, gcdInitial, gcd_is_exact_resolved_function,
      expectedGcd, Function.enter, model, Plus2Pipeline.model, pairOfWords,
      State.write, State.clear]
    exact u32_cast_nat b.toNat b.isLt

theorem initial_pair_canonical (a b : GcdWord32) :
    canonicalPair (readPair (initialGlobals a b)) := by
  rw [initial_readPair]
  unfold canonicalPair WordAbstract.Kernel.intUnsignedCanonical pairOfWords
  exact ⟨⟨by simp, Int.ofNat_lt.2 a.isLt⟩,
    ⟨by simp, Int.ofNat_lt.2 b.isLt⟩⟩

private def loopGlobals (a b c : GcdWord32) : Globals :=
  model.projectGlobals (gcdABCState a b c)

private theorem assemble_loop_globals (a b c : GcdWord32) :
    model.assemble false (loopGlobals a b c) = gcdABCState a b c := by
  rfl

private theorem c_condition_valid (a b c : GcdWord32) (nonzero : a ≠ 0) :
    splitValid gcdCondition false (loopGlobals a b c) := by
  exact ⟨1, by
    change gcdCondition.eval (model.assemble false (loopGlobals a b c)) = some 1
    rw [assemble_loop_globals]
    exact gcd_condition_nonzero a b c nonzero⟩

private theorem c_a_valid (a b c : GcdWord32) :
    splitValid (.variable u32 1) false (loopGlobals a b c) := by
  exact ⟨Int.ofNat a.toNat, by
    change (Expr.variable u32 1).eval
      (model.assemble false (loopGlobals a b c)) = _
    rw [assemble_loop_globals]
    exact gcdABC_read_a a b c⟩

private theorem c_remainder_valid (a b c : GcdWord32) (nonzero : a ≠ 0) :
    splitValid gcdRemainder false (loopGlobals a b c) := by
  exact ⟨Int.ofNat (b % a).toNat, by
    change gcdRemainder.eval (model.assemble false (loopGlobals a b c)) = _
    rw [assemble_loop_globals]
    exact gcd_remainder_eval a b c nonzero⟩

private theorem c_c_valid (a b c : GcdWord32) :
    splitValid (.variable u32 3) false (loopGlobals a b c) := by
  exact ⟨Int.ofNat c.toNat, by
    change (Expr.variable u32 3).eval
      (model.assemble false (loopGlobals a b c)) = _
    rw [assemble_loop_globals]
    exact gcdABC_read_c a b c⟩

private theorem update_c (a b c : GcdWord32) :
    updateExpression 3 u32 (.variable u32 1) false (loopGlobals a b c) =
      loopGlobals a b a := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue loopGlobals
  unfold model
  rw [show Plus2Pipeline.model.assemble false
      (Plus2Pipeline.model.projectGlobals (gcdABCState a b c)) = gcdABCState a b c by rfl]
  rw [show (Expr.variable u32 1).eval (gcdABCState a b c) =
      some (Int.ofNat a.toNat) from gcdABC_read_a a b c,
    Option.getD_some, gcdABC_set_c]

private theorem update_a (a b c : GcdWord32) (nonzero : a ≠ 0) :
    updateExpression 1 u32 gcdRemainder false (loopGlobals a b c) =
      loopGlobals (b % a) b c := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue loopGlobals
  unfold model
  rw [show Plus2Pipeline.model.assemble false
      (Plus2Pipeline.model.projectGlobals (gcdABCState a b c)) = gcdABCState a b c by rfl]
  rw [gcd_remainder_eval a b c nonzero, Option.getD_some, gcdABC_set_a]

private theorem update_b (a b c : GcdWord32) :
    updateExpression 2 u32 (.variable u32 3) false (loopGlobals a b c) =
      loopGlobals a c c := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue loopGlobals
  unfold model
  rw [show Plus2Pipeline.model.assemble false
      (Plus2Pipeline.model.projectGlobals (gcdABCState a b c)) = gcdABCState a b c by rfl]
  rw [show (Expr.variable u32 3).eval (gcdABCState a b c) =
      some (Int.ofNat c.toNat) from gcdABC_read_c a b c,
    Option.getD_some, gcdABC_set_b]

private theorem strengthen_c_body_exact (Prefix : Type)
    (argument : DeclarationContext Prefix) (a b c : GcdWord32)
    (nonzero : a ≠ 0) :
    (strengthenCBody Prefix).denote (argument, false) (loopGlobals a b c) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals (b % a) a a) := by
  simp only [strengthenCBody, TypeStrengthen.Kernel.Source.Term.denote, L2.seq]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_condition_valid a b c nonzero)]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_a_valid a b c)]
  rw [Plus2Pipeline.bindE_modify_left, update_c]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_remainder_valid a b a nonzero)]
  rw [Plus2Pipeline.bindE_modify_left, update_a a b a nonzero]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_c_valid (b % a) b a)]
  rw [Plus2Pipeline.bindE_modify_left, update_b (b % a) b a]
  exact Plus2Pipeline.l2_gets_eq _ _ _

private def cWhileTest (result : Except Bool Bool) (state : Globals) : Prop :=
  match result with
  | .error _ => False
  | .ok value => propositionBool (splitLoopTest value state) = true

private def cWhileBody (Prefix : Type) (argument : DeclarationContext Prefix) :
    Except Bool Bool -> Nondet Globals (Except Bool Bool) :=
  whileLoopEBody fun locals => (strengthenCBody Prefix).denote (argument, locals)

private def generatedCLoop (Prefix : Type) (argument : DeclarationContext Prefix) :
    L2.L2Program Globals Bool Bool :=
  whileLoop cWhileTest (cWhileBody Prefix argument) (.ok false)

private theorem c_loop_is_l2 (Prefix : Type) (argument : DeclarationContext Prefix) :
    L2.while (fun locals state => propositionBool (splitLoopTest locals state) = true)
      (fun locals => (strengthenCBody Prefix).denote (argument, locals)) false ["c"] =
      generatedCLoop Prefix argument := by
  unfold L2.while whileLoopE generatedCLoop cWhileTest cWhileBody
  apply congrArg (fun test => whileLoop test
    (whileLoopEBody fun locals => (strengthenCBody Prefix).denote (argument, locals))
    (.ok false))
  funext result state
  cases result <;> rfl

private theorem c_test_zero (b c : GcdWord32) :
    ¬propositionBool (splitLoopTest false (loopGlobals 0 b c)) = true := by
  rw [propositionBool_exact]
  unfold splitLoopTest
  rw [assemble_loop_globals, gcd_condition_zero_abc]
  simp

private theorem c_test_nonzero (a b c : GcdWord32) (nonzero : a ≠ 0) :
    propositionBool (splitLoopTest false (loopGlobals a b c)) = true := by
  rw [propositionBool_exact]
  simp [splitLoopTest, assemble_loop_globals, gcd_condition_nonzero a b c nonzero]

def gcdFinalC : GcdWord32 -> GcdWord32 -> GcdWord32 -> GcdWord32
  | a, b, c => if a = 0 then c else gcdFinalC (b % a) a a
termination_by a => a.toNat
decreasing_by exact gcd_variant_strictly_decreases a b (by assumption)

set_option maxHeartbeats 2000000 in
private theorem generated_c_loop_exact (Prefix : Type)
    (argument : DeclarationContext Prefix) (a b c : GcdWord32) :
    generatedCLoop Prefix argument (loopGlobals a b c) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals 0 (gcdWord a b) (gcdFinalC a b c)) := by
  induction a, b using gcdWord.induct generalizing c with
  | case1 b =>
      apply Plus2Pipeline.behavior_ext
      · funext outcome
        apply propext
        constructor
        · intro member
          change WhileResult _ _ (some (Except.ok false, loopGlobals 0 b c))
              (some outcome) at member
          cases member with
          | stop _ => simp [gcdWord, gcdFinalC, Zag.Lang.AutoCorres.returnOk,
              Zag.Lang.AutoCorres.pure]
          | step holds _ _ => exact False.elim (c_test_zero b c holds)
        · intro member
          have equality : outcome = (Except.ok false, loopGlobals 0 b c) := by
            simpa [gcdWord, gcdFinalC, Zag.Lang.AutoCorres.returnOk,
              Zag.Lang.AutoCorres.pure] using member
          cases equality
          exact WhileResult.stop (c_test_zero b c)
      · apply propext
        constructor
        · rintro (finite | notTerminates)
          · change WhileResult _ _ (some (Except.ok false, loopGlobals 0 b c)) none
              at finite
            cases finite with
            | bodyFailure holds _ => exact c_test_zero b c holds
            | step holds _ _ => exact c_test_zero b c holds
          · exact notTerminates (.stop (c_test_zero b c))
        · intro failed
          exact False.elim failed
  | case2 a b nonzero induction =>
      have testHolds := c_test_nonzero a b c nonzero
      have bodyExact := strengthen_c_body_exact Prefix argument a b c nonzero
      have restExact := induction a
      apply Plus2Pipeline.behavior_ext
      · funext outcome
        apply propext
        constructor
        · intro member
          change WhileResult _ _ (some (Except.ok false, loopGlobals a b c))
              (some outcome) at member
          cases member with
          | stop stopped => exact False.elim (stopped testHolds)
          | step _ bodyMember rest =>
              simp only [cWhileBody, whileLoopEBody] at bodyMember
              rw [bodyExact] at bodyMember
              simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
              rcases bodyMember with ⟨rfl, rfl⟩
              have restMember : outcome ∈
                  (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).results := rest
              rw [restExact] at restMember
              rw [gcdWord_nonzero a b nonzero]
              rw [show gcdFinalC a b c = gcdFinalC (b % a) a a by
                rw [gcdFinalC, if_neg nonzero]]
              exact restMember
        · intro member
          have expectedMember :
              (Except.ok false,
                loopGlobals 0 (gcdWord (b % a) a) (gcdFinalC (b % a) a a)) ∈
              (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).results := by
            rw [restExact]
            exact mem_returnOk.mpr ⟨rfl, rfl⟩
          rcases outcome with ⟨outcome, post⟩
          change (outcome, post) =
            (Except.ok false, loopGlobals 0 (gcdWord a b) (gcdFinalC a b c)) at member
          cases member
          exact @WhileResult.step Globals (Except Bool Bool)
            cWhileTest (cWhileBody Prefix argument)
            (.ok false) (loopGlobals a b c)
            (.ok false) (loopGlobals (b % a) a a)
            (some (.ok false, loopGlobals 0 (gcdWord a b) (gcdFinalC a b c)))
            testHolds (by
              simp only [cWhileBody, whileLoopEBody]
              rw [bodyExact]
              exact mem_returnOk.mpr ⟨rfl, rfl⟩)
            (by
              rw [gcdWord_nonzero a b nonzero]
              rw [show gcdFinalC a b c = gcdFinalC (b % a) a a by
                rw [gcdFinalC, if_neg nonzero]]
              exact expectedMember)
      · apply propext
        constructor
        · rintro (finite | notTerminates)
          · change WhileResult _ _ (some (Except.ok false, loopGlobals a b c)) none at finite
            cases finite with
            | bodyFailure _ bodyFailed =>
                simp only [cWhileBody, whileLoopEBody] at bodyFailed
                rw [bodyExact] at bodyFailed
                exact Plus2Pipeline.returnOk_not_failed false _ bodyFailed
            | step _ bodyMember rest =>
                simp only [cWhileBody, whileLoopEBody] at bodyMember
                rw [bodyExact] at bodyMember
                simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                have restFailed :
                    (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).failed :=
                  Or.inl rest
                rw [restExact] at restFailed
                exact Plus2Pipeline.returnOk_not_failed false _ restFailed
          · apply notTerminates
            exact @WhileTerminates.step Globals (Except Bool Bool)
              cWhileTest (cWhileBody Prefix argument)
              (.ok false) (loopGlobals a b c) testHolds (by
                intro next nextState bodyMember
                simp only [cWhileBody, whileLoopEBody] at bodyMember
                rw [bodyExact] at bodyMember
                simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                exact Classical.byContradiction fun restDoesNotTerminate => by
                  have restFailed :
                      (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).failed :=
                    Or.inr restDoesNotTerminate
                  rw [restExact] at restFailed
                  exact Plus2Pipeline.returnOk_not_failed false _ restFailed)
        · intro failed
          exact False.elim failed

private def initialLoopGlobals (a b : GcdWord32) : Globals :=
  model.projectGlobals (gcdABState a b)

private theorem clear_initial_globals (a b : GcdWord32) :
    clearSlot 3 false (initialGlobals a b) = initialLoopGlobals a b := by
  simp [clearSlot, initialGlobals, initialLoopGlobals, gcdInitial,
    gcd_is_exact_resolved_function, expectedGcd, Function.enter, model,
    Plus2Pipeline.model, gcdABState, State.clear, State.write]

private theorem initial_c_condition_eval (a b : GcdWord32) (nonzero : a ≠ 0) :
    gcdCondition.eval (gcdABState a b) = some 1 := by
  have castA := u32_cast_nat a.toNat a.isLt
  have positive : a.toNat ≠ 0 := by
    intro zero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using zero)
  have zeroS : s32.cast 0 = 0 := by native_decide
  have zeroU : u32.cast 0 = 0 := by native_decide
  have castA' : u32.cast (a.toNat : Int) = (a.toNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using castA
  simp [gcdCondition, Expr.eval, gcdAB_read_a, zeroS, zeroU]
  rw [castA']
  simpa using positive

private theorem initial_c_condition_valid (a b : GcdWord32) (nonzero : a ≠ 0) :
    splitValid gcdCondition false (initialLoopGlobals a b) := by
  exact ⟨1, initial_c_condition_eval a b nonzero⟩

private theorem initial_c_a_valid (a b : GcdWord32) :
    splitValid (.variable u32 1) false (initialLoopGlobals a b) := by
  exact ⟨Int.ofNat a.toNat, by
    change (Expr.variable u32 1).eval (gcdABState a b) = _
    exact gcdAB_read_a a b⟩

private theorem initial_update_c (a b : GcdWord32) :
    updateExpression 3 u32 (.variable u32 1) false (initialLoopGlobals a b) =
      loopGlobals a b a := by
  unfold updateExpression Plus2Pipeline.updateExpression
  unfold Plus2Pipeline.expressionValue initialLoopGlobals loopGlobals
  unfold model
  rw [show Plus2Pipeline.model.assemble false
      (Plus2Pipeline.model.projectGlobals (gcdABState a b)) = gcdABState a b by rfl]
  rw [show (Expr.variable u32 1).eval (gcdABState a b) =
      some (Int.ofNat a.toNat) from gcdAB_read_a a b,
    Option.getD_some, gcdAB_set_c]

private theorem strengthen_initial_c_body_exact (Prefix : Type)
    (argument : DeclarationContext Prefix) (a b : GcdWord32)
    (nonzero : a ≠ 0) :
    (strengthenCBody Prefix).denote (argument, false) (initialLoopGlobals a b) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false
        (loopGlobals (b % a) a a) := by
  simp only [strengthenCBody, TypeStrengthen.Kernel.Source.Term.denote, L2.seq]
  rw [Plus2Pipeline.bindE_guard_left _ _ _
    (initial_c_condition_valid a b nonzero)]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (initial_c_a_valid a b)]
  rw [Plus2Pipeline.bindE_modify_left, initial_update_c]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_remainder_valid a b a nonzero)]
  rw [Plus2Pipeline.bindE_modify_left, update_a a b a nonzero]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_c_valid (b % a) b a)]
  rw [Plus2Pipeline.bindE_modify_left, update_b (b % a) b a]
  exact Plus2Pipeline.l2_gets_eq _ _ _

private theorem initial_c_test_zero (b : GcdWord32) :
    ¬propositionBool (splitLoopTest false (initialLoopGlobals 0 b)) = true := by
  rw [propositionBool_exact]
  unfold splitLoopTest
  rw [show model.assemble false (initialLoopGlobals 0 b) = gcdABState 0 b by rfl,
    gcd_condition_zero]
  simp

private theorem initial_c_test_nonzero (a b : GcdWord32) (nonzero : a ≠ 0) :
    propositionBool (splitLoopTest false (initialLoopGlobals a b)) = true := by
  rw [propositionBool_exact]
  unfold splitLoopTest
  rw [show model.assemble false (initialLoopGlobals a b) = gcdABState a b by rfl]
  rw [initial_c_condition_eval a b nonzero]
  simp

private def cLoopFinalGlobals (a b : GcdWord32) : Globals :=
  if a = 0 then initialLoopGlobals a b
  else loopGlobals 0 (gcdWord a b) (gcdFinalC a b 0)

set_option maxHeartbeats 1000000 in
private theorem generated_initial_c_loop_exact (Prefix : Type)
    (argument : DeclarationContext Prefix) (a b : GcdWord32) :
    generatedCLoop Prefix argument (initialLoopGlobals a b) =
      Zag.Lang.AutoCorres.returnOk (ε := Bool) false (cLoopFinalGlobals a b) := by
  by_cases zero : a = 0
  · subst a
    apply Plus2Pipeline.behavior_ext
    · funext outcome
      apply propext
      constructor
      · intro member
        change WhileResult _ _ (some (Except.ok false, initialLoopGlobals 0 b))
            (some outcome) at member
        cases member with
        | stop _ => simpa [cLoopFinalGlobals, Zag.Lang.AutoCorres.returnOk,
            Zag.Lang.AutoCorres.pure]
        | step holds _ _ => exact False.elim (initial_c_test_zero b holds)
      · intro member
        have equality : outcome = (Except.ok false, initialLoopGlobals 0 b) := by
          simpa [cLoopFinalGlobals, Zag.Lang.AutoCorres.returnOk,
            Zag.Lang.AutoCorres.pure] using member
        cases equality
        exact WhileResult.stop (initial_c_test_zero b)
    · apply propext
      constructor
      · rintro (finite | notTerminates)
        · change WhileResult _ _ (some (Except.ok false, initialLoopGlobals 0 b)) none
            at finite
          cases finite with
          | bodyFailure holds _ => exact initial_c_test_zero b holds
          | step holds _ _ => exact initial_c_test_zero b holds
        · exact notTerminates (.stop (initial_c_test_zero b))
      · intro failed
        exact False.elim failed
  · have testHolds := initial_c_test_nonzero a b zero
    have bodyExact := strengthen_initial_c_body_exact Prefix argument a b zero
    have restExact := generated_c_loop_exact Prefix argument (b % a) a a
    apply Plus2Pipeline.behavior_ext
    · funext outcome
      apply propext
      constructor
      · intro member
        change WhileResult _ _ (some (Except.ok false, initialLoopGlobals a b))
            (some outcome) at member
        cases member with
        | stop stopped => exact False.elim (stopped testHolds)
        | step _ bodyMember rest =>
            simp only [cWhileBody, whileLoopEBody] at bodyMember
            rw [bodyExact] at bodyMember
            simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
            rcases bodyMember with ⟨rfl, rfl⟩
            have restMember : outcome ∈
                (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).results := rest
            rw [restExact] at restMember
            rw [cLoopFinalGlobals, if_neg zero, gcdWord_nonzero a b zero]
            rw [show gcdFinalC a b 0 = gcdFinalC (b % a) a a by
              rw [gcdFinalC, if_neg zero]]
            exact restMember
      · intro member
        have expectedMember :
            (Except.ok false,
              loopGlobals 0 (gcdWord (b % a) a) (gcdFinalC (b % a) a a)) ∈
            (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).results := by
          rw [restExact]
          exact mem_returnOk.mpr ⟨rfl, rfl⟩
        rcases outcome with ⟨outcome, post⟩
        change (outcome, post) =
          (Except.ok false, cLoopFinalGlobals a b) at member
        cases member
        exact @WhileResult.step Globals (Except Bool Bool)
          cWhileTest (cWhileBody Prefix argument)
          (.ok false) (initialLoopGlobals a b)
          (.ok false) (loopGlobals (b % a) a a)
          (some (.ok false, cLoopFinalGlobals a b))
          testHolds (by
            simp only [cWhileBody, whileLoopEBody]
            rw [bodyExact]
            exact mem_returnOk.mpr ⟨rfl, rfl⟩)
          (by
            rw [cLoopFinalGlobals, if_neg zero, gcdWord_nonzero a b zero]
            rw [show gcdFinalC a b 0 = gcdFinalC (b % a) a a by
              rw [gcdFinalC, if_neg zero]]
            exact expectedMember)
    · apply propext
      constructor
      · rintro (finite | notTerminates)
        · change WhileResult _ _ (some (Except.ok false, initialLoopGlobals a b)) none
            at finite
          cases finite with
          | bodyFailure _ bodyFailed =>
              simp only [cWhileBody, whileLoopEBody] at bodyFailed
              rw [bodyExact] at bodyFailed
              exact Plus2Pipeline.returnOk_not_failed false _ bodyFailed
          | step _ bodyMember rest =>
              simp only [cWhileBody, whileLoopEBody] at bodyMember
              rw [bodyExact] at bodyMember
              simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
              rcases bodyMember with ⟨rfl, rfl⟩
              have restFailed :
                  (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).failed :=
                Or.inl rest
              rw [restExact] at restFailed
              exact Plus2Pipeline.returnOk_not_failed false _ restFailed
        · apply notTerminates
          exact @WhileTerminates.step Globals (Except Bool Bool)
            cWhileTest (cWhileBody Prefix argument)
            (.ok false) (initialLoopGlobals a b) testHolds (by
              intro next nextState bodyMember
              simp only [cWhileBody, whileLoopEBody] at bodyMember
              rw [bodyExact] at bodyMember
              simp only [Zag.Lang.AutoCorres.returnOk, mem_pure] at bodyMember
              rcases bodyMember with ⟨rfl, rfl⟩
              exact Classical.byContradiction fun restDoesNotTerminate => by
                have restFailed :
                    (generatedCLoop Prefix argument (loopGlobals (b % a) a a)).failed :=
                  Or.inr restDoesNotTerminate
                rw [restExact] at restFailed
                exact Plus2Pipeline.returnOk_not_failed false _ restFailed)
      · intro failed
        exact False.elim failed

private theorem c_loop_final_b (a b : GcdWord32) :
    (Expr.variable u32 2).eval
        (model.assemble false (cLoopFinalGlobals a b)) =
      some (Int.ofNat (gcdWord a b).toNat) := by
  by_cases zero : a = 0
  · subst a
    simp only [cLoopFinalGlobals]
    change (Expr.variable u32 2).eval (gcdABState 0 b) = _
    simp [Expr.eval, gcdWord, gcdAB_read_b]
  · simp only [cLoopFinalGlobals, if_neg zero]
    change (Expr.variable u32 2).eval
      (gcdABCState 0 (gcdWord a b) (gcdFinalC a b 0)) = _
    exact gcdABC_read_b 0 (gcdWord a b) (gcdFinalC a b 0)

private theorem c_loop_result_valid (a b : GcdWord32) :
    splitValid (.variable u32 2) false (cLoopFinalGlobals a b) :=
  ⟨Int.ofNat (gcdWord a b).toNat, c_loop_final_b a b⟩

def cResultGlobals (a b : GcdWord32) : Globals :=
  setResult false (cLoopFinalGlobals a b)

set_option maxRecDepth 100000 in
private theorem c_result_value (a b : GcdWord32) :
    readResult (cResultGlobals a b) = Int.ofNat (gcdWord a b).toNat := by
  unfold cResultGlobals setResult readResult
  unfold expressionValue Plus2Pipeline.expressionValue model
  rw [show (Expr.variable u32 2).eval
      (Plus2Pipeline.model.assemble false (cLoopFinalGlobals a b)) =
        some (Int.ofNat (gcdWord a b).toNat) from c_loop_final_b a b,
    Option.getD_some]
  change u32.cast (Int.ofNat (gcdWord a b).toNat) = _
  exact u32_cast_nat (gcdWord a b).toNat (gcdWord a b).isLt

private theorem generated_catch_exact (Prefix : Type) (context : Prefix)
    (a b : GcdWord32) :
    (strengthenCatchBody Prefix).denote (context, false) (initialGlobals a b) =
      Zag.Lang.AutoCorres.throw true (cResultGlobals a b) := by
  simp only [strengthenCatchBody, TypeStrengthen.Kernel.Source.Term.denote, L2.seq]
  rw [Plus2Pipeline.bindE_modify_left, clear_initial_globals]
  have loopEq :
      L2.while (fun locals state => propositionBool (splitLoopTest locals state) = true)
        (fun locals => (strengthenCBody Prefix).denote (((context, false), ()), locals))
        false [] = generatedCLoop Prefix ((context, false), ()) := by
    unfold L2.while whileLoopE generatedCLoop cWhileTest cWhileBody
    apply congrArg (fun test => whileLoop test
      (whileLoopEBody fun locals =>
        (strengthenCBody Prefix).denote (((context, false), ()), locals))
      (.ok false))
    funext result state
    cases result <;> rfl
  rw [loopEq]
  rw [Plus2Pipeline.bindE_replace_returnOk _ _ _ _
    (generated_initial_c_loop_exact Prefix ((context, false), ()) a b)]
  rw [Plus2Pipeline.bindE_guard_left _ _ _ (c_loop_result_valid a b)]
  rw [Plus2Pipeline.bindE_modify_left]
  rfl

private theorem generated_nondet_catch_exact (Prefix : Type) (context : Prefix)
    (a b : GcdWord32) :
    TypeStrengthen.Kernel.nondetCatch
        ((strengthenCatchBody Prefix).denote (context, false))
        (fun exception => Zag.Lang.AutoCorres.pure exception)
        (initialGlobals a b) =
      Zag.Lang.AutoCorres.pure true (cResultGlobals a b) := by
  unfold TypeStrengthen.Kernel.nondetCatch
  exact Plus2Pipeline.bind_replace_pure _ _ _ _
    (generated_catch_exact Prefix context a b)

private def generatedProjectedNondet : Nondet Globals Nat :=
  Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.pure false) fun locals =>
    Zag.Lang.AutoCorres.bind
      (TypeStrengthen.Kernel.nondetCatch
        ((strengthenCatchBody Unit).denote ((), locals)) fun exception =>
          Zag.Lang.AutoCorres.pure exception) fun locals =>
      Zag.Lang.AutoCorres.bind
        (Zag.Lang.AutoCorres.guard (splitReturned locals)) fun _ =>
          Zag.Lang.AutoCorres.gets fun state =>
            WordAbstract.Kernel.abstractUnsignedInt 32 (readResult state)

private def generatedNatBody (pair : Nat × Nat) : Nondet Globals (Nat × Nat) :=
  Zag.Lang.AutoCorres.bind
    (Zag.Lang.AutoCorres.guard fun _ =>
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.2) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.1) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat pair.1) ≠ 0) fun _ =>
    Zag.Lang.AutoCorres.bind (Zag.Lang.AutoCorres.pure (mappedNatPair pair)) fun mapped =>
      Zag.Lang.AutoCorres.bind
        (Zag.Lang.AutoCorres.guard fun _ => mapped.1 < 2 ^ 32 /\ mapped.2 < 2 ^ 32)
        fun _ => Zag.Lang.AutoCorres.pure mapped

private def generatedNatLoop (initial : Nat × Nat) : Nondet Globals (Nat × Nat) :=
  whileLoop (fun pair _ => propositionBool (pair.1 ≠ 0) = true)
    generatedNatBody initial

private def generatedFinalNondet : Nondet Globals Nat :=
  Zag.Lang.AutoCorres.bind
    (Zag.Lang.AutoCorres.gets fun state =>
      (WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).1,
        WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).2)) fun initial =>
    Zag.Lang.AutoCorres.bind
      (Zag.Lang.AutoCorres.guard fun _ => initial.1 < 2 ^ 32 /\ initial.2 < 2 ^ 32)
      fun _ =>
      Zag.Lang.AutoCorres.bind
        (Zag.Lang.AutoCorres.guard fun _ =>
          canonicalPair (Int.ofNat initial.1, Int.ofNat initial.2)) fun _ =>
        Zag.Lang.AutoCorres.bind generatedProjectedNondet fun concreteResult =>
          Zag.Lang.AutoCorres.bind
            (Zag.Lang.AutoCorres.guard fun _ => concreteResult < 2 ^ 32 /\
              (reabstractNatPair initial).1 < 2 ^ 32 /\
              (reabstractNatPair initial).2 < 2 ^ 32) fun _ =>
            Zag.Lang.AutoCorres.bind (generatedNatLoop (reabstractNatPair initial))
              fun loopResult =>
              Zag.Lang.AutoCorres.bind
                (Zag.Lang.AutoCorres.guard fun _ =>
                  loopResult.1 < 2 ^ 32 /\ loopResult.2 < 2 ^ 32) fun _ =>
                Zag.Lang.AutoCorres.bind
                  (Zag.Lang.AutoCorres.guard fun _ =>
                    Int.ofNat loopResult.2 = Int.ofNat concreteResult) fun _ =>
                  Zag.Lang.AutoCorres.pure
                    (WordAbstract.Kernel.abstractUnsignedInt 32
                      (Int.ofNat loopResult.2))

private theorem final_target_is_generated :
    finalTarget = Zag.Lang.AutoCorres.liftE generatedFinalNondet := by
  rfl

private theorem abstract_word (value : GcdWord32) :
    WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat value.toNat) = value.toNat := by
  unfold WordAbstract.Kernel.abstractUnsignedInt
  rw [if_pos (show WordAbstract.Kernel.intUnsignedCanonical 32
    (Int.ofNat value.toNat) from ⟨by simp, Int.ofNat_lt.2 value.isLt⟩)]
  simp

private theorem mapped_word_pair (a b : GcdWord32) :
    mappedNatPair (a.toNat, b.toNat) = ((b % a).toNat, a.toNat) := by
  unfold mappedNatPair
  rw [abstract_word, abstract_word, gcd_remainder_toNat]

private theorem generated_nat_body_exact (a b : GcdWord32) (nonzero : a ≠ 0) :
    generatedNatBody (a.toNat, b.toNat) =
      Zag.Lang.AutoCorres.pure ((b % a).toNat, a.toNat) := by
  funext state
  have aNonzero : a.toNat ≠ 0 := by
    intro zero
    apply nonzero
    exact BitVec.toNat_inj.mp (by simpa using zero)
  unfold generatedNatBody
  have initialGuard :
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat b.toNat) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat a.toNat) < 2 ^ 32 /\
      WordAbstract.Kernel.abstractUnsignedInt 32 (Int.ofNat a.toNat) ≠ 0 := by
    rw [abstract_word, abstract_word]
    exact ⟨b.isLt, a.isLt, aNonzero⟩
  rw [Plus2Pipeline.bind_guard_left _ _ state initialGuard]
  rw [Plus2Pipeline.bind_pure_left_at]
  rw [mapped_word_pair]
  have finalGuard : (b % a).toNat < 2 ^ 32 /\ a.toNat < 2 ^ 32 :=
    ⟨(b % a).isLt, a.isLt⟩
  rw [Plus2Pipeline.bind_guard_left _ _ state finalGuard]

private theorem nat_test_zero (b : GcdWord32) :
    ¬propositionBool ((0, b.toNat).1 ≠ 0) = true := by
  rw [propositionBool_exact]
  simp

private theorem nat_test_nonzero (a b : GcdWord32) (nonzero : a ≠ 0) :
    propositionBool ((a.toNat, b.toNat).1 ≠ 0) = true := by
  rw [propositionBool_exact]
  intro zero
  apply nonzero
  exact BitVec.toNat_inj.mp (by simpa using zero)

set_option maxHeartbeats 2000000 in
private theorem generated_nat_loop_exact (a b : GcdWord32) :
    generatedNatLoop (a.toNat, b.toNat) =
      Zag.Lang.AutoCorres.pure (0, (gcdWord a b).toNat) := by
  induction a, b using gcdWord.induct with
  | case1 b =>
      funext state
      apply Plus2Pipeline.behavior_ext
      · funext outcome
        apply propext
        constructor
        · intro member
          change WhileResult _ _ (some ((0, b.toNat), state)) (some outcome) at member
          cases member with
          | stop _ => simpa [gcdWord, Zag.Lang.AutoCorres.pure]
          | step holds _ _ => exact False.elim (nat_test_zero b holds)
        · intro member
          have equality : outcome = ((0, b.toNat), state) := by
            simpa [gcdWord, Zag.Lang.AutoCorres.pure] using member
          cases equality
          exact WhileResult.stop (nat_test_zero b)
      · apply propext
        constructor
        · rintro (finite | notTerminates)
          · change WhileResult _ _ (some ((0, b.toNat), state)) none at finite
            cases finite with
            | bodyFailure holds _ => exact nat_test_zero b holds
            | step holds _ _ => exact nat_test_zero b holds
          · exact notTerminates (.stop (nat_test_zero b))
        · intro failed
          exact False.elim failed
  | case2 a b nonzero induction =>
      funext state
      have testHolds := nat_test_nonzero a b nonzero
      have bodyExact := congrFun (generated_nat_body_exact a b nonzero) state
      have restExact := congrFun induction state
      apply Plus2Pipeline.behavior_ext
      · funext outcome
        apply propext
        constructor
        · intro member
          change WhileResult _ _ (some ((a.toNat, b.toNat), state))
              (some outcome) at member
          cases member with
          | stop stopped => exact False.elim (stopped testHolds)
          | step _ bodyMember rest =>
              rw [bodyExact] at bodyMember
              simp only [mem_pure] at bodyMember
              rcases bodyMember with ⟨rfl, rfl⟩
              change outcome ∈
                (generatedNatLoop ((b % a).toNat, a.toNat) _).results at rest
              rw [induction] at rest
              rw [gcdWord_nonzero a b nonzero]
              exact rest
        · intro member
          have expectedMember :
              ((0, (gcdWord (b % a) a).toNat), state) ∈
                (generatedNatLoop ((b % a).toNat, a.toNat) state).results := by
            rw [restExact]
            exact mem_pure.mpr ⟨rfl, rfl⟩
          rcases outcome with ⟨result, post⟩
          change (result, post) = ((0, (gcdWord a b).toNat), state) at member
          cases member
          exact @WhileResult.step Globals (Nat × Nat)
            (fun pair _ => propositionBool (pair.1 ≠ 0) = true)
            generatedNatBody (a.toNat, b.toNat) state
            ((b % a).toNat, a.toNat) state
            (some ((0, (gcdWord a b).toNat), state))
            testHolds (by
              rw [bodyExact]
              exact mem_pure.mpr ⟨rfl, rfl⟩)
            (by
              rw [gcdWord_nonzero a b nonzero]
              exact expectedMember)
      · apply propext
        constructor
        · rintro (finite | notTerminates)
          · change WhileResult _ _ (some ((a.toNat, b.toNat), state)) none at finite
            cases finite with
            | bodyFailure _ bodyFailed =>
                rw [bodyExact] at bodyFailed
                exact bodyFailed
            | step _ bodyMember rest =>
                rw [bodyExact] at bodyMember
                simp only [mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                have restFailed :
                    (generatedNatLoop ((b % a).toNat, a.toNat) _).failed :=
                  Or.inl rest
                rw [induction] at restFailed
                exact restFailed
          · apply notTerminates
            exact @WhileTerminates.step Globals (Nat × Nat)
              (fun pair _ => propositionBool (pair.1 ≠ 0) = true)
              generatedNatBody (a.toNat, b.toNat) state testHolds (by
                intro next nextState bodyMember
                rw [bodyExact] at bodyMember
                simp only [mem_pure] at bodyMember
                rcases bodyMember with ⟨rfl, rfl⟩
                exact Classical.byContradiction fun restDoesNotTerminate => by
                  have restFailed :
                      (generatedNatLoop ((b % a).toNat, a.toNat) _).failed :=
                    Or.inr restDoesNotTerminate
                  rw [induction] at restFailed
                  exact restFailed)
        · intro failed
          exact False.elim failed

private theorem generated_projected_exact (a b : GcdWord32) :
    generatedProjectedNondet (initialGlobals a b) =
      Zag.Lang.AutoCorres.pure (gcdWord a b).toNat (cResultGlobals a b) := by
  unfold generatedProjectedNondet
  rw [Plus2Pipeline.bind_pure_left_at]
  rw [Plus2Pipeline.bind_replace_pure _ _ _ _
    (generated_nondet_catch_exact Unit () a b)]
  rw [Plus2Pipeline.bind_guard_left _ _ _
    (show splitReturned true (cResultGlobals a b) by rfl)]
  change Zag.Lang.AutoCorres.pure
    (WordAbstract.Kernel.abstractUnsignedInt 32 (readResult (cResultGlobals a b)))
      (cResultGlobals a b) = _
  rw [c_result_value, abstract_word]

private theorem initial_abstract_pair (a b : GcdWord32) :
    (WordAbstract.Kernel.abstractUnsignedInt 32 (readPair (initialGlobals a b)).1,
      WordAbstract.Kernel.abstractUnsignedInt 32 (readPair (initialGlobals a b)).2) =
      (a.toNat, b.toNat) := by
  rw [initial_readPair]
  unfold pairOfWords
  rw [abstract_word, abstract_word]

private theorem initial_nat_canonical (a b : GcdWord32) :
    canonicalPair (Int.ofNat a.toNat, Int.ofNat b.toNat) := by
  exact ⟨⟨by simp, Int.ofNat_lt.2 a.isLt⟩,
    ⟨by simp, Int.ofNat_lt.2 b.isLt⟩⟩

private theorem reabstract_word_pair (a b : GcdWord32) :
    reabstractNatPair (a.toNat, b.toNat) = (a.toNat, b.toNat) := by
  unfold reabstractNatPair
  rw [abstract_word, abstract_word]

private theorem generated_final_exact (a b : GcdWord32) :
    generatedFinalNondet (initialGlobals a b) =
      Zag.Lang.AutoCorres.pure (gcdWord a b).toNat (cResultGlobals a b) := by
  have initialGet :
      (Zag.Lang.AutoCorres.gets fun state =>
        (WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).1,
          WordAbstract.Kernel.abstractUnsignedInt 32 (readPair state).2))
          (initialGlobals a b) =
        Zag.Lang.AutoCorres.pure (a.toNat, b.toNat) (initialGlobals a b) := by
    change Zag.Lang.AutoCorres.pure
      (WordAbstract.Kernel.abstractUnsignedInt 32 (readPair (initialGlobals a b)).1,
        WordAbstract.Kernel.abstractUnsignedInt 32 (readPair (initialGlobals a b)).2)
        (initialGlobals a b) = _
    rw [initial_abstract_pair]
  unfold generatedFinalNondet
  rw [Plus2Pipeline.bind_replace_pure _ _ _ _ initialGet]
  have initialBounds : a.toNat < 2 ^ 32 /\ b.toNat < 2 ^ 32 :=
    ⟨a.isLt, b.isLt⟩
  rw [Plus2Pipeline.bind_guard_left _ _ (initialGlobals a b) initialBounds]
  rw [Plus2Pipeline.bind_guard_left _ _ (initialGlobals a b)
    (initial_nat_canonical a b)]
  rw [Plus2Pipeline.bind_replace_pure _ _ _ _ (generated_projected_exact a b)]
  rw [reabstract_word_pair]
  have projectedGuard :
      (gcdWord a b).toNat < 2 ^ 32 /\
        a.toNat < 2 ^ 32 /\ b.toNat < 2 ^ 32 :=
    ⟨(gcdWord a b).isLt, a.isLt, b.isLt⟩
  rw [Plus2Pipeline.bind_guard_left _ _ (cResultGlobals a b) projectedGuard]
  rw [Plus2Pipeline.bind_replace_pure _ _ _ _
    (congrFun (generated_nat_loop_exact a b) (cResultGlobals a b))]
  have finalGuard : 0 < 2 ^ 32 /\ (gcdWord a b).toNat < 2 ^ 32 := by
    exact ⟨by decide, (gcdWord a b).isLt⟩
  rw [Plus2Pipeline.bind_guard_left _ _ (cResultGlobals a b) finalGuard]
  rw [Plus2Pipeline.bind_guard_left _ _ (cResultGlobals a b)
    (show Int.ofNat (0, (gcdWord a b).toNat).2 =
      Int.ofNat (gcdWord a b).toNat by rfl)]
  rw [abstract_word]

/-- Exact generated endpoint behavior for every pair of u32 inputs. -/
theorem final_target_exact (a b : GcdWord32) :
    finalTarget (initialGlobals a b) =
      Zag.Lang.AutoCorres.returnOk (ε := Unit) (Nat.gcd a.toNat b.toNat)
        (cResultGlobals a b) := by
  rw [final_target_is_generated]
  rw [Plus2Pipeline.liftE_replace_pure _ _ _ (generated_final_exact a b)]
  rw [gcdWord_toNat]

theorem final_target_pure_return (a b : GcdWord32) :
    finalTarget (initialGlobals a b) =
      Zag.Lang.AutoCorres.liftE
        (Zag.Lang.AutoCorres.pure (Nat.gcd a.toNat b.toNat))
          (cResultGlobals a b) := by
  rw [Plus2Pipeline.liftE_pure_at]
  exact final_target_exact a b

/-- The generated final target is total on arbitrary u32 inputs. -/
theorem final_target_no_failure (a b : GcdWord32) :
    ¬(finalTarget (initialGlobals a b)).failed := by
  rw [final_target_exact]
  exact Plus2Pipeline.returnOk_not_failed _ _

theorem final_target_gcd_result (a b : GcdWord32) :
    (Except.ok (Nat.gcd a.toNat b.toNat), cResultGlobals a b) ∈
      (finalTarget (initialGlobals a b)).results := by
  rw [final_target_exact]
  exact mem_returnOk.mpr ⟨rfl, rfl⟩

theorem final_target_returns_only_gcd (a b : GcdWord32) :
    ∀ result post,
      (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
        result = Nat.gcd a.toNat b.toNat := by
  intro result post member
  rw [final_target_exact, mem_returnOk] at member
  exact member.1

theorem final_target_valid (a b : GcdWord32) :
    ¬(finalTarget (initialGlobals a b)).failed /\
      ∀ result post,
        (Except.ok result, post) ∈ (finalTarget (initialGlobals a b)).results →
          result = Nat.gcd a.toNat b.toNat :=
  ⟨final_target_no_failure a b, final_target_returns_only_gcd a b⟩

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline
