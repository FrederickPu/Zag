import Test.AutoCorres.CParser.ScalarSimpl.Plus
import Lang.AutoCorres.ML.autocorres

/-! # Fixture-derived `plus` through the five AutoCorres phases -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

noncomputable section

private theorem behavior_ext {State Result : Type}
    {left right : Behavior State Result}
    (results : left.results = right.results)
    (failed : left.failed = right.failed) : left = right := by
  cases left
  cases right
  cases results
  cases failed
  rfl

abbrev Full := State
abbrev Locals := Bool

structure Globals where
  value : Nat -> Int
  initialized : Nat -> Bool
  result : Int
  callStack : List CallFrame
  temporaries : List Int

def model : ML.LocalVarExtract.StateModel Full Locals Globals where
  projectGlobals := fun state =>
    { value := state.value
      initialized := state.initialized
      result := state.result
      callStack := state.callStack
      temporaries := state.temporaries }
  projectLocals := State.returned
  assemble := fun returned globals =>
    { value := globals.value
      initialized := globals.initialized
      returned
      result := globals.result
      callStack := globals.callStack
      temporaries := globals.temporaries }
  projectGlobals_assemble := by intros; rfl
  projectLocals_assemble := by intros; rfl
  assemble_project := by intro state; cases state; rfl

def plusExpression : Expr :=
  .binary u32 u32 .add (.variable u32 1) (.variable u32 2)

def expectedFunction : Function :=
  { name := "plus"
    returnType := u32
    parameters := [(1, u32), (2, u32)]
    locals := []
    body := .seq (.return u32 plusExpression) .skip }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus_eq_expected : plus = expectedFunction := by native_decide

def expressionValid (state : State) : Prop :=
  exists value, plusExpression.eval state = some value

def expressionValue (state : State) : Int :=
  (plusExpression.eval state).getD 0

def setResult (_ : Locals) (globals : Globals) : Globals :=
  model.projectGlobals
    ((model.assemble false globals).returnValue u32
      (expressionValue (model.assemble false globals)))

def setReturned (_ : Locals) (_ : Globals) : Locals := true

def resetReturned (_ : Locals) (_ : Globals) : Locals := false

def keepReturned (locals : Locals) (_ : Globals) : Locals := locals

def returnUpdate (state : State) : State :=
  state.returnValue u32 (expressionValue state)

def splitValid (locals : Locals) (globals : Globals) : Prop :=
  expressionValid (model.assemble locals globals)

def splitReturned (locals : Locals) (_ : Globals) : Prop := locals = true

def generatedL1 : L1.Syntax Full :=
  .seq (.modify State.resetReturn)
    (.seq
      (.catch
        (.seq
          (.seq (.guard expressionValid)
            (.seq (.modify returnUpdate) .throw))
          .skip)
        .skip)
      (.seq (.modify expectedFunction.finalize)
        (.seq (.guard fun state => state.returned = true) .skip)))

def normalizedL1 : L1.Syntax Full :=
  .seq (.modify (ML.LocalVarExtract.Source.localTransform model resetReturned))
    (.seq
      (.catch
        (.seq
          (.seq (.guard fun state =>
              splitValid (model.projectLocals state) (model.projectGlobals state))
            (.seq
              (.seq (.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
                (.modify (ML.LocalVarExtract.Source.localTransform model setReturned)))
              .throw))
          .skip)
        .skip)
      (.seq (.modify (ML.LocalVarExtract.Source.localTransform model keepReturned))
        (.seq (.guard fun state =>
          splitReturned (model.projectLocals state) (model.projectGlobals state)) .skip)))

theorem commandEq : expectedFunction.command = plus.command :=
  congrArg Function.command plus_eq_expected.symm

def transportedSupport : SimplConv.Kernel.Supported plus.command :=
  expectedFunction.supported.transport commandEq

def simplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment transportedSupport

def fixtureSimplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment plusEmitsSupported

theorem fixture_simpl_target_eq :
    fixtureSimplCertificate.target = simplCertificate.target := by
  unfold fixtureSimplCertificate simplCertificate
  rw [SimplConv.Kernel.Supported.unique plusEmitsSupported transportedSupport]

theorem simpl_generated_shape : simplCertificate.target = generatedL1 := by
  unfold simplCertificate
  unfold transportedSupport
  rw [ML.SimplConv.simplConv_transport_target]
  simp [ML.SimplConv.simplConv, expectedFunction, Function.supported,
    _root_.Zag.Lang.AutoCorres.CParser.ScalarSimpl.supported,
    Function.command, compile, plusExpression, generatedL1]
  constructor <;> rfl

private theorem reset_update_eq :
    State.resetReturn =
      ML.LocalVarExtract.Source.localTransform model resetReturned := by
  funext state
  cases state
  rfl

private theorem finalize_update_eq :
    expectedFunction.finalize =
      ML.LocalVarExtract.Source.localTransform model keepReturned := by
  funext state
  cases state
  simp [expectedFunction, Function.finalize,
    ML.LocalVarExtract.Source.localTransform, model, keepReturned]

private theorem return_update_eq :
    L1.modify returnUpdate =
      L1.seq
        (L1.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
        (L1.modify (ML.LocalVarExtract.Source.localTransform model setReturned)) := by
  funext state
  have combinedUpdate :
      ML.LocalVarExtract.Source.localTransform model setReturned
          (ML.LocalVarExtract.Source.globalTransform model setResult state) =
        returnUpdate state := by
    cases state
    rfl
  apply behavior_ext
  · funext outcome
    apply propext
    rcases outcome with ⟨result, post⟩
    cases result with
    | error exception =>
        change (Except.error exception, post) ∈
            (L2.modify returnUpdate state).results ↔
          (Except.error exception, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq]
    | ok result =>
        change (Except.ok result, post) ∈
            (L2.modify returnUpdate state).results ↔
          (Except.ok result, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq, combinedUpdate]
  · apply propext
    change (L2.modify (Exception := Unit) returnUpdate state).failed ↔
      (L2.seq
        (L2.modify
          (ML.LocalVarExtract.Source.globalTransform model setResult))
        (fun _ => L2.modify
          (ML.LocalVarExtract.Source.localTransform model setReturned)) state).failed
    simp [L2.seq]

private theorem split_valid_full :
    (fun state => splitValid (model.projectLocals state) (model.projectGlobals state)) =
      expressionValid := by
  funext state
  simp [splitValid, model]

private theorem split_returned_full :
    (fun state => splitReturned (model.projectLocals state) (model.projectGlobals state)) =
      (fun state => state.returned = true) := by
  funext state
  rfl

theorem fixture_simpl_endpoint :
    fixtureSimplCertificate.target.denote = normalizedL1.denote := by
  rw [fixture_simpl_target_eq]
  rw [simpl_generated_shape]
  simp only [generatedL1, normalizedL1, L1.Syntax.denote]
  rw [reset_update_eq, finalize_update_eq, return_update_eq]
  rw [split_valid_full, split_returned_full]

theorem normalizedL1Corres :
    L1.L1Corres false emptyEnvironment normalizedL1.denote plus.command := by
  rw [← fixture_simpl_endpoint]
  exact fixtureSimplCertificate.corres

def lveSupported : ML.LocalVarExtract.Supported model normalizedL1 :=
  .seq (.localUpdate resetReturned)
    (.seq
      (.catch
        (.seq
          (.seq (.guard splitValid)
            (.seq
              (.seq (.globalUpdate setResult) (.localUpdate setReturned))
              .throw))
          .skip)
        .skip)
      (.seq (.localUpdate keepReturned)
        (.seq (.guard splitReturned) .skip)))

def lveCertificate :=
  ML.LocalVarExtract.extractCanonical model lveSupported

theorem lve_consumes_fixture_endpoint (locals : Locals) :
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        lveCertificate.target locals)
      fixtureSimplCertificate.target.denote := by
  rw [fixture_simpl_endpoint]
  exact lveCertificate.corres locals

def readResult (globals : Globals) : BitVec 32 :=
  BitVec.ofInt 32 globals.result

def projectedL2 : L2.Syntax Globals Bool (BitVec 32) :=
  .seq (lveCertificate.target false) fun _ => .gets readResult []

private theorem projectCorres :
    CorresXF id (fun _ post => readResult post)
      (fun exception _ => exception) (fun _ => True)
      projectedL2.denote
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        lveCertificate.target false) := by
  intro state hypothesis
  constructor
  · intro result post member
    cases result with
    | error exception =>
        change (Except.error exception, post) ∈
          (L2.seq
            (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
              lveCertificate.target false)
            (fun _ => L2.gets readResult []) state).results
        exact ⟨Except.error exception, post, member, rfl⟩
    | ok value =>
        change (Except.ok (readResult post), post) ∈
          (L2.seq
            (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
              lveCertificate.target false)
            (fun _ => L2.gets readResult []) state).results
        refine ⟨Except.ok value, post, member, ?_⟩
        simp [L2.gets]
  · intro failed
    apply hypothesis.2
    exact Or.inl failed

private theorem projectedL2Corres_normalized :
    L2.L2Corres model.projectGlobals
      (fun state => readResult (model.projectGlobals state))
      model.projectLocals
      (fun state => model.projectLocals state = false)
      projectedL2.denote normalizedL1.denote := by
  simpa [L2.L2Corres, Function.comp_def] using
    (CorresXF.merge (lveCertificate.corres false) projectCorres)

theorem projectedL2Corres :
    L2.L2Corres model.projectGlobals
      (fun state => readResult (model.projectGlobals state))
      model.projectLocals
      (fun state => model.projectLocals state = false)
      projectedL2.denote fixtureSimplCertificate.target.denote := by
  rw [fixture_simpl_endpoint]
  exact projectedL2Corres_normalized

theorem heapLiftCorres :
    HeapLift.L2Tcorres id projectedL2.denote projectedL2.denote :=
  HeapLift.L2Tcorres_id projectedL2.denote

noncomputable def validTest (locals : Locals) (globals : Globals) : Bool :=
  @ite Bool (splitValid locals globals) (Classical.propDecidable _) true false

theorem validTest_exact (locals : Locals) (globals : Globals) :
    validTest locals globals = true ↔ splitValid locals globals := by
  simp [validTest]

def wordLveSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool :=
  .seq (.gets (.bool false) []) fun reset =>
    .seq
      (.catch
        (.seq
          ((.seq
              (.seq
                (.guard (.state .bool (validTest reset)))
                fun _ => .gets (.bool reset) [])
              fun localsValue =>
                .seq
                  (.seq
                    (.seq (.modify (setResult localsValue)) fun _ =>
                      .gets (.bool localsValue) [])
                    fun _ => .gets (.bool true) [])
                  fun localsValue => .throw localsValue []) :
            WordAbstract.Kernel.Source.Syntax .unit Globals .bool .bool)
          fun (localsValue : Bool) => .gets (.bool localsValue) [])
        fun exception => .gets (.bool exception) [])
      fun localsValue =>
        .seq (.gets (.bool localsValue) []) fun localsValue =>
          .seq
            (.seq (.guard (.bool localsValue)) fun _ => .gets (.bool localsValue) [])
            fun localsValue => .gets (.bool localsValue) []

def wordSource :
    WordAbstract.Kernel.Source.Syntax .unit Globals .bool (.word 32) :=
  .seq wordLveSource fun _ => .gets (.state (.word 32) readResult) []

theorem heap_to_word_endpoint_exact :
    projectedL2.denote = wordSource.denote () := by
  simp only [projectedL2, lveCertificate, lveSupported,
    ML.LocalVarExtract.extractCanonical, ML.LocalVarExtract.extract,
    LocalVarExtract.Kernel.Certificate.close,
    LocalVarExtract.Kernel.CanonicalTarget.Syntax.ofGeneric,
    L2.Syntax.denote, wordSource, wordLveSource,
    WordAbstract.Kernel.Source.Syntax.denote,
    WordAbstract.Kernel.Source.Expr.eval]
  have guardEq : forall localsValue,
      L2.guard (Exception := Bool) (splitValid localsValue) =
        L2.guard (fun state => validTest localsValue state = true) := by
    intro localsValue
    congr 1
    funext state
    exact propext (validTest_exact localsValue state).symm
  simp only [guardEq]
  unfold resetReturned keepReturned setReturned splitReturned readResult
  rfl

def wordCertificate := ML.WordAbstract.transformSource wordSource

theorem word_consumes_heap_endpoint :
    WordAbstract.corresTA (fun _ => True) BitVec.toNat id
      (wordCertificate.target.denote ()) projectedL2.denote := by
  rw [heap_to_word_endpoint_exact]
  exact wordCertificate.corres ()

def strengthenCatchBody :
    TypeStrengthen.Kernel.Source.Term (Unit × Bool) Globals Bool Bool :=
  .seq (.guard fun input state => validTest input.2 state)
    (.seq (.modify fun input state => setResult input.1.2 state)
      (.throw (fun _ => true) []))

def strengthenCatchHandler :
    TypeStrengthen.Kernel.Source.Term ((Unit × Bool) × Bool) Globals Bool Bool :=
  .pure (fun input => input.2) []

def strengthenRest :
    TypeStrengthen.Kernel.Source.Term ((Unit × Bool) × Bool) Globals Bool Nat :=
  .seq (.guard fun input _ => input.2)
    (.gets (fun _ state => (readResult state).toNat) [])

def strengthenSource :
    TypeStrengthen.Kernel.Source.Closed Globals Bool Nat :=
  .seq (.pure (fun _ => false) [])
    (.seq (.catchHandlers strengthenCatchBody strengthenCatchHandler)
      strengthenRest)

def strengthenSupported :
    TypeStrengthen.Kernel.Supported .nondet strengthenSource :=
  .nondetSeq .nondetValue
    (.nondetSeq (.nondetCatchHandlers .nondetValue)
      (.nondetSeq .nondetGuard .nondetRead))

def strengthenCertificate :=
  ML.TypeStrengthen.strengthenClosed strengthenSupported

theorem l2_seq_assoc
    {State Exception Middle Output Final : Type}
    (first : L2.L2Program State Exception Middle)
    (next : Middle -> L2.L2Program State Exception Output)
    (last : Output -> L2.L2Program State Exception Final) :
    L2.seq (L2.seq first next) last =
      L2.seq first fun value => L2.seq (next value) last := by
  funext state
  apply behavior_ext
  · funext result
    apply propext
    rcases result with ⟨outcome, post⟩
    unfold L2.seq
    cases outcome with
    | error error =>
        change ((Except.error error, post) ∈
            (bindE (bindE first next) last state).results) ↔
          ((Except.error error, post) ∈
            (bindE first (fun value => bindE (next value) last) state).results)
        constructor
        · intro member
          rcases TypeStrengthen.mem_bindE_error.mp member with
            innerError | ⟨output, outputState, innerOk, lastError⟩
          · rcases TypeStrengthen.mem_bindE_error.mp innerError with
              firstError | ⟨value, middle, firstOk, nextError⟩
            · exact TypeStrengthen.mem_bindE_error.mpr (Or.inl firstError)
            · exact TypeStrengthen.mem_bindE_error.mpr
                (Or.inr ⟨value, middle, firstOk,
                  TypeStrengthen.mem_bindE_error.mpr (Or.inl nextError)⟩)
          · rcases mem_bindE_ok.mp innerOk with
              ⟨value, middle, firstOk, nextOk⟩
            exact TypeStrengthen.mem_bindE_error.mpr
              (Or.inr ⟨value, middle, firstOk,
                TypeStrengthen.mem_bindE_error.mpr
                  (Or.inr ⟨output, outputState, nextOk, lastError⟩)⟩)
        · intro member
          rcases TypeStrengthen.mem_bindE_error.mp member with
            firstError | ⟨value, middle, firstOk, restError⟩
          · exact TypeStrengthen.mem_bindE_error.mpr
              (Or.inl (TypeStrengthen.mem_bindE_error.mpr (Or.inl firstError)))
          · rcases TypeStrengthen.mem_bindE_error.mp restError with
              nextError | ⟨output, outputState, nextOk, lastError⟩
            · exact TypeStrengthen.mem_bindE_error.mpr
                (Or.inl (TypeStrengthen.mem_bindE_error.mpr
                  (Or.inr ⟨value, middle, firstOk, nextError⟩)))
            · exact TypeStrengthen.mem_bindE_error.mpr
                (Or.inr ⟨output, outputState,
                  mem_bindE_ok.mpr ⟨value, middle, firstOk, nextOk⟩,
                  lastError⟩)
    | ok output =>
        change ((Except.ok output, post) ∈
            (bindE (bindE first next) last state).results) ↔
          ((Except.ok output, post) ∈
            (bindE first (fun value => bindE (next value) last) state).results)
        constructor
        · intro member
          rcases mem_bindE_ok.mp member with
            ⟨output, outputState, innerOk, lastOk⟩
          rcases mem_bindE_ok.mp innerOk with
            ⟨value, middle, firstOk, nextOk⟩
          exact mem_bindE_ok.mpr ⟨value, middle, firstOk,
            mem_bindE_ok.mpr ⟨output, outputState, nextOk, lastOk⟩⟩
        · intro member
          rcases mem_bindE_ok.mp member with
            ⟨value, middle, firstOk, restOk⟩
          rcases mem_bindE_ok.mp restOk with
            ⟨output, outputState, nextOk, lastOk⟩
          exact mem_bindE_ok.mpr ⟨output, outputState,
            mem_bindE_ok.mpr ⟨value, middle, firstOk, nextOk⟩, lastOk⟩
  · apply propext
    unfold L2.seq
    constructor
    · intro failed
      rcases TypeStrengthen.failed_bindE.mp failed with
        innerFailed | ⟨output, outputState, innerOk, lastFailed⟩
      · rcases TypeStrengthen.failed_bindE.mp innerFailed with
          firstFailed | ⟨value, middle, firstOk, nextFailed⟩
        · exact TypeStrengthen.failed_bindE.mpr (Or.inl firstFailed)
        · exact TypeStrengthen.failed_bindE.mpr
            (Or.inr ⟨value, middle, firstOk,
              TypeStrengthen.failed_bindE.mpr (Or.inl nextFailed)⟩)
      · rcases mem_bindE_ok.mp innerOk with
          ⟨value, middle, firstOk, nextOk⟩
        exact TypeStrengthen.failed_bindE.mpr
          (Or.inr ⟨value, middle, firstOk,
            TypeStrengthen.failed_bindE.mpr
              (Or.inr ⟨output, outputState, nextOk, lastFailed⟩)⟩)
    · intro failed
      rcases TypeStrengthen.failed_bindE.mp failed with
        firstFailed | ⟨value, middle, firstOk, restFailed⟩
      · exact TypeStrengthen.failed_bindE.mpr
          (Or.inl (TypeStrengthen.failed_bindE.mpr (Or.inl firstFailed)))
      · rcases TypeStrengthen.failed_bindE.mp restFailed with
          nextFailed | ⟨output, outputState, nextOk, lastFailed⟩
        · exact TypeStrengthen.failed_bindE.mpr
            (Or.inl (TypeStrengthen.failed_bindE.mpr
              (Or.inr ⟨value, middle, firstOk, nextFailed⟩)))
        · exact TypeStrengthen.failed_bindE.mpr
            (Or.inr ⟨output, outputState,
              mem_bindE_ok.mpr ⟨value, middle, firstOk, nextOk⟩,
              lastFailed⟩)

theorem l2_seq_true_guard
    {State Exception Output : Type}
    (next : Unit -> L2.L2Program State Exception Output) :
    L2.seq (L2.guard fun _ : State => True) next = next () := by
  funext state
  apply behavior_ext
  · funext result
    apply propext
    rcases result with ⟨outcome, post⟩
    unfold L2.seq
    cases outcome with
    | error error =>
        change ((Except.error error, post) ∈
            (bindE (L2.guard fun _ : State => True) next state).results) ↔
          ((Except.error error, post) ∈ (next () state).results)
        rw [TypeStrengthen.mem_bindE_error]
        simp [L2.guard, L2.mem_liftE_iff, mem_guard]
        constructor
        · rintro ⟨value, member⟩
          cases value
          exact member
        · intro member
          exact ⟨(), member⟩
    | ok output =>
        change ((Except.ok output, post) ∈
            (bindE (L2.guard fun _ : State => True) next state).results) ↔
          ((Except.ok output, post) ∈ (next () state).results)
        rw [mem_bindE_ok]
        simp [L2.guard, L2.mem_liftE_iff, mem_guard]
        constructor
        · rintro ⟨value, member⟩
          cases value
          exact member
        · intro member
          exact ⟨(), member⟩
  · apply propext
    unfold L2.seq
    rw [TypeStrengthen.failed_bindE]
    simp [L2.guard, L2.mem_liftE_iff, mem_guard, failed_guard]
    constructor
    · rintro ⟨value, failed⟩
      cases value
      exact failed
    · intro failed
      exact ⟨(), failed⟩

theorem l2_seq_gets
    {State Exception Middle Output : Type}
    (read : State -> Middle) (names : List String)
    (next : Middle -> L2.L2Program State Exception Output) :
    L2.seq (L2.gets read names) next = fun state => next (read state) state := by
  funext state
  apply behavior_ext
  · funext result
    apply propext
    rcases result with ⟨outcome, post⟩
    unfold L2.seq
    cases outcome with
    | error error =>
        change ((Except.error error, post) ∈
            (bindE (L2.gets read names) next state).results) ↔
          ((Except.error error, post) ∈ (next (read state) state).results)
        rw [TypeStrengthen.mem_bindE_error]
        simp [L2.gets, L2.mem_liftE_iff, mem_gets]
        constructor
        · rintro ⟨value, middle, ⟨valueEq, middleEq⟩, member⟩
          subst value
          subst middle
          exact member
        · intro member
          exact ⟨read state, state, ⟨rfl, rfl⟩, member⟩
    | ok output =>
        change ((Except.ok output, post) ∈
            (bindE (L2.gets read names) next state).results) ↔
          ((Except.ok output, post) ∈ (next (read state) state).results)
        rw [mem_bindE_ok]
        simp [L2.gets, L2.mem_liftE_iff, mem_gets]
        constructor
        · rintro ⟨value, middle, ⟨valueEq, middleEq⟩, member⟩
          subst value
          subst middle
          exact member
        · intro member
          exact ⟨read state, state, ⟨rfl, rfl⟩, member⟩
  · apply propext
    unfold L2.seq
    rw [TypeStrengthen.failed_bindE]
    simp [L2.gets, L2.mem_liftE_iff, Zag.Lang.AutoCorres.gets]
    constructor
    · rintro ⟨value, middle, equality, failed⟩
      cases equality
      exact failed
    · intro failed
      exact ⟨read state, state, rfl, failed⟩

theorem l2_seq_throw {State Exception Middle Output : Type}
    (exception : Exception) (names : List String)
    (next : Middle -> L2.L2Program State Exception Output) :
    L2.seq (L2.throw (Value := Middle) exception names) next =
      L2.throw exception names := by
  funext state
  apply behavior_ext
  · funext result
    apply propext
    rcases result with ⟨outcome, post⟩
    unfold L2.seq
    cases outcome with
    | error error =>
        change ((Except.error error, post) ∈
            (bindE (L2.throw (Value := Middle) exception names) next state).results) ↔
          ((Except.error error, post) ∈
            (L2.throw (Value := Output) exception names state).results)
        rw [TypeStrengthen.mem_bindE_error]
        simp [L2.throw]
        intro value middle member _
        change (Except.ok value, middle) =
          (Except.error exception, state) at member
        cases member
    | ok output =>
        change ((Except.ok output, post) ∈
            (bindE (L2.throw (Value := Middle) exception names) next state).results) ↔
          ((Except.ok output, post) ∈
            (L2.throw (Value := Output) exception names state).results)
        rw [mem_bindE_ok]
        simp [L2.throw]
        constructor
        · rintro ⟨value, middle, member, _⟩
          change (Except.ok value, middle) =
            (Except.error exception, state) at member
          cases member
        · intro member
          change (Except.ok output, post) =
            (Except.error exception, state) at member
          cases member
  · apply propext
    unfold L2.seq
    rw [TypeStrengthen.failed_bindE]
    simp [L2.throw, Zag.Lang.AutoCorres.throw,
      Zag.Lang.AutoCorres.pure]
    intro value middle member
    change (Except.ok value, middle) =
      (Except.error exception, state) at member
    cases member

theorem word_to_strengthen_call_exact :
    L2.call (Exception := Unit) (wordCertificate.target.denote ()) =
      L2.call (Exception := Unit) (strengthenSource.denote ()) := by
  dsimp [wordCertificate, ML.WordAbstract.transformSource,
    ML.WordAbstract.transform, ML.WordAbstract.transformRaw,
    ML.WordAbstract.supported, ML.WordAbstract.Expr.supported,
    ML.WordAbstract.Expr.transform,
    wordSource, wordLveSource]
  simp only [WordAbstract.Kernel.Target.Syntax.denote,
    WordAbstract.Kernel.Target.Expr.eval,
    WordAbstract.Kernel.TypeMap.concretize,
    TypeStrengthen.Kernel.Source.Term.denote,
    strengthenSource, strengthenCatchBody, strengthenCatchHandler,
    strengthenRest]
  simp [l2_seq_assoc, l2_seq_true_guard, l2_seq_gets, l2_seq_throw,
    validTest_exact, WordAbstract.Kernel.typeMap,
    WordAbstract.valid_typ_abs_fn_id]

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
    false emptyEnvironment plus.command finalTarget :=
  { stateProjectL2 := model.projectGlobals
    returnExtractL2 := fun state => readResult (model.projectGlobals state)
    exceptionExtractL2 := model.projectLocals
    preconditionL2 := fun state => model.projectLocals state = false
    stateProjectHL := id
    preconditionWA := fun _ => True
    returnExtractWA := BitVec.toNat
    exceptionExtractWA := id
    l1 := fixtureSimplCertificate.target.denote
    l1Corres := fixtureSimplCertificate.corres
    l2 := projectedL2.denote
    l2Corres := projectedL2Corres
    heapLifted := projectedL2.denote
    heapLiftCorres := heapLiftCorres
    wordAbstracted := wordCertificate.target.denote ()
    wordAbstractCorres := word_consumes_heap_endpoint
    typeStrengthen := type_strengthen_consumes_word_endpoint }

theorem final_chain_endpoints :
    finalChain.l1 = fixtureSimplCertificate.target.denote ∧
    finalChain.l2 = projectedL2.denote ∧
    finalChain.heapLifted = projectedL2.denote ∧
    finalChain.wordAbstracted = wordCertificate.target.denote () := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finalAcCorres :
    ac_corres model.projectGlobals false emptyEnvironment
      (fun state => (readResult (model.projectGlobals state)).toNat)
      (fun state => model.projectLocals state = false)
      finalTarget plus.command := by
  simpa [finalChain, Function.comp_def] using finalChain.acCorres

theorem raw_success_reaches_final {state post : State}
    (initialLocals : model.projectLocals state = false)
    (targetDoesNotFail : ¬(finalTarget (model.projectGlobals state)).failed)
    (execution : Raw.FunctionExec plusCertificate.program "plus"
      plusCertificate.functionInfo plusCertificate.rawBody plus.returnType
      state (.success post)) :
    (Except.ok ((readResult (model.projectGlobals post)).toNat),
      model.projectGlobals post) ∈
      (finalTarget (model.projectGlobals state)).results := by
  have simplExecution :
      Simpl.Exec emptyEnvironment plus.command (.normal state) (.normal post) := by
    simpa [Raw.embedOutcome] using
      (plus_finite_execution_iff state (.success post)).mp execution
  rcases (finalAcCorres state ⟨initialLocals, targetDoesNotFail⟩).1
      (.normal post) simplExecution with ⟨actualPost, equality, member⟩
  cases equality
  exact member

def concreteState : State :=
  match plus.enter [3, 4] with
  | .ok state => state
  | .error _ => {}

def concreteGlobals : Globals := model.projectGlobals concreteState

def concretePost : Globals := setResult false concreteGlobals

def concreteFullPost : State :=
  concreteState.resetReturn.returnValue u32 7

theorem concrete_initial_locals : model.projectLocals concreteState = false := by
  native_decide

theorem concrete_raw_fixture_executes :
    Raw.FunctionExec plusCertificate.program "plus" plusCertificate.functionInfo
      plusCertificate.rawBody plus.returnType concreteState
      (.success concreteFullPost) := by
  apply (plus_finite_execution_iff concreteState (.success concreteFullPost)).mpr
  apply plus.command_correct
  apply Function.Exec.returned
  rw [plus_eq_expected]
  apply Stmt.Exec.seqReturned
  apply Stmt.Exec.ret (result := 7)
  native_decide

theorem concrete_valid : splitValid false concreteGlobals := by
  unfold splitValid expressionValid concreteGlobals concreteState model
  refine ⟨7, ?_⟩
  native_decide

theorem concrete_valid_test : validTest false concreteGlobals = true :=
  (validTest_exact false concreteGlobals).mpr concrete_valid

theorem concrete_result : (readResult concretePost).toNat = 7 := by
  native_decide

theorem concrete_raw_result_is_seven :
    (readResult (model.projectGlobals concreteFullPost)).toNat = 7 := by
  native_decide

theorem final_target_executes_seven :
    (Except.ok 7, concretePost) ∈ (finalTarget concreteGlobals).results := by
  have bodyMember : (Except.error true, concretePost) ∈
      (strengthenCatchBody.denote ((), false) concreteGlobals).results := by
    simp [strengthenCatchBody, TypeStrengthen.Kernel.Source.Term.denote,
      L2.seq, concrete_valid_test, concretePost]
    rfl
  have handlerMember : (Except.ok true, concretePost) ∈
      (strengthenCatchHandler.denote (((), false), true) concretePost).results := by
    simp [strengthenCatchHandler, TypeStrengthen.Kernel.Source.Term.denote,
      L2.gets]
  have catchMember : (Except.ok true, concretePost) ∈
      (L2.catch (strengthenCatchBody.denote ((), false))
        (fun exception => strengthenCatchHandler.denote
          (((), false), exception)) concreteGlobals).results :=
    ⟨Except.error true, concretePost, bodyMember, handlerMember⟩
  have restMember : (Except.ok 7, concretePost) ∈
      (strengthenRest.denote ((((), false), true)) concretePost).results := by
    simp [strengthenRest, TypeStrengthen.Kernel.Source.Term.denote,
      L2.seq, concrete_result]
  have sourceMember : (Except.ok 7, concretePost) ∈
      (strengthenSource.denote () concreteGlobals).results := by
    simp only [strengthenSource, TypeStrengthen.Kernel.Source.Term.denote]
    exact mem_bindE_ok.mpr ⟨false, concreteGlobals, by simp [L2.gets],
      mem_bindE_ok.mpr ⟨true, concretePost, catchMember, restMember⟩⟩
  have callMember : (Except.ok 7, concretePost) ∈
      (L2.call (Exception := Unit) (strengthenSource.denote ())
        concreteGlobals).results :=
    TypeStrengthen.mem_call_ok.mpr sourceMember
  rw [strengthenCertificate.exact Unit] at callMember
  simpa [finalTarget] using callMember

theorem fixture_and_final_execute_three_plus_four :
    Raw.FunctionExec plusCertificate.program "plus" plusCertificate.functionInfo
        plusCertificate.rawBody plus.returnType concreteState
        (.success concreteFullPost) ∧
      (readResult (model.projectGlobals concreteFullPost)).toNat = 7 ∧
      (Except.ok 7, concretePost) ∈ (finalTarget concreteGlobals).results :=
  ⟨concrete_raw_fixture_executes, concrete_raw_result_is_seven,
    final_target_executes_seven⟩

end
end Zag.Test.AutoCorres.CParser.ScalarSimpl.PlusPipeline
