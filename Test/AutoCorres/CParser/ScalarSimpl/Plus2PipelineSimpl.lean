import Test.AutoCorres.CParser.ScalarSimpl.Plus2Termination
import Lang.AutoCorres.ML.autocorres

/-! # Fixture-derived `plus2` through SimplConv and local-variable extraction -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.Plus2Pipeline

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

def expressionValid (expression : Expr) (state : State) : Prop :=
  exists value, expression.eval state = some value

def expressionValue (expression : Expr) (state : State) : Int :=
  (expression.eval state).getD 0

def resetReturned (_ : Locals) (_ : Globals) : Locals := false
def keepReturned (locals : Locals) (_ : Globals) : Locals := locals
def setReturned (_ : Locals) (_ : Globals) : Locals := true

def updateExpression (id : Nat) (type : ScalarType) (expression : Expr)
    (locals : Locals) (globals : Globals) : Globals :=
  model.projectGlobals
    ((model.assemble locals globals).write id type
      (expressionValue expression (model.assemble locals globals)))

def setResult (locals : Locals) (globals : Globals) : Globals :=
  model.projectGlobals
    ((model.assemble locals globals).returnValue u32
      (expressionValue (.variable u32 1) (model.assemble locals globals)))

def splitValid (expression : Expr) (locals : Locals) (globals : Globals) : Prop :=
  expressionValid expression (model.assemble locals globals)

def splitLoopTest (locals : Locals) (globals : Globals) : Prop :=
  plus2Condition.eval (model.assemble locals globals) != some 0

def splitReturned (locals : Locals) (_ : Globals) : Prop := locals = true

def normalizedLoopBody : L1.Syntax Full :=
  .seq
    (.seq (.guard fun state => splitValid plus2Condition
        (model.projectLocals state) (model.projectGlobals state)) .skip)
    (.seq
      (.seq
        (.seq (.guard fun state => splitValid plus2Increment
            (model.projectLocals state) (model.projectGlobals state))
          (.modify (ML.LocalVarExtract.Source.globalTransform model
            (updateExpression 1 u32 plus2Increment))))
        (.seq
          (.seq (.guard fun state => splitValid plus2Decrement
              (model.projectLocals state) (model.projectGlobals state))
            (.modify (ML.LocalVarExtract.Source.globalTransform model
              (updateExpression 2 u32 plus2Decrement))))
          .skip))
      .skip)

def normalizedL1 : L1.Syntax Full :=
  .seq (.modify (ML.LocalVarExtract.Source.localTransform model resetReturned))
    (.seq
      (.catch
        (.seq
          (.while (fun state => splitLoopTest
              (model.projectLocals state) (model.projectGlobals state))
            normalizedLoopBody)
          (.seq
            (.seq (.guard fun state => splitValid (.variable u32 1)
                (model.projectLocals state) (model.projectGlobals state))
              (.seq
                (.seq (.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
                  (.modify (ML.LocalVarExtract.Source.localTransform model setReturned)))
                .throw))
            .skip))
        .skip)
      (.seq (.modify (ML.LocalVarExtract.Source.localTransform model keepReturned))
        (.seq (.guard fun state => splitReturned
          (model.projectLocals state) (model.projectGlobals state)) .skip)))

def generatedLoopBody : L1.Syntax Full :=
  .seq
    (.seq (.guard (expressionValid plus2Condition)) .skip)
    (.seq
      (.seq
        (.seq (.guard (expressionValid plus2Increment))
          (.modify fun state => state.write 1 u32
            (expressionValue plus2Increment state)))
        (.seq
          (.seq (.guard (expressionValid plus2Decrement))
            (.modify fun state => state.write 2 u32
              (expressionValue plus2Decrement state)))
          .skip))
      .skip)

def generatedShape : L1.Syntax Full :=
  .seq (.modify State.resetReturn)
    (.seq
      (.catch
        (.seq
          (.while (fun state => plus2Condition.eval state != some 0)
            generatedLoopBody)
          (.seq
            (.seq (.guard (expressionValid (.variable u32 1)))
              (.seq (.modify fun state => state.returnValue u32
                (expressionValue (.variable u32 1) state)) .throw))
            .skip))
        .skip)
      (.seq (.modify expectedPlus2.finalize)
        (.seq (.guard fun state => state.returned = true) .skip)))

def fixtureSimplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment plus2EmitsSupported

theorem commandEq : expectedPlus2.command = plus2.command :=
  congrArg Function.command plus2_is_resolved_while_body.symm

def transportedSupport : SimplConv.Kernel.Supported plus2.command :=
  expectedPlus2.supported.transport commandEq

def simplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment transportedSupport

theorem fixture_simpl_target_eq :
    fixtureSimplCertificate.target = simplCertificate.target := by
  unfold fixtureSimplCertificate simplCertificate
  rw [SimplConv.Kernel.Supported.unique plus2EmitsSupported transportedSupport]

theorem simpl_generated_shape : simplCertificate.target = generatedShape := by
  unfold simplCertificate transportedSupport
  rw [ML.SimplConv.simplConv_transport_target]
  simp [ML.SimplConv.simplConv, expectedPlus2, Function.supported,
    _root_.Zag.Lang.AutoCorres.CParser.ScalarSimpl.supported,
    Function.command, compile, plus2Loop, plus2LoopBody, generatedLoopBody,
    generatedShape, expressionValue]
  repeat first | apply And.intro | rfl

/-- The exact L1 syntax emitted from the fixture certificate. -/
def generatedL1 : L1.Syntax Full := fixtureSimplCertificate.target

private theorem reset_update_eq :
    State.resetReturn =
      ML.LocalVarExtract.Source.localTransform model resetReturned := by
  funext state
  cases state
  rfl

private theorem finalize_update_eq :
    expectedPlus2.finalize =
      ML.LocalVarExtract.Source.localTransform model keepReturned := by
  funext state
  cases state
  simp [Function.finalize, ML.LocalVarExtract.Source.localTransform, model,
    keepReturned, expectedPlus2]

private theorem write_update_eq (id : Nat) (type : ScalarType) (expression : Expr) :
    (fun state => state.write id type (expressionValue expression state)) =
      ML.LocalVarExtract.Source.globalTransform model
        (updateExpression id type expression) := by
  funext state
  cases state
  rfl

private theorem return_update_eq :
    L1.modify (fun state => state.returnValue u32
        (expressionValue (.variable u32 1) state)) =
      L1.seq
        (L1.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
        (L1.modify (ML.LocalVarExtract.Source.localTransform model setReturned)) := by
  funext state
  have combinedUpdate :
      ML.LocalVarExtract.Source.localTransform model setReturned
          (ML.LocalVarExtract.Source.globalTransform model setResult state) =
        state.returnValue u32 (expressionValue (.variable u32 1) state) := by
    cases state
    rfl
  apply behavior_ext
  · funext outcome
    apply propext
    rcases outcome with ⟨result, post⟩
    cases result with
    | error exception =>
        change (Except.error exception, post) ∈
            (L2.modify (fun state => state.returnValue u32
              (expressionValue (.variable u32 1) state)) state).results ↔
          (Except.error exception, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq]
    | ok result =>
        change (Except.ok result, post) ∈
            (L2.modify (fun state => state.returnValue u32
              (expressionValue (.variable u32 1) state)) state).results ↔
          (Except.ok result, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq, combinedUpdate]
  · apply propext
    change (L2.modify (Exception := Unit) (fun state => state.returnValue u32
        (expressionValue (.variable u32 1) state)) state).failed ↔
      (L2.seq
        (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
        (fun _ => L2.modify
          (ML.LocalVarExtract.Source.localTransform model setReturned)) state).failed
    simp [L2.seq]

private theorem split_valid_full (expression : Expr) :
    (fun state => splitValid expression
      (model.projectLocals state) (model.projectGlobals state)) =
      expressionValid expression := by
  funext state
  simp [splitValid, model]

private theorem split_loop_test_full :
    (fun state => splitLoopTest
      (model.projectLocals state) (model.projectGlobals state)) =
      (fun state => (plus2Condition.eval state != some 0) = true) := by
  funext state
  simp [splitLoopTest, model]

private theorem split_returned_full :
    (fun state => splitReturned
      (model.projectLocals state) (model.projectGlobals state)) =
      (fun state => state.returned = true) := by
  funext state
  rfl

theorem fixture_simpl_endpoint : generatedL1.denote = normalizedL1.denote := by
  unfold generatedL1
  rw [fixture_simpl_target_eq]
  rw [simpl_generated_shape]
  simp only [generatedShape, generatedLoopBody, normalizedL1,
    normalizedLoopBody, L1.Syntax.denote]
  rw [reset_update_eq, finalize_update_eq, return_update_eq,
    write_update_eq 1 u32 plus2Increment, write_update_eq 2 u32 plus2Decrement]
  rw [split_valid_full plus2Condition, split_valid_full plus2Increment,
    split_valid_full plus2Decrement, split_valid_full (.variable u32 1),
    split_loop_test_full, split_returned_full]

theorem normalizedL1Corres :
    L1.L1Corres false emptyEnvironment normalizedL1.denote plus2.command := by
  rw [← fixture_simpl_endpoint]
  exact fixtureSimplCertificate.corres

def lveLoopBodySupported : ML.LocalVarExtract.Supported model normalizedLoopBody :=
  .seq
    (.seq (.guard (splitValid plus2Condition)) .skip)
    (.seq
      (.seq
        (.seq (.guard (splitValid plus2Increment))
          (.globalUpdate (updateExpression 1 u32 plus2Increment)))
        (.seq
          (.seq (.guard (splitValid plus2Decrement))
            (.globalUpdate (updateExpression 2 u32 plus2Decrement)))
          .skip))
      .skip)

def lveSupported : ML.LocalVarExtract.Supported model normalizedL1 :=
  .seq (.localUpdate resetReturned)
    (.seq
      (.catch
        (.seq (.loop splitLoopTest lveLoopBodySupported)
          (.seq
            (.seq (.guard (splitValid (.variable u32 1)))
              (.seq
                (.seq (.globalUpdate setResult) (.localUpdate setReturned))
                .throw))
            .skip))
        .skip)
      (.seq (.localUpdate keepReturned)
        (.seq (.guard splitReturned) .skip)))

def lveCertificate := ML.LocalVarExtract.extractCanonical model lveSupported

theorem lve_consumes_fixture_endpoint (locals : Locals) :
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        lveCertificate.target locals)
      generatedL1.denote := by
  rw [fixture_simpl_endpoint]
  exact lveCertificate.corres locals

def readResult (globals : Globals) : BitVec 32 := BitVec.ofInt 32 globals.result

def projectedL2Syntax : L2.Syntax Globals Bool (BitVec 32) :=
  .seq (lveCertificate.target false) fun _ => .gets readResult []

def projectedL2 : L2.L2Program Globals Bool (BitVec 32) := projectedL2Syntax.denote

private theorem projectCorres :
    CorresXF id (fun _ post => readResult post)
      (fun exception _ => exception) (fun _ => True)
      projectedL2
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote
        lveCertificate.target false) := by
  intro state hypothesis
  constructor
  · intro result post member
    cases result with
    | error exception => exact ⟨Except.error exception, post, member, rfl⟩
    | ok value =>
        refine ⟨Except.ok value, post, member, ?_⟩
        simp [L2.gets]
  · intro failed
    apply hypothesis.2
    exact Or.inl failed

theorem projectedL2Corres :
    L2.L2Corres model.projectGlobals
      (fun state => readResult (model.projectGlobals state))
      model.projectLocals
      (fun state => model.projectLocals state = false)
      projectedL2 generatedL1.denote := by
  rw [fixture_simpl_endpoint]
  simpa [L2.L2Corres, Function.comp_def] using
    (CorresXF.merge (lveCertificate.corres false) projectCorres)

end

end Zag.Test.AutoCorres.CParser.ScalarSimpl.Plus2Pipeline
