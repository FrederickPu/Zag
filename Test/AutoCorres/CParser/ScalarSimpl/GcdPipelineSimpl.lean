import Test.AutoCorres.CParser.ScalarSimpl.GcdExecution
import Test.AutoCorres.CParser.ScalarSimpl.Plus2PipelineSimpl

/-! # Fixture-derived `gcd` through SimplConv and local-variable extraction -/

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline

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
abbrev Globals := Plus2Pipeline.Globals

def model : ML.LocalVarExtract.StateModel Full Locals Globals := Plus2Pipeline.model

def expressionValid := Plus2Pipeline.expressionValid
def expressionValue := Plus2Pipeline.expressionValue
def resetReturned := Plus2Pipeline.resetReturned
def keepReturned := Plus2Pipeline.keepReturned
def setReturned := Plus2Pipeline.setReturned
def updateExpression := Plus2Pipeline.updateExpression
def splitValid := Plus2Pipeline.splitValid
def splitReturned := Plus2Pipeline.splitReturned

def clearSlot (id : Nat) (locals : Locals) (globals : Globals) : Globals :=
  model.projectGlobals ((model.assemble locals globals).clear id)

def setResult (locals : Locals) (globals : Globals) : Globals :=
  model.projectGlobals
    ((model.assemble locals globals).returnValue u32
      (expressionValue (.variable u32 2) (model.assemble locals globals)))

def splitLoopTest (locals : Locals) (globals : Globals) : Prop :=
  gcdCondition.eval (model.assemble locals globals) != some 0

def normalizedLoopBody : L1.Syntax Full :=
  .seq
    (.seq (.guard fun state => splitValid gcdCondition
        (model.projectLocals state) (model.projectGlobals state)) .skip)
    (.seq
      (.seq
        (.seq (.guard fun state => splitValid (.variable u32 1)
            (model.projectLocals state) (model.projectGlobals state))
          (.modify (ML.LocalVarExtract.Source.globalTransform model
            (updateExpression 3 u32 (.variable u32 1)))))
        (.seq
          (.seq (.guard fun state => splitValid gcdRemainder
              (model.projectLocals state) (model.projectGlobals state))
            (.modify (ML.LocalVarExtract.Source.globalTransform model
              (updateExpression 1 u32 gcdRemainder))))
          (.seq
            (.seq (.guard fun state => splitValid (.variable u32 3)
                (model.projectLocals state) (model.projectGlobals state))
              (.modify (ML.LocalVarExtract.Source.globalTransform model
                (updateExpression 2 u32 (.variable u32 3)))))
            .skip)))
      .skip)

def normalizedDeclaration : L1.Syntax Full :=
  .modify (ML.LocalVarExtract.Source.globalTransform model (clearSlot 3))

def normalizedL1 : L1.Syntax Full :=
  .seq (.modify (ML.LocalVarExtract.Source.localTransform model resetReturned))
    (.seq
      (.catch
        (.seq normalizedDeclaration
          (.seq
            (.while (fun state => splitLoopTest
                (model.projectLocals state) (model.projectGlobals state))
              normalizedLoopBody)
            (.seq
              (.seq (.guard fun state => splitValid (.variable u32 2)
                  (model.projectLocals state) (model.projectGlobals state))
                (.seq
                  (.seq (.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
                    (.modify (ML.LocalVarExtract.Source.localTransform model setReturned)))
                  .throw))
              .skip)))
        .skip)
      (.seq (.modify (ML.LocalVarExtract.Source.localTransform model keepReturned))
        (.seq (.guard fun state => splitReturned
          (model.projectLocals state) (model.projectGlobals state)) .skip)))

def generatedLoopBody : L1.Syntax Full :=
  .seq
    (.seq (.guard (expressionValid gcdCondition)) .skip)
    (.seq
      (.seq
        (.seq (.guard (expressionValid (.variable u32 1)))
          (.modify fun state => state.write 3 u32
            (expressionValue (.variable u32 1) state)))
        (.seq
          (.seq (.guard (expressionValid gcdRemainder))
            (.modify fun state => state.write 1 u32
              (expressionValue gcdRemainder state)))
          (.seq
            (.seq (.guard (expressionValid (.variable u32 3)))
              (.modify fun state => state.write 2 u32
                (expressionValue (.variable u32 3) state)))
            .skip)))
      .skip)

def generatedShape : L1.Syntax Full :=
  .seq (.modify State.resetReturn)
    (.seq
      (.catch
        (.seq (.modify fun state => state.clear 3)
          (.seq
            (.while (fun state => gcdCondition.eval state != some 0)
              generatedLoopBody)
            (.seq
              (.seq (.guard (expressionValid (.variable u32 2)))
                (.seq (.modify fun state => state.returnValue u32
                  (expressionValue (.variable u32 2) state)) .throw))
              .skip)))
        .skip)
      (.seq (.modify expectedGcd.finalize)
        (.seq (.guard fun state => state.returned = true) .skip)))

def fixtureSimplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment gcdEmitsSupported

theorem commandEq : expectedGcd.command = gcdFunction.command :=
  congrArg Function.command gcd_is_exact_resolved_function.symm

def transportedSupport : SimplConv.Kernel.Supported gcdFunction.command :=
  expectedGcd.supported.transport commandEq

def simplCertificate :=
  ML.SimplConv.simplConv false emptyEnvironment transportedSupport

theorem fixture_simpl_target_eq :
    fixtureSimplCertificate.target = simplCertificate.target := by
  unfold fixtureSimplCertificate simplCertificate
  rw [SimplConv.Kernel.Supported.unique gcdEmitsSupported transportedSupport]

theorem simpl_generated_shape : simplCertificate.target = generatedShape := by
  unfold simplCertificate transportedSupport
  rw [ML.SimplConv.simplConv_transport_target]
  simp [ML.SimplConv.simplConv, expectedGcd, Function.supported,
    _root_.Zag.Lang.AutoCorres.CParser.ScalarSimpl.supported,
    Function.command, compile, gcdLoop, gcdLoopBody,
    generatedLoopBody, generatedShape, expressionValue]
  repeat first | apply And.intro | rfl

def generatedL1 : L1.Syntax Full := fixtureSimplCertificate.target

private theorem reset_update_eq :
    State.resetReturn = ML.LocalVarExtract.Source.localTransform model resetReturned := by
  funext state
  cases state
  rfl

private theorem finalize_update_eq :
    expectedGcd.finalize = ML.LocalVarExtract.Source.localTransform model keepReturned := by
  funext state
  cases state
  simp [Function.finalize, ML.LocalVarExtract.Source.localTransform, model,
    keepReturned, expectedGcd, Plus2Pipeline.keepReturned, Plus2Pipeline.model]

private theorem clear_update_eq (id : Nat) :
    (fun state : State => state.clear id) =
      ML.LocalVarExtract.Source.globalTransform model (clearSlot id) := by
  funext state
  cases state
  rfl

private theorem write_update_eq (id : Nat) (type : ScalarType) (expression : Expr) :
    (fun state => state.write id type (expressionValue expression state)) =
      ML.LocalVarExtract.Source.globalTransform model
        (updateExpression id type expression) := by
  funext state
  cases state
  rfl

private theorem return_update_eq :
    L1.modify (fun state => state.returnValue u32
        (expressionValue (.variable u32 2) state)) =
      L1.seq
        (L1.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
        (L1.modify (ML.LocalVarExtract.Source.localTransform model setReturned)) := by
  funext state
  have combinedUpdate :
      ML.LocalVarExtract.Source.localTransform model setReturned
          (ML.LocalVarExtract.Source.globalTransform model setResult state) =
        state.returnValue u32 (expressionValue (.variable u32 2) state) := by
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
              (expressionValue (.variable u32 2) state)) state).results ↔
          (Except.error exception, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq]
    | ok result =>
        change (Except.ok result, post) ∈
            (L2.modify (fun state => state.returnValue u32
              (expressionValue (.variable u32 2) state)) state).results ↔
          (Except.ok result, post) ∈
            (L2.seq
              (L2.modify (ML.LocalVarExtract.Source.globalTransform model setResult))
              (fun _ => L2.modify
                (ML.LocalVarExtract.Source.localTransform model setReturned)) state).results
        simp [L2.seq, combinedUpdate]
  · apply propext
    change (L2.modify (Exception := Unit) (fun state => state.returnValue u32
        (expressionValue (.variable u32 2) state)) state).failed ↔
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
  simp [splitValid, expressionValid, model, Plus2Pipeline.splitValid,
    Plus2Pipeline.expressionValid, Plus2Pipeline.model]

private theorem split_loop_test_full :
    (fun state => splitLoopTest
      (model.projectLocals state) (model.projectGlobals state)) =
      (fun state => (gcdCondition.eval state != some 0) = true) := by
  funext state
  simp [splitLoopTest, model, Plus2Pipeline.model]

private theorem split_returned_full :
    (fun state => splitReturned
      (model.projectLocals state) (model.projectGlobals state)) =
      (fun state => state.returned = true) := by
  funext state
  rfl

theorem fixture_simpl_endpoint : generatedL1.denote = normalizedL1.denote := by
  unfold generatedL1
  rw [fixture_simpl_target_eq, simpl_generated_shape]
  simp only [generatedShape, generatedLoopBody, normalizedL1,
    normalizedDeclaration, normalizedLoopBody, L1.Syntax.denote]
  rw [reset_update_eq, finalize_update_eq, return_update_eq, clear_update_eq 3,
    write_update_eq 3 u32 (.variable u32 1),
    write_update_eq 1 u32 gcdRemainder,
    write_update_eq 2 u32 (.variable u32 3)]
  rw [split_valid_full gcdCondition, split_valid_full (.variable u32 1),
    split_valid_full gcdRemainder, split_valid_full (.variable u32 3),
    split_valid_full (.variable u32 2), split_loop_test_full, split_returned_full]

theorem normalizedL1Corres :
    L1.L1Corres false emptyEnvironment normalizedL1.denote gcdFunction.command := by
  rw [← fixture_simpl_endpoint]
  exact fixtureSimplCertificate.corres

def lveLoopBodySupported : ML.LocalVarExtract.Supported model normalizedLoopBody :=
  .seq
    (.seq (.guard (splitValid gcdCondition)) .skip)
    (.seq
      (.seq
        (.seq (.guard (splitValid (.variable u32 1)))
          (.globalUpdate (updateExpression 3 u32 (.variable u32 1))))
        (.seq
          (.seq (.guard (splitValid gcdRemainder))
            (.globalUpdate (updateExpression 1 u32 gcdRemainder)))
          (.seq
            (.seq (.guard (splitValid (.variable u32 3)))
              (.globalUpdate (updateExpression 2 u32 (.variable u32 3))))
            .skip)))
      .skip)

def lveSupported : ML.LocalVarExtract.Supported model normalizedL1 :=
  .seq (.localUpdate resetReturned)
    (.seq
      (.catch
        (.seq (.globalUpdate (clearSlot 3))
          (.seq (.loop splitLoopTest lveLoopBodySupported)
            (.seq
              (.seq (.guard (splitValid (.variable u32 2)))
                (.seq
                  (.seq (.globalUpdate setResult) (.localUpdate setReturned))
                  .throw))
              .skip)))
        .skip)
      (.seq (.localUpdate keepReturned)
        (.seq (.guard splitReturned) .skip)))

def lveCertificate := ML.LocalVarExtract.extractCanonical model lveSupported

theorem lve_consumes_fixture_endpoint (locals : Locals) :
    L2.L2Corres model.projectGlobals model.projectLocals model.projectLocals
      (fun state => model.projectLocals state = locals)
      (LocalVarExtract.Kernel.CanonicalTarget.Syntax.denote lveCertificate.target locals)
      generatedL1.denote := by
  rw [fixture_simpl_endpoint]
  exact lveCertificate.corres locals

def readResult (globals : Globals) : Int := globals.result

def projectedL2Syntax : L2.Syntax Globals Bool Int :=
  .seq (lveCertificate.target false) fun _ => .gets readResult []

def projectedL2 : L2.L2Program Globals Bool Int := projectedL2Syntax.denote

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

end Zag.Test.AutoCorres.CParser.ScalarSimpl.GcdPipeline
