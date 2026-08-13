import Lean.Parser
import Lang.AutoCorres.AutoCorres

namespace Zag.Lang.AutoCorres

namespace CorresXF

/-- A generated target tied to its exact source by a kernel-checked correspondence. -/
structure Refinement
    {ConcreteState AbstractState ConcreteResult AbstractResult : Type}
    {ConcreteException AbstractException : Type}
    (stateMap : ConcreteState → AbstractState)
    (normalMap : ConcreteResult → ConcreteState → AbstractResult)
    (exceptionMap : ConcreteException → ConcreteState → AbstractException)
    (precondition : ConcreteState → Prop)
    (source : Nondet ConcreteState (Except ConcreteException ConcreteResult)) where
  target : Nondet AbstractState (Except AbstractException AbstractResult)
  corres : CorresXF stateMap normalMap exceptionMap precondition target source

namespace Refinement

def ofCorresXF
    {ConcreteState AbstractState ConcreteResult AbstractResult : Type}
    {ConcreteException AbstractException : Type}
    {stateMap : ConcreteState → AbstractState}
    {normalMap : ConcreteResult → ConcreteState → AbstractResult}
    {exceptionMap : ConcreteException → ConcreteState → AbstractException}
    {precondition : ConcreteState → Prop}
    {source : Nondet ConcreteState (Except ConcreteException ConcreteResult)}
    {target : Nondet AbstractState (Except AbstractException AbstractResult)}
    (proof : CorresXF stateMap normalMap exceptionMap precondition target source) :
    Refinement stateMap normalMap exceptionMap precondition source :=
  ⟨target, proof⟩

def refl {State Exception Result : Type} (precondition : State → Prop)
    (source : Nondet State (Except Exception Result)) :
    Refinement id (fun result _ => result) (fun exception _ => exception)
      precondition source :=
  ⟨source, CorresXF.refl precondition source⟩

/-- Compose refinements only when the second consumes the first generated endpoint. -/
def andThen
    {ConcreteState MiddleState AbstractState : Type}
    {ConcreteResult MiddleResult AbstractResult : Type}
    {ConcreteException MiddleException AbstractException : Type}
    {stateMap₁ : ConcreteState → MiddleState}
    {normalMap₁ : ConcreteResult → ConcreteState → MiddleResult}
    {exceptionMap₁ : ConcreteException → ConcreteState → MiddleException}
    {precondition₁ : ConcreteState → Prop}
    {stateMap₂ : MiddleState → AbstractState}
    {normalMap₂ : MiddleResult → MiddleState → AbstractResult}
    {exceptionMap₂ : MiddleException → MiddleState → AbstractException}
    {precondition₂ : MiddleState → Prop}
    {source : Nondet ConcreteState (Except ConcreteException ConcreteResult)}
    (first : Refinement stateMap₁ normalMap₁ exceptionMap₁ precondition₁ source)
    (second : Refinement stateMap₂ normalMap₂ exceptionMap₂ precondition₂ first.target) :
    Refinement (stateMap₂ ∘ stateMap₁)
      (fun result state => normalMap₂ (normalMap₁ result state) (stateMap₁ state))
      (fun exception state =>
        exceptionMap₂ (exceptionMap₁ exception state) (stateMap₁ state))
      (fun state => precondition₁ state ∧ precondition₂ (stateMap₁ state)) source :=
  ⟨second.target, CorresXF.merge first.corres second.corres⟩

def ofL2Corres
    {ConcreteState AbstractState Exception Result : Type}
    {stateMap : ConcreteState → AbstractState}
    {returnExtract : ConcreteState → Result}
    {exceptionExtract : ConcreteState → Exception}
    {precondition : ConcreteState → Prop}
    {source : L1.L1Program ConcreteState}
    {target : L2.L2Program AbstractState Exception Result}
    (proof : L2.L2Corres stateMap returnExtract exceptionExtract precondition
      target source) :
    Refinement stateMap (fun _ state => returnExtract state)
      (fun _ state => exceptionExtract state) precondition source :=
  ⟨target, proof⟩

def ofHeapLift
    {ConcreteState AbstractState Exception Result : Type}
    {stateMap : ConcreteState → AbstractState}
    {source : L2.L2Program ConcreteState Exception Result}
    {target : L2.L2Program AbstractState Exception Result}
    (proof : HeapLift.L2Tcorres stateMap target source) :
    Refinement stateMap (fun result _ => result) (fun exception _ => exception)
      (fun _ => True) source :=
  ⟨target, proof⟩

def ofWordAbstract
    {State ConcreteException ConcreteResult AbstractException AbstractResult : Type}
    {precondition : State → Prop}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {source : L2.L2Program State ConcreteException ConcreteResult}
    {target : L2.L2Program State AbstractException AbstractResult}
    (proof : WordAbstract.corresTA precondition resultMap exceptionMap target source) :
    Refinement id (fun result _ => resultMap result)
      (fun exception _ => exceptionMap exception) precondition source :=
  ⟨target, proof⟩

def ofTypeStrengthen
    {State SourceException TargetException Result : Type}
    {source : L2.L2Program State SourceException Result}
    {target : L2.L2Program State TargetException Result}
    (exceptionMap : SourceException → State → TargetException)
    (equality : L2.call (Exception := TargetException) source = target) :
    Refinement id (fun result _ => result) exceptionMap (fun _ => True) source :=
  ⟨target, corresXF_from_L2_call exceptionMap equality⟩

end Refinement

end CorresXF

syntax (name := exactCorresXFRefinement) "exact_corresxf " term : tactic
syntax (name := exactAutoCorresRefinement) "exact_autocorres " term : tactic

macro_rules
  | `(tactic| exact_corresxf $refinement) =>
      `(tactic| exact ($refinement).corres)
  | `(tactic| exact_autocorres $certificate) =>
      `(tactic| exact ($certificate).acCorres)

namespace RefinementResult

/-- Extract the certified output of a refinement after its success obligation is proved. -/
def get : (result : Except ε α) → result.isOk → α
  | .error _, success => by
      change false = true at success
      exact False.elim (Bool.false_ne_true success)
  | .ok value, _ => value

theorem eq_ok_get (result : Except ε α) (success : result.isOk) :
    result = .ok (get result success) := by
  cases result with
  | error error =>
      change false = true at success
      exact False.elim (Bool.false_ne_true success)
  | ok value => rfl

/-- A successful refinement result paired with its exact generating equation. -/
structure Success (result : Except ε α) where
  artifact : α
  exact : result = .ok artifact

def success (result : Except ε α) (isOk : result.isOk) : Success result :=
  { artifact := get result isOk
    exact := eq_ok_get result isOk }

end RefinementResult

/-- Run a proof-producing refinement and bind its successful dependent result. -/
syntax (name := runRefinement)
  "run_refinement " ident " from " term " success_by " tacticSeq : command

macro_rules
  | `(run_refinement $name:ident from $runner:term success_by $proof:tacticSeq) =>
      `(def $name :=
          RefinementResult.get $runner (by $proof:tacticSeq))

end Zag.Lang.AutoCorres
