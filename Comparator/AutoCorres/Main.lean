import Lang.AutoCorres.SimplConv
import Lang.AutoCorres.LocalVarExtract
import Lang.AutoCorres.HeapLift
import Lang.AutoCorres.WordAbstract
import Lang.AutoCorres.TypeStrengthen

/-!
# Trusted AutoCorres Comparator interface

This import boundary contains the IRs, denotations, support indices, and
correspondence statements. It intentionally imports no `Lang.AutoCorres.ML`
module and contains no lifting implementation.
-/

namespace Comparator.AutoCorres

open Zag.Lang.AutoCorres

universe u v w x y z

/-- Trusted statement of the final SIMPL-to-monad correspondence. -/
def acCorres
    {ConcreteState : Type u} {State : Type v} {Result : Type w}
    {Exception : Type x} {Proc : Type y} {Fault : Type z}
    (stateProject : ConcreteState -> State)
    (checkTermination : Bool)
    (env : Simpl.Body ConcreteState Proc Fault)
    (returnExtract : ConcreteState -> Result)
    (precondition : ConcreteState -> Prop)
    (target : L2.L2Program State Exception Result)
    (source : Simpl.Com ConcreteState Proc Fault) : Prop :=
  forall state, (precondition state ∧ ¬ (target (stateProject state)).failed) ->
    (forall final, Simpl.Exec env source (.normal state) final ->
      exists post, final = .normal post ∧
        (Except.ok (returnExtract post), stateProject post) ∈
          (target (stateProject state)).results) ∧
    (checkTermination = true ->
      Simpl.Terminates env source (.normal state))

end Comparator.AutoCorres
