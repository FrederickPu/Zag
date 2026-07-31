import Lang.SSA

/-!
# SIMPL language

Corresponds to [`tools/c-parser/Simpl/Language.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/c-parser/Simpl/Language.thy).
-/

namespace Zag.Lang.AutoCorres.Simpl

universe u v w

abbrev StatePred (State : Type u) := State -> Prop
abbrev StateRel (State : Type u) := State × State -> Prop

inductive Com (State : Type u) (Proc : Type v) (Fault : Type w) where
| Skip
| Basic (transform : State -> State)
| Spec (relation : StateRel State)
| Seq (first second : Com State Proc Fault)
| Cond (test : StatePred State) (thenCom elseCom : Com State Proc Fault)
| While (test : StatePred State) (body : Com State Proc Fault)
| Call (proc : Proc)
| DynCom (command : State -> Com State Proc Fault)
| Guard (fault : Fault) (guard : StatePred State) (body : Com State Proc Fault)
| Throw
| Catch (body handler : Com State Proc Fault)

end Zag.Lang.AutoCorres.Simpl
