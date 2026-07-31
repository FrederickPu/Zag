import Lang.AutoCorres.Simpl.Semantic

/-!
# SIMPL termination semantics

Corresponds to [`tools/c-parser/Simpl/Termination.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/c-parser/Simpl/Termination.thy).
-/

namespace Zag.Lang.AutoCorres.Simpl

universe u v w

/-!
This is SIMPL's separate all-branches termination judgment. In particular,
`Spec` and an undefined `Call` terminate because their execution is stuck;
successful evaluation is not required. Sequential composition, loops, and
catches quantify over every applicable execution branch.
-/

inductive Terminates (env : Body State Proc Fault) :
    Com State Proc Fault -> XState State Fault -> Prop where
| skip : Terminates env .Skip (.normal s)
| basic : Terminates env (.Basic transform) (.normal s)
| spec : Terminates env (.Spec relation) (.normal s)
| guard :
    g s ->
    Terminates env body (.normal s) ->
    Terminates env (.Guard fault g body) (.normal s)
| guardFault :
    Not (g s) ->
    Terminates env (.Guard fault g body) (.normal s)
| fault : Terminates env command (.fault label)
| seq :
    Terminates env first (.normal s) ->
    (forall result, Exec env first (.normal s) result -> Terminates env second result) ->
    Terminates env (.Seq first second) (.normal s)
| condTrue :
    test s ->
    Terminates env thenCom (.normal s) ->
    Terminates env (.Cond test thenCom elseCom) (.normal s)
| condFalse :
    Not (test s) ->
    Terminates env elseCom (.normal s) ->
    Terminates env (.Cond test thenCom elseCom) (.normal s)
| whileTrue :
    test s ->
    Terminates env body (.normal s) ->
    (forall result,
      Exec env body (.normal s) result -> Terminates env (.While test body) result) ->
    Terminates env (.While test body) (.normal s)
| whileFalse :
    Not (test s) ->
    Terminates env (.While test body) (.normal s)
| call :
    env proc = some body ->
    Terminates env body (.normal s) ->
    Terminates env (.Call proc) (.normal s)
| callUndefined :
    env proc = none ->
    Terminates env (.Call proc) (.normal s)
| stuck : Terminates env command .stuck
| dynCom :
    Terminates env (command s) (.normal s) ->
    Terminates env (.DynCom command) (.normal s)
| throw : Terminates env .Throw (.normal s)
| abrupt : Terminates env command (.abrupt s)
| catch :
    Terminates env body (.normal s) ->
    (forall thrown,
      Exec env body (.normal s) (.abrupt thrown) -> Terminates env handler (.normal thrown)) ->
    Terminates env (.Catch body handler) (.normal s)

theorem undefined_call_terminates (proc : Proc) (s : State) :
    Terminates (emptyBody : Body State Proc Fault) (.Call proc) (.normal s) :=
  .callUndefined rfl

end Zag.Lang.AutoCorres.Simpl
