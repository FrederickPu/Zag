import Lang.AutoCorres.Simpl.Language

/-!
# SIMPL big-step semantics

Corresponds to [`tools/c-parser/Simpl/Semantic.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/c-parser/Simpl/Semantic.thy).
-/

namespace Zag.Lang.AutoCorres.Simpl

universe u v w

inductive XState (State : Type u) (Fault : Type w) where
| normal (state : State)
| abrupt (state : State)
| fault (label : Fault)
| stuck

def XState.IsAbrupt : XState State Fault -> Prop
| .abrupt _ => True
| _ => False

abbrev Body (State : Type u) (Proc : Type v) (Fault : Type w) :=
  Proc -> Option (Com State Proc Fault)

inductive Exec (env : Body State Proc Fault) :
    Com State Proc Fault -> XState State Fault -> XState State Fault -> Prop where
| skip : Exec env .Skip (.normal s) (.normal s)
| guard :
    g s ->
    Exec env body (.normal s) result ->
    Exec env (.Guard fault g body) (.normal s) result
| guardFault :
    Not (g s) ->
    Exec env (.Guard fault g body) (.normal s) (.fault fault)
| faultProp : Exec env command (.fault fault) (.fault fault)
| basic : Exec env (.Basic transform) (.normal s) (.normal (transform s))
| spec :
    relation (s, t) ->
    Exec env (.Spec relation) (.normal s) (.normal t)
| specStuck :
    (forall t, Not (relation (s, t))) ->
    Exec env (.Spec relation) (.normal s) .stuck
| seq :
    Exec env first (.normal s) middle ->
    Exec env second middle result ->
    Exec env (.Seq first second) (.normal s) result
| condTrue :
    test s ->
    Exec env thenCom (.normal s) result ->
    Exec env (.Cond test thenCom elseCom) (.normal s) result
| condFalse :
    Not (test s) ->
    Exec env elseCom (.normal s) result ->
    Exec env (.Cond test thenCom elseCom) (.normal s) result
| whileTrue :
    test s ->
    Exec env body (.normal s) middle ->
    Exec env (.While test body) middle result ->
    Exec env (.While test body) (.normal s) result
| whileFalse :
    Not (test s) ->
    Exec env (.While test body) (.normal s) (.normal s)
| call :
    env proc = some body ->
    Exec env body (.normal s) result ->
    Exec env (.Call proc) (.normal s) result
| callUndefined :
    env proc = none ->
    Exec env (.Call proc) (.normal s) .stuck
| stuckProp : Exec env command .stuck .stuck
| dynCom :
    Exec env (command s) (.normal s) result ->
    Exec env (.DynCom command) (.normal s) result
| throw : Exec env .Throw (.normal s) (.abrupt s)
| abruptProp : Exec env command (.abrupt s) (.abrupt s)
| catchMatch :
    Exec env body (.normal s) (.abrupt thrown) ->
    Exec env handler (.normal thrown) result ->
    Exec env (.Catch body handler) (.normal s) result
| catchMiss :
    Exec env body (.normal s) result ->
    Not result.IsAbrupt ->
    Exec env (.Catch body handler) (.normal s) result

theorem skip_exec (env : Body State Proc Fault) (s : State) :
    Exec env .Skip (.normal s) (.normal s) :=
  .skip

theorem guard_fault_exec (env : Body State Proc Fault) (guard : StatePred State)
    (fault : Fault) (body : Com State Proc Fault) (s : State) (h : Not (guard s)) :
    Exec env (.Guard fault guard body) (.normal s) (.fault fault) :=
  .guardFault h

private def oneOrTwo : StateRel Nat :=
  fun pair => pair.1 = 0 /\ (pair.2 = 1 \/ pair.2 = 2)

def nondeterministicSpec : Com Nat Unit Unit :=
  .Spec oneOrTwo

theorem nondeterministic_spec_branches (env : Body Nat Unit Unit) :
    Exec env nondeterministicSpec (.normal 0) (.normal 1) /\
      Exec env nondeterministicSpec (.normal 0) (.normal 2) := by
  constructor
  · exact .spec (by simp [oneOrTwo])
  · exact .spec (by simp [oneOrTwo])

def emptyBody : Body State Proc Fault :=
  fun _ => none

theorem undefined_call_stuck (proc : Proc) (s : State) :
    Exec (emptyBody : Body State Proc Fault) (.Call proc) (.normal s) .stuck :=
  .callUndefined rfl

end Zag.Lang.AutoCorres.Simpl
