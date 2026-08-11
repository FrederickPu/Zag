import Lang.AutoCorres.SimplConv

/-!
# Recursive SimplConv families

Calls inside one SCC remain symbolic while its bodies are translated. Calls to
an already scheduled SCC carry an ordinary callee certificate and do not consume
the current SCC's measure. Instantiation produces canonical `L1.Syntax`.

The correspondence theorem is bounded partial correctness: at an insufficient
measure the target reaches `L1.fail`, so `L1Corres` has no nonfailure premise.
Clients claiming a concrete result must separately prove that their selected
measure does not fail.
-/

namespace Zag.Lang.AutoCorres.SimplConv.Recursive

open Zag.Lang.AutoCorres

universe u v w

inductive Syntax (Member : Type v) (State : Type u) where
  | skip
  | seq (first second : Syntax Member State)
  | modify (transform : State → State)
  | condition (test : State → Prop) (thenBranch elseBranch : Syntax Member State)
  | «catch» (body handler : Syntax Member State)
  | «while» (test : State → Prop) (body : Syntax Member State)
  | throw
  | spec (relation : Set (State × State))
  | guard (test : State → Prop) (body : Syntax Member State)
  | internalCall (member : Member)
  | externalCall (target : L1.Syntax State)

namespace Syntax

/-- Substitute current-SCC calls and retain certified external call boundaries. -/
def instantiate (members : Member → L1.Syntax State) :
    Syntax Member State → L1.Syntax State
  | .skip => .skip
  | .seq first second => .seq (first.instantiate members) (second.instantiate members)
  | .modify transform => .modify transform
  | .condition test thenBranch elseBranch =>
      .condition test (thenBranch.instantiate members) (elseBranch.instantiate members)
  | .catch body handler => .catch (body.instantiate members) (handler.instantiate members)
  | .while test body => .while test (body.instantiate members)
  | .throw => .throw
  | .spec relation => .spec relation
  | .guard test body => .seq (.guard test) (body.instantiate members)
  | .internalCall member => members member
  | .externalCall target => .call target

end Syntax

/-- Structural support for one body in a resolved procedure environment. -/
inductive Supported {State : Type u} {Proc : Type v} {Fault : Type w}
    {Member : Type v} (embed : Member → Proc) (env : Simpl.Body State Proc Fault) :
    Simpl.Com State Proc Fault → Syntax Member State → Type (max (u + 1) (v + 1) (w + 1)) where
  | skip : Supported embed env .Skip .skip
  | seq : Supported embed env first firstTarget → Supported embed env second secondTarget →
      Supported embed env (.Seq first second) (.seq firstTarget secondTarget)
  | basic (transform : State → State) :
      Supported embed env (.Basic transform) (.modify transform)
  | cond (test : State → Prop) :
      Supported embed env thenBranch thenTarget →
      Supported embed env elseBranch elseTarget →
      Supported embed env (.Cond test thenBranch elseBranch)
        (.condition test thenTarget elseTarget)
  | «catch» : Supported embed env body bodyTarget →
      Supported embed env handler handlerTarget →
      Supported embed env (.Catch body handler) (.catch bodyTarget handlerTarget)
  | «while» (test : State → Prop) : Supported embed env body bodyTarget →
      Supported embed env (.While test body) (.while test bodyTarget)
  | throw : Supported embed env .Throw .throw
  | guard (fault : Fault) (test : State → Prop) :
      Supported embed env body bodyTarget →
      Supported embed env (.Guard fault test body) (.guard test bodyTarget)
  | spec (relation : Simpl.StateRel State) :
      Supported embed env (.Spec relation) (.spec relation)
  | internalCall (member : Member) :
      Supported embed env (.Call (embed member)) (.internalCall member)
  | externalCall (procedure : Proc) (sourceBody : Simpl.Com State Proc Fault)
      (targetBody : L1.Syntax State) (defined : env procedure = some sourceBody)
      (corres : L1.L1Corres false env targetBody.denote sourceBody) :
      Supported embed env (.Call procedure) (.externalCall targetBody)

theorem Supported.corres
    {State : Type u} {Proc Member : Type v} {Fault : Type w}
    {embed : Member → Proc} {env : Simpl.Body State Proc Fault}
    {source : Simpl.Com State Proc Fault} {target : Syntax Member State}
    (supported : Supported embed env source target)
    (members : Member → L1.Syntax State)
    (internalCorres : ∀ member,
      L1.L1Corres false env (members member).denote (.Call (embed member))) :
    L1.L1Corres false env (target.instantiate members).denote source := by
  induction supported with
  | skip => exact L1.L1Corres_skip false env
  | seq _ _ firstCorrect secondCorrect =>
      exact L1.L1Corres_seq firstCorrect secondCorrect
  | basic transform => exact L1.L1Corres_modify false env transform
  | cond test _ _ thenCorrect elseCorrect =>
      exact L1.L1Corres_condition thenCorrect elseCorrect
  | «catch» _ _ bodyCorrect handlerCorrect =>
      exact L1.L1Corres_catch bodyCorrect handlerCorrect
  | «while» test _ bodyCorrect => exact L1.L1Corres_while bodyCorrect
  | throw => exact L1.L1Corres_throw false env
  | guard fault test _ bodyCorrect => exact L1.L1Corres_guard bodyCorrect fault
  | spec relation => exact L1.L1Corres_spec false env relation
  | internalCall member => exact internalCorres member
  | externalCall procedure sourceBody targetBody defined bodyCorres =>
      exact L1.L1Corres_call defined bodyCorres

/-- All translated bodies in one SCC, indexed only by its member subtype. -/
structure Family {State : Type u} {Proc Member : Type v} {Fault : Type w}
    (embed : Member → Proc) (env : Simpl.Body State Proc Fault) where
  sourceBody : Member → Simpl.Com State Proc Fault
  targetBody : Member → Syntax Member State
  defined : ∀ member, env (embed member) = some (sourceBody member)
  supported : ∀ member, Supported embed env (sourceBody member) (targetBody member)

namespace Family

variable {State : Type u} {Proc Member : Type v} {Fault : Type w}
variable {embed : Member → Proc} {env : Simpl.Body State Proc Fault}

/-- Canonical L1 artifact for one explicit SCC recursion measure. -/
def atMeasureSyntax (family : Family embed env) : Nat → Member → L1.Syntax State
  | 0, _ => .fail
  | measure + 1, member =>
      (family.targetBody member).instantiate (family.atMeasureSyntax measure)

noncomputable def atMeasure (family : Family embed env) (measure : Nat)
    (member : Member) : L1.L1Program State :=
  (family.atMeasureSyntax measure member).denote

theorem atMeasure_call_corres (family : Family embed env) :
    ∀ measure member,
      L1.L1Corres false env (family.atMeasure measure member) (.Call (embed member))
  | 0, member => by
      simpa [atMeasure, atMeasureSyntax] using
        (L1.L1Corres_fail false env (.Call (embed member)))
  | measure + 1, member => by
      have bodyCorrect : L1.L1Corres false env
          ((family.targetBody member).instantiate (family.atMeasureSyntax measure)).denote
          (family.sourceBody member) :=
        (family.supported member).corres (family.atMeasureSyntax measure)
          (fun called => family.atMeasure_call_corres measure called)
      simpa [atMeasure, atMeasureSyntax] using
        L1.L1Corres_call (family.defined member) bodyCorrect

theorem atMeasure_body_corres (family : Family embed env) (measure : Nat)
    (member : Member) :
    L1.L1Corres false env (family.atMeasure (measure + 1) member)
      (family.sourceBody member) := by
  simpa [atMeasure, atMeasureSyntax] using
    (family.supported member).corres (family.atMeasureSyntax measure)
      (fun called => family.atMeasure_call_corres measure called)

end Family

end Zag.Lang.AutoCorres.SimplConv.Recursive
