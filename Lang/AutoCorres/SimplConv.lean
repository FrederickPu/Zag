import Lang.AutoCorres.L1Peephole

/-!
# SIMPL conversion support

Corresponds only to [`tools/autocorres/SimplConv.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/SimplConv.thy).

The local language has no C-parser command sugar or `switch`, so the upstream
`L1unfold` declarations and `switch_alt_defs` are unsupported. It also has no
fixed-word library, so `sless_positive` and `sle_positive` are unsupported.
The upstream `L1except` collection additionally refers to unavailable
set-to-predicate declarations; its sequence normalization rule is provided by
the imported peephole module.
-/

namespace Zag.Lang.AutoCorres.SimplConv

open Zag.Lang.AutoCorres

universe u v w

namespace Kernel

/-- SimplConv emits the canonical reified L1 syntax consumed by later passes. -/
abbrev Target (State : Type u) := L1.Syntax State

namespace Target

/-- Compatibility name for the canonical L1 denotation. -/
noncomputable abbrev denote : Target State -> L1.L1Program State :=
  L1.Syntax.denote

end Target

/-- A generated reified target together with exact correspondence to its source. -/
structure Certificate (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) (source : Simpl.Com State Proc Fault) where
  target : Target State
  corres : L1.L1Corres checkTermination env target.denote source

/-- Reindex a certificate across an exact source-command equality. -/
def Certificate.transport {left right : Simpl.Com State Proc Fault}
    (equality : left = right)
    (certificate : Certificate checkTermination env left) :
    Certificate checkTermination env right :=
  equality ▸ certificate

@[simp] theorem Certificate.transport_target
    {left right : Simpl.Com State Proc Fault} (equality : left = right)
    (certificate : Certificate checkTermination env left) :
    (certificate.transport equality).target = certificate.target := by
  cases equality
  rfl

/-- Evidence that a command lies in the structural fragment handled by `simplConv`. -/
inductive Supported {State : Type u} {Proc : Type v} {Fault : Type w} :
    Simpl.Com State Proc Fault -> Type (max u v w) where
  | skip : Supported .Skip
  | seq {left right} : Supported left -> Supported right -> Supported (.Seq left right)
  | basic (transform : State -> State) : Supported (.Basic transform)
  | cond (test : State -> Prop) {thenCom elseCom} :
      Supported thenCom -> Supported elseCom -> Supported (.Cond test thenCom elseCom)
  | «catch» {body handler} :
      Supported body -> Supported handler -> Supported (.Catch body handler)
  | «while» (test : State -> Prop) {body} : Supported body -> Supported (.While test body)
  | throw : Supported .Throw
  | guard (fault : Fault) (test : State -> Prop) {body} :
      Supported body -> Supported (.Guard fault test body)
  | spec (relation : Simpl.StateRel State) : Supported (.Spec relation)

/-- Structural support evidence is uniquely determined by its indexed command. -/
theorem Supported.unique {source : Simpl.Com State Proc Fault}
    (left right : Supported source) : left = right := by
  induction left with
  | skip => cases right; rfl
  | seq _ _ leftIH rightIH =>
      cases right with
      | seq otherLeft otherRight =>
          rw [leftIH otherLeft, rightIH otherRight]
  | basic transform => cases right; rfl
  | cond test _ _ thenIH elseIH =>
      cases right with
      | cond _ otherThen otherElse =>
          rw [thenIH otherThen, elseIH otherElse]
  | «catch» _ _ bodyIH handlerIH =>
      cases right with
      | «catch» otherBody otherHandler =>
          rw [bodyIH otherBody, handlerIH otherHandler]
  | «while» test _ bodyIH =>
      cases right with
      | «while» _ otherBody => rw [bodyIH otherBody]
  | throw => cases right; rfl
  | guard fault test _ bodyIH =>
      cases right with
      | guard _ _ otherBody => rw [bodyIH otherBody]
  | spec relation => cases right; rfl

/-- Reindex structural support across an exact command equality. -/
def Supported.transport {left right : Simpl.Com State Proc Fault}
    (equality : left = right) (supported : Supported left) : Supported right :=
  equality ▸ supported

/--
Environment-indexed support used for whole-program conversion. A call carries
the exact previously certified callee instance selected by an SCC scheduler.
-/
inductive ProgramSupported {State : Type u} {Proc : Type v} {Fault : Type w}
    (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) :
    Simpl.Com State Proc Fault -> Type (max (u + 1) (v + 1) (w + 1)) where
  | skip : ProgramSupported checkTermination env .Skip
  | seq {left right} : ProgramSupported checkTermination env left ->
      ProgramSupported checkTermination env right ->
      ProgramSupported checkTermination env (.Seq left right)
  | basic (transform : State -> State) :
      ProgramSupported checkTermination env (.Basic transform)
  | cond (test : State -> Prop) {thenCom elseCom} :
      ProgramSupported checkTermination env thenCom ->
      ProgramSupported checkTermination env elseCom ->
      ProgramSupported checkTermination env (.Cond test thenCom elseCom)
  | «catch» {body handler} : ProgramSupported checkTermination env body ->
      ProgramSupported checkTermination env handler ->
      ProgramSupported checkTermination env (.Catch body handler)
  | «while» (test : State -> Prop) {body} :
      ProgramSupported checkTermination env body ->
      ProgramSupported checkTermination env (.While test body)
  | throw : ProgramSupported checkTermination env .Throw
  | guard (fault : Fault) (test : State -> Prop) {body} :
      ProgramSupported checkTermination env body ->
      ProgramSupported checkTermination env (.Guard fault test body)
  | spec (relation : Simpl.StateRel State) :
      ProgramSupported checkTermination env (.Spec relation)
  | «call» (proc : Proc) (sourceBody : Simpl.Com State Proc Fault)
      (targetBody : Target State)
      (defined : env proc = some sourceBody)
      (corres : L1.L1Corres checkTermination env targetBody.denote sourceBody) :
      ProgramSupported checkTermination env (.Call proc)

/-- Lift the call-free structural fragment into environment-indexed support. -/
def Supported.inProgram (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) :
    {source : Simpl.Com State Proc Fault} -> Supported source ->
      ProgramSupported checkTermination env source
  | _, .skip => .skip
  | _, .seq left right => .seq (left.inProgram checkTermination env)
      (right.inProgram checkTermination env)
  | _, .basic transform => .basic transform
  | _, .cond test thenCom elseCom => .cond test
      (thenCom.inProgram checkTermination env) (elseCom.inProgram checkTermination env)
  | _, .catch body handler => .catch (body.inProgram checkTermination env)
      (handler.inProgram checkTermination env)
  | _, .while test body => .while test (body.inProgram checkTermination env)
  | _, .throw => .throw
  | _, .guard fault test body => .guard fault test (body.inProgram checkTermination env)
  | _, .spec relation => .spec relation

end Kernel

/-- Induction in the recursion-measure shape used by generated L1 functions. -/
theorem recguard_induct {P : Nat -> Prop} (zero : P 0)
    (step : forall n, P (_root_.Zag.Lang.AutoCorres.L1.recguard_dec n) -> P n)
    (n : Nat) : P n := by
  induction n with
  | zero => exact zero
  | succ n inductionHypothesis =>
      apply step
      simpa [_root_.Zag.Lang.AutoCorres.L1.recguard_dec] using inductionHypothesis

end Zag.Lang.AutoCorres.SimplConv
