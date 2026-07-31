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

/-- Reified L1 output. Predicate fields are retained as syntax, not inspected. -/
inductive Target (State : Type u) where
  | skip
  | seq (left right : Target State)
  | modify (transform : State -> State)
  | condition (test : State -> Prop) (thenProgram elseProgram : Target State)
  | «catch» (body handler : Target State)
  | «while» (test : State -> Prop) (body : Target State)
  | throw
  | spec (relation : Simpl.StateRel State)
  | guard (test : State -> Prop)

namespace Target

/-- Interpret reified output as L1 semantics. Semantic predicate branching lives here. -/
noncomputable def denote : Target State -> L1.L1Program State
  | .skip => L1.skip
  | .seq left right => L1.seq left.denote right.denote
  | .modify transform => L1.modify transform
  | .condition test thenProgram elseProgram =>
      L1.condition test thenProgram.denote elseProgram.denote
  | .catch body handler => L1.catch body.denote handler.denote
  | .while test body => L1.while test body.denote
  | .throw => L1.throw
  | .spec relation => L1.spec relation
  | .guard test => L1.guard test

end Target

/-- A generated reified target together with exact correspondence to its source. -/
structure Certificate (checkTermination : Bool)
    (env : Simpl.Body State Proc Fault) (source : Simpl.Com State Proc Fault) where
  target : Target State
  corres : L1.L1Corres checkTermination env target.denote source

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
