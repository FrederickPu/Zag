import Lib.Peano.Defs

/-!
  Zag-backed Simpl fragment.

  `Basic` is a typed Zag term over a declared state, open under one state variable:
  `[State] ⊢ body : State`.

  Outcomes model normal termination, abrupt exit (`Throw`), guard failure, and stuck
  evaluation. The concrete word-state ABI lives in `Lang.Simple.ABI`.
-/

namespace Lang.Simple

universe u v

/-- The Zag context used by a Simple program. -/
structure Context where
  zagCtx : Zag.Ctx
  stateTy : Zag.Ty
  types : Zag.Peano.Types zagCtx.primCtx
  iteOp : zagCtx.opCtx.get? "ite" = some Zag.Op.ite

attribute [instance] Context.types

abbrev Context.primCtx (ctx : Context) : Zag.PrimitiveCtx := ctx.zagCtx.primCtx
abbrev Context.primFuncCtx (ctx : Context) : Zag.PrimFuncCtx ctx.primCtx := ctx.zagCtx.primFuncCtx
abbrev Context.opCtx (ctx : Context) : Zag.OpCtx ctx.primCtx := ctx.zagCtx.opCtx

def stateVarCtx (ctx : Context) : Zag.VarCtx :=
  [ctx.stateTy]

abbrev Basic (ctx : Context) : Type :=
  Zag.TermOf ctx.zagCtx (stateVarCtx ctx) ctx.stateTy

abbrev BExp (ctx : Context) : Type :=
  Zag.TermOf ctx.zagCtx (stateVarCtx ctx) (.prim "Bool")

/--
  Flagged state used by the pure first-cut pipeline (M1):
  `struct [fault, abrupt, State]`.
-/
def flaggedStateTy (stateTy : Zag.Ty) : Zag.Ty :=
  .struct [.prim "Bool", .prim "Bool", stateTy]

def faultIdx : Fin 3 := ⟨0, by decide⟩
def abruptIdx : Fin 3 := ⟨1, by decide⟩
def stateIdx : Fin 3 := ⟨2, by decide⟩

/-- Liftable Simpl commands. -/
inductive Com (ctx : Context) (proc : Type u) (fault : Type v) where
  | Skip : Com ctx proc fault
  | Basic : Basic ctx → Com ctx proc fault
  | Guard : BExp ctx → Com ctx proc fault → Com ctx proc fault
  | Seq : Com ctx proc fault → Com ctx proc fault → Com ctx proc fault
  | Cond : BExp ctx → Com ctx proc fault → Com ctx proc fault → Com ctx proc fault
  | While : BExp ctx → Com ctx proc fault → Com ctx proc fault
  | Call : proc → Com ctx proc fault
  | Throw : Com ctx proc fault
  | Catch : Com ctx proc fault → Com ctx proc fault → Com ctx proc fault

/-- Procedure environment: maps procedure names to bodies. -/
abbrev ProcEnv (ctx : Context) (proc : Type u) (fault : Type v) :=
  proc → Option (Com ctx proc fault)

namespace Com

variable {ctx : Context} {proc : Type u} {fault : Type v}

def bseq : Com ctx proc fault → Com ctx proc fault → Com ctx proc fault :=
  .Seq

end Com

/-- Big-step outcomes. First cut uses unit-like fault via a carried state snapshot. -/
inductive Outcome (ctx : Context) (fault : Type v) where
  | normal (s : Zag.Val ctx.primCtx)
  | abrupt (s : Zag.Val ctx.primCtx)
  | fault (f : fault) (s : Zag.Val ctx.primCtx)
  | stuck

namespace Outcome

variable {ctx : Context} {fault : Type v}

def state? : Outcome ctx fault → Option (Zag.Val ctx.primCtx)
  | .normal s => some s
  | .abrupt s => some s
  | .fault _ s => some s
  | .stuck => none

def isNormal : Outcome ctx fault → Bool
  | .normal _ => true
  | _ => false

end Outcome

def evalBasic? {ctx : Context}
    (state : Zag.Val ctx.primCtx)
    (update : Basic ctx) : Option (Zag.Val ctx.primCtx) :=
  Zag.Term.eval ctx.zagCtx [state] update.val

def evalBExp? {ctx : Context}
    (state : Zag.Val ctx.primCtx)
    (condition : BExp ctx) : Option Bool := do
  let value ← Zag.Term.eval ctx.zagCtx [state] condition.val
  value.asBool?

/--
  Outcome-indexed big-step relation.
  Abrupt propagates through `Seq`; `Catch` intercepts it; `Guard` produces `fault`
  when the condition is false; `Basic` produces `stuck` when evaluation fails.
  `Call` is unsupported until a procedure environment is supplied (see `BigStep.call`).
-/
inductive BigStep {ctx : Context} {proc : Type u} {fault : Type v}
    (Γ : ProcEnv ctx proc fault)
    (unitFault : fault) :
    Com ctx proc fault → Outcome ctx fault → Outcome ctx fault → Prop where
  | skip (o : Outcome ctx fault) :
      BigStep Γ unitFault .Skip o o
  | basic {update : Basic ctx} {s s' : Zag.Val ctx.primCtx} :
      evalBasic? s update = some s' →
      BigStep Γ unitFault (.Basic update) (.normal s) (.normal s')
  | basicStuck {update : Basic ctx} {s : Zag.Val ctx.primCtx} :
      evalBasic? s update = none →
      BigStep Γ unitFault (.Basic update) (.normal s) .stuck
  | guardTrue {b : BExp ctx} {c : Com ctx proc fault}
      {s : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c (.normal s) o →
      BigStep Γ unitFault (.Guard b c) (.normal s) o
  | guardFalse {b : BExp ctx} {c : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = some false →
      BigStep Γ unitFault (.Guard b c) (.normal s) (.fault unitFault s)
  | guardStuck {b : BExp ctx} {c : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = none →
      BigStep Γ unitFault (.Guard b c) (.normal s) .stuck
  | seqNormal {c1 c2 : Com ctx proc fault}
      {s mid : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      BigStep Γ unitFault c1 (.normal s) (.normal mid) →
      BigStep Γ unitFault c2 (.normal mid) o →
      BigStep Γ unitFault (.Seq c1 c2) (.normal s) o
  | seqAbrupt {c1 c2 : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} :
      BigStep Γ unitFault c1 (.normal s) (.abrupt s') →
      BigStep Γ unitFault (.Seq c1 c2) (.normal s) (.abrupt s')
  | seqFault {c1 c2 : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} {f : fault} :
      BigStep Γ unitFault c1 (.normal s) (.fault f s') →
      BigStep Γ unitFault (.Seq c1 c2) (.normal s) (.fault f s')
  | seqStuck {c1 c2 : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      BigStep Γ unitFault c1 (.normal s) .stuck →
      BigStep Γ unitFault (.Seq c1 c2) (.normal s) .stuck
  | condTrue {b : BExp ctx} {c1 c2 : Com ctx proc fault}
      {s : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c1 (.normal s) o →
      BigStep Γ unitFault (.Cond b c1 c2) (.normal s) o
  | condFalse {b : BExp ctx} {c1 c2 : Com ctx proc fault}
      {s : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      evalBExp? s b = some false →
      BigStep Γ unitFault c2 (.normal s) o →
      BigStep Γ unitFault (.Cond b c1 c2) (.normal s) o
  | condStuck {b : BExp ctx} {c1 c2 : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = none →
      BigStep Γ unitFault (.Cond b c1 c2) (.normal s) .stuck
  | whileTrue {b : BExp ctx} {c : Com ctx proc fault}
      {s mid : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c (.normal s) (.normal mid) →
      BigStep Γ unitFault (.While b c) (.normal mid) o →
      BigStep Γ unitFault (.While b c) (.normal s) o
  | whileTrueAbrupt {b : BExp ctx} {c : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c (.normal s) (.abrupt s') →
      BigStep Γ unitFault (.While b c) (.normal s) (.abrupt s')
  | whileTrueFault {b : BExp ctx} {c : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} {f : fault} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c (.normal s) (.fault f s') →
      BigStep Γ unitFault (.While b c) (.normal s) (.fault f s')
  | whileTrueStuck {b : BExp ctx} {c : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = some true →
      BigStep Γ unitFault c (.normal s) .stuck →
      BigStep Γ unitFault (.While b c) (.normal s) .stuck
  | whileFalse {b : BExp ctx} {c : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = some false →
      BigStep Γ unitFault (.While b c) (.normal s) (.normal s)
  | whileStuck {b : BExp ctx} {c : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      evalBExp? s b = none →
      BigStep Γ unitFault (.While b c) (.normal s) .stuck
  | throw {s : Zag.Val ctx.primCtx} :
      BigStep Γ unitFault .Throw (.normal s) (.abrupt s)
  | catchNormal {c1 c2 : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} :
      BigStep Γ unitFault c1 (.normal s) (.normal s') →
      BigStep Γ unitFault (.Catch c1 c2) (.normal s) (.normal s')
  | catchAbrupt {c1 c2 : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      BigStep Γ unitFault c1 (.normal s) (.abrupt s') →
      BigStep Γ unitFault c2 (.normal s') o →
      BigStep Γ unitFault (.Catch c1 c2) (.normal s) o
  | catchFault {c1 c2 : Com ctx proc fault}
      {s s' : Zag.Val ctx.primCtx} {f : fault} :
      BigStep Γ unitFault c1 (.normal s) (.fault f s') →
      BigStep Γ unitFault (.Catch c1 c2) (.normal s) (.fault f s')
  | catchStuck {c1 c2 : Com ctx proc fault} {s : Zag.Val ctx.primCtx} :
      BigStep Γ unitFault c1 (.normal s) .stuck →
      BigStep Γ unitFault (.Catch c1 c2) (.normal s) .stuck
  | call {p : proc} {body : Com ctx proc fault}
      {s : Zag.Val ctx.primCtx} {o : Outcome ctx fault} :
      Γ p = some body →
      BigStep Γ unitFault body (.normal s) o →
      BigStep Γ unitFault (.Call p) (.normal s) o
  | callMissing {p : proc} {s : Zag.Val ctx.primCtx} :
      Γ p = none →
      BigStep Γ unitFault (.Call p) (.normal s) .stuck
  | fromNonNormal {c : Com ctx proc fault} {o : Outcome ctx fault}
      (h : ¬ o.isNormal) :
      BigStep Γ unitFault c o o

end Lang.Simple
