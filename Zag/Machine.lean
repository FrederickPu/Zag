import Zag.EvalAttr
import Zag.Theory

/-!
# The abstract machine

A state is `⟨control, env, stack⟩`. `control` is what is happening *now*; the stack is the
pending work, innermost first. `step` dispatches on the control and, when a value is being handed
back, on the **top frame only** -- never deeper. That single property is what `Zag/Weakening.lean`
turns into `step_weaken`, and everything compositional rests on it.

This file is the execution behaviour and nothing else. Its metatheory is in `Zag/Weakening.lean`,
the relations built on it are in `Zag/EvalState.lean`, and the loop rule is in `Zag/Loop.lean`.
-/

namespace Zag

/- Tagged here, not at the definitions: `Zag/Data.lean` is import-free on purpose. -/
attribute [eval_step]
  Scope.get? OpCtx.get? BlockCtx.get? BlockCtx.Raw.get? Op.ofVals Op.Body.eager Block.entryEnv



/-- What the machine is doing right now. -/
inductive Action (primCtx : PrimitiveCtx) where
/-- No rule applies. Reached only by a control instruction, which has no semantics yet. -/
| stuck
| eval (term : Term primCtx)
| ret (value : Val primCtx)
| exit (blockName : String) (value : Val primCtx)

/-- Where a collected list of values is going, once `Frame.args` has gathered it. -/
inductive Sink (primCtx : PrimitiveCtx) where
/-- the collected list is `fn :: args`; hand it to `applyValue` -/
| apply
/-- the collected list is one value; unwind to `blockName` with it -/
| exitTo (blockName : String)
/-- the collected list is a control instruction's initial phi values -/
| control (control : String) (blocks : List String)

/-- One piece of pending work. Each frame carries the environment to resume under. -/
inductive Frame (primCtx : PrimitiveCtx) where
/-- collecting left to right: `done` in hand, `rest` still terms, then the list goes to `sink` -/
| args (sink : Sink primCtx) (done : List (Val primCtx)) (rest : List (Term primCtx))
    (env : Env primCtx)
/-- driving an operator. Not an `args` frame: an operator chooses *whether* to evaluate each
  operand, so it is a coroutine, not a collector -/
| opBody (resume : Option (Val primCtx) → Op.Body primCtx) (rest : List (Term primCtx))
    (env : Env primCtx)
/-- running a block body: bind the incoming value to `name`, then carry on -/
| instrs (name : String) (rest : List (Instr primCtx)) (result : Term primCtx)
    (env : Env primCtx)
/-- the frame an unwind can target: an `exit` naming `blockName` stops here -/
| call (blockName : String) (env : Env primCtx)
/-- a control mid-flight: `phase` is its own state, `args` the phi values in play. No
  continuation of its own -- an `instrs` frame sits directly beneath it -/
| control (control : String) (phase : Nat) (blocks : List String) (args : List (Val primCtx))
    (env : Env primCtx)

namespace Frame

/-- A stack suffix made only of operator frames. Such a suffix cannot catch an `exit`; it can
  only be consumed after the computation above it has returned a value. -/
inductive OpBodies {primCtx : PrimitiveCtx} : List (Frame primCtx) → Prop where
| nil : OpBodies []
| cons {resume : Option (Val primCtx) → Op.Body primCtx} {rest : List (Term primCtx)}
    {env : Env primCtx} {frames : List (Frame primCtx)} :
    OpBodies frames → OpBodies (.opBody resume rest env :: frames)

end Frame

/-- What it is doing, the scope, and the work still pending. The heap is deliberately not here:
  it belongs to the monad. -/
structure EvalState (primCtx : PrimitiveCtx) where
  control : Action primCtx
  env : Env primCtx
  stack : List (Frame primCtx)

namespace EvalState

variable {primCtx : PrimitiveCtx}

/-- Start evaluating `term` in `env` with nothing pending. -/
def start (env : Env primCtx) (term : Term primCtx) : EvalState primCtx :=
  { control := .eval term, env := env, stack := [] }

/-- Add frames under the work already represented by `state`. -/
def appendStack (state : EvalState primCtx) (base : List (Frame primCtx)) : EvalState primCtx :=
  { state with stack := state.stack ++ base }

/-- Evaluation has finished when it is handing a value back and nothing is waiting for it. -/
def result? (state : EvalState primCtx) : Option (Val primCtx) :=
  match state.control, state.stack with
  | .ret value, [] => some value
  | _, _ => none

/-- Feed operands to an operator until it wants one evaluated, finishes, or fails. -/
@[eval_step] def driveOp (body : Op.Body primCtx) (rest : List (Term primCtx)) (env : Env primCtx)
    (stack : List (Frame primCtx)) : Option (EvalState primCtx) :=
  match body, rest with
  | .fail, _ => none
  | .done value, _ => some { control := .ret value, env := env, stack := stack }
  | .next _ _, [] => none
  | .next true resume, operand :: rest =>
      some { control := .eval operand, env := env, stack := .opBody resume rest env :: stack }
  | .next false resume, _ :: rest => driveOp (resume none) rest env stack
termination_by rest

/-- Begin a block body: the instructions in order, then the returned term. -/
@[eval_step] def enterInstrs (instrs : List (Instr primCtx)) (result : Term primCtx) (env : Env primCtx)
    (stack : List (Frame primCtx)) : EvalState primCtx :=
  match instrs with
  | [] => { control := .eval result, env := env, stack := stack }
  | instr :: rest =>
      match instr.source with
      | .term value =>
          { control := .eval value, env := env,
            stack := .instrs instr.name rest result env :: stack }
      | .control control blocks (arg :: args) =>
          { control := .eval arg, env := env,
            stack := .args (.control control blocks) [] args env
                       :: .instrs instr.name rest result env :: stack }
      -- a control with no phi values has nothing to iterate over
      | .control _ _ [] => { control := .stuck, env := env, stack := stack }

/-- Enter `block` with the given arguments, pushing the frame an `exit` can target. -/
@[eval_step] def enterBlock (blockName : String) (block : Block primCtx) (vargs : List (Val primCtx))
    (callerEnv : Env primCtx) (stack : List (Frame primCtx)) : Option (EvalState primCtx) :=
  if vargs.length = block.params.length then
    some (enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call blockName callerEnv :: stack))
  else none


/-- Finish an application: a primitive function value is applied purely, a block reference is
  entered. The single calling convention. -/
@[eval_step] def applyValue (ctx : Ctx) (fn : Val ctx.primCtx) (vargs : List (Val ctx.primCtx))
    (env : Env ctx.primCtx) (stack : List (Frame ctx.primCtx)) : Option (EvalState ctx.primCtx) :=
  match fn with
  | .blockRef name _ _ =>
      match ctx.blockCtx.get? name with
      | none => none
      | some block => enterBlock name block vargs env stack
  | .mk fnTy fnVal =>
      match Term.evalApp (Val.mk fnTy fnVal) vargs with
      | none => none
      | some value => some { control := .ret value, env := env, stack := stack }

/-- Act on what a control asked for: finish, or run one of the blocks it drives with the control
  frame reinstated so the answer comes back here. -/
@[eval_step] def driveControl (ctx : Ctx) (control : String) (phase : Nat)
    (yield : Control.Yield ctx.primCtx) (blocks : List String) (env : Env ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Option (EvalState ctx.primCtx) :=
  match yield with
  -- the `instrs` frame at the head of `stack` is the continuation; just hand it the answer
  | .done value => some { control := .ret value, env := env, stack := stack }
  | .call role args =>
      match blocks[role]? with
      | none => none
      | some blockName =>
          match ctx.blockCtx.get? blockName with
          | none => none
          | some block =>
                      enterBlock blockName block args env
                (.control control phase blocks args env :: stack)



/-- Start work on a term. Never inspects the pending stack -- only pushes onto it. -/
@[eval_step] def evalStep (ctx : Ctx) (term : Term ctx.primCtx) (env : Env ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Option (EvalState ctx.primCtx) :=
  match term with
  | .prim ty value => some { control := .ret (Val.mk ty value), env := env, stack := stack }
  | .var name =>
      match Scope.get? env name with
      | some value => some { control := .ret value, env := env, stack := stack }
      -- a name not bound locally may still name a block, and a block is a value
      | none =>
          match ctx.blockCtx.get? name with
          | some block =>
              some { control := .ret (.blockRef name (block.params.map Prod.snd) block.outTy),
                     env := env, stack := stack }
          | none => none
  | .exit blockName value =>
      some { control := .eval value, env := env,
             stack := .args (.exitTo blockName) [] [] env :: stack }
  | .op name args =>
      match ctx.opCtx.get? name with
      | none => none
      | some oper => if args.length = oper.arity then driveOp oper.body args env stack else none
  | .call name args =>
      match ctx.blockCtx.get? name with
      | none => none
      | some block =>
          match args with
          | [] =>
              applyValue ctx (.blockRef name (block.params.map Prod.snd) block.outTy) [] env stack
          | arg :: rest =>
              some { control := .eval arg, env := env,
                     stack := .args .apply
                       [.blockRef name (block.params.map Prod.snd) block.outTy] rest env :: stack }
  | .app fn args =>
      some { control := .eval fn, env := env, stack := .args .apply [] args env :: stack }

/-- The current action is finished and produced `value`; `frame` becomes the current action,
  resumed with it. Never inspects a term -- there is none left. -/
@[eval_step] def resumeFrame (ctx : Ctx) (frame : Frame ctx.primCtx) (value : Val ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Option (EvalState ctx.primCtx) :=
  match frame with
  | .opBody k rest env => driveOp (k (some value)) rest env stack
  | .args sink done rest env =>
      match rest with
      | arg :: rest =>
          some { control := .eval arg, env := env,
                 stack := .args sink (done ++ [value]) rest env :: stack }
      | [] =>
          match sink with
          | .apply =>
              match done ++ [value] with
              | fn :: vargs => applyValue ctx fn vargs env stack
              | [] => none
          | .exitTo blockName =>
              match done ++ [value] with
              | [v] => some { control := .exit blockName v, env := env, stack := stack }
              | _ => none
          | .control c blocks =>
              match Scope.get? ctx.controlCtx c with
              | none => none
              | some ctrl =>
                  match ctrl.init (done ++ [value]) with
                  | none => none
                  | some (phase, yield) => driveControl ctx c phase yield blocks env stack
  | .instrs name rest result env =>
      some (enterInstrs rest result (env ++ [(name, value)]) stack)
  | .call _ callerEnv => some { control := .ret value, env := callerEnv, stack := stack }
  | .control c phase blocks args env =>
      match Scope.get? ctx.controlCtx c with
      | none => none
      | some ctrl =>
          match ctrl.next phase args value with
          | none => none
          | some (phase', yield) => driveControl ctx c phase' yield blocks env stack

/-- Unwinding: discard one frame. Only a `call` frame naming the target stops it. -/
@[eval_step] def unwindFrame (frame : Frame primCtx) (blockName : String) (value : Val primCtx)
    (env : Env primCtx) (stack : List (Frame primCtx)) : Option (EvalState primCtx) :=
  match frame with
  | .call target callerEnv =>
      if blockName = target then
        some { control := .ret value, env := callerEnv, stack := stack }
      else
        some { control := .exit blockName value, env := callerEnv, stack := stack }
  | _ => some { control := .exit blockName value, env := env, stack := stack }

/-- One step, in three modes: start a term, resume the top frame with a value, or unwind past it.

  Only the `ret` and `exit` modes look at the stack, and only at its head. A value with an empty
  stack is a finished state -- see `EvalState.result?`. -/
@[eval_step] def step (ctx : Ctx) : EvalState ctx.primCtx → Option (EvalState ctx.primCtx)
| { control := .stuck, .. } => none
| { control := .eval term, env, stack } => evalStep ctx term env stack
| { control := .ret _, stack := [], .. } => none
| { control := .ret value, stack := frame :: stack, .. } => resumeFrame ctx frame value stack
| { control := .exit _ _, stack := [], .. } => none
| { control := .exit blockName value, env, stack := frame :: stack } =>
    unwindFrame frame blockName value env stack

/-- Run at most `fuel` steps, stopping early if evaluation gets stuck or finishes. Total, and
  structurally recursive on `fuel` -- which is what lets the effect type be any monad once
  `applyOperator` becomes `M`-valued. -/
def run (ctx : Ctx) : Nat → EvalState ctx.primCtx → EvalState ctx.primCtx
| 0, state => state
| fuel + 1, state =>
    match step ctx state with
    | none => state
    | some next => run ctx fuel next


/-- Exactly `fuel` steps, failing if any of them is stuck. Unlike `run`, which stops early and
  returns the last state, this is `none` the moment a step does not apply -- which is what makes
  it compose: `stepN_add` splits a run at any point. -/
def stepN (ctx : Ctx) : Nat → EvalState ctx.primCtx → Option (EvalState ctx.primCtx)
| 0, state => some state
| fuel + 1, state => (step ctx state).bind (stepN ctx fuel)

@[simp] theorem stepN_zero (state : EvalState ctx.primCtx) : stepN ctx 0 state = some state := rfl

theorem stepN_succ (fuel : Nat) (state : EvalState ctx.primCtx) :
    stepN ctx (fuel + 1) state = (step ctx state).bind (stepN ctx fuel) := rfl


end EvalState

end Zag
