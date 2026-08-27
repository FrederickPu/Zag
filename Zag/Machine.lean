import Zag.EvalAttr
import Zag.Theory

/-!
# The abstract machine

A configuration is `⟨control, env, stack⟩`. `control` is what is happening *now*; the stack is the
pending work, innermost first. `Machine.step` dispatches on the control and, when a value is handed
back, on the **top frame only** -- never deeper.

This file is the execution behaviour and nothing else. The logical relations built on it are in
`Zag/EvalTriple.lean`, and the loop rule is in `Zag/Loop.lean`.
-/

namespace Zag

/- Tagged here, not at the definitions: `Zag/Data.lean` is import-free on purpose. -/
attribute [eval_step]
  Scope.get? OpCtx.get? BlockCtx.get? BlockCtx.Raw.get? Op.ofVals Op.Body.eager Block.entryEnv
  Op.Arg.ofTerms Op.Arg.ofVals



/-- What the machine is doing right now. -/
inductive Action (primCtx : PrimitiveCtx) where
/-- No rule applies. Kept as an explicit malformed-machine state. -/
| stuck
| eval (term : Term primCtx)
| ret (value : Val primCtx)
/-- Apply `fn` to arguments that are already values. An operator asks for this, and applying an
  `opRef` may restart an operator. Stepping through the action breaks that recursive knot. -/
| apply (fn : Val primCtx) (args : List (Val primCtx))
| exit (blockName : String) (value : Val primCtx)

/-- Where a collected list of values is going, once `Frame.args` has gathered it. -/
inductive Sink (primCtx : PrimitiveCtx) where
/-- the collected list is `fn :: args`; hand it to `applyValue` -/
| apply
/-- the collected list is one value; unwind to `blockName` with it -/
| exitTo (blockName : String)

/-- One piece of pending work. Each frame carries the environment to resume under. -/
inductive Frame (primCtx : PrimitiveCtx) where
/-- collecting left to right: `done` in hand, `rest` still terms, then the list goes to `sink` -/
| args (sink : Sink primCtx) (done : List (Val primCtx)) (rest : List (Term primCtx))
    (env : Env primCtx)
/-- driving an operator. Not an `args` frame: an operator chooses *whether* to evaluate each
  operand, so it is a coroutine, not a collector -/
| opBody (resume : Option (Val primCtx) → Op.Body primCtx) (rest : List (Op.Arg primCtx))
    (env : Env primCtx)
/-- running a block body: bind the incoming value to `name`, then carry on -/
| instrs (name : String) (rest : List (Instr primCtx)) (result : Term primCtx)
    (env : Env primCtx)
/-- the frame an unwind can target: an `exit` naming `blockName` stops here -/
| call (blockName : String) (env : Env primCtx)

namespace Frame

/-- A stack suffix made only of operator frames. Such a suffix cannot catch an `exit`; it can
  only be consumed after the computation above it has returned a value. -/
inductive OpBodies {primCtx : PrimitiveCtx} : List (Frame primCtx) → Prop where
| nil : OpBodies []
| cons {resume : Option (Val primCtx) → Op.Body primCtx} {rest : List (Op.Arg primCtx)}
    {env : Env primCtx} {frames : List (Frame primCtx)} :
    OpBodies frames → OpBodies (.opBody resume rest env :: frames)

end Frame

namespace Machine

/-- What it is doing, the scope, and the work still pending. -/
structure Config (primCtx : PrimitiveCtx) where
  control : Action primCtx
  env : Env primCtx
  stack : List (Frame primCtx)

variable {primCtx : PrimitiveCtx}

/-- Start evaluating `term` in `env` with nothing pending. -/
def start (env : Env primCtx) (term : Term primCtx) : Config primCtx :=
  { control := .eval term, env := env, stack := [] }

/-- Add frames under the work already represented by `state`. -/
def appendStack (state : Config primCtx) (base : List (Frame primCtx)) : Config primCtx :=
  { state with stack := state.stack ++ base }

/-- Evaluation has finished when it is handing a value back and nothing is waiting for it. -/
def result? (state : Config primCtx) : Option (Val primCtx) :=
  match state.control, state.stack with
  | .ret value, [] => some value
  | _, _ => none

/-- Feed terms or already-produced values to an operator until it suspends, finishes, or fails. -/
@[eval_step] def driveOp (body : Op.Body primCtx) (rest : List (Op.Arg primCtx)) (env : Env primCtx)
    (stack : List (Frame primCtx)) : Option (Config primCtx) :=
  match body, rest with
  | .fail, _ => none
  | .done value, _ => some { control := .ret value, env := env, stack := stack }
  | .next _ _, [] => none
  | .next true resume, .inl operand :: rest =>
      some { control := .eval operand, env := env, stack := .opBody resume rest env :: stack }
  | .next true resume, .inr value :: rest => driveOp (resume (some value)) rest env stack
  | .next false resume, _ :: rest => driveOp (resume none) rest env stack
  | .apply fn args resume, _ =>
      let k := fun
        | some value => resume value
        | none => .fail
      some ⟨Action.apply fn args, env, .opBody k rest env :: stack⟩
termination_by rest

/-- An eager operator requests evaluation of its next surface-term argument. -/
theorem driveOp_next_term (resume : Option (Val primCtx) → Op.Body primCtx)
    (operand : Term primCtx) (rest : List (Op.Arg primCtx)) (env : Env primCtx)
    (stack : List (Frame primCtx)) :
    driveOp (.next true resume) (.inl operand :: rest) env stack =
      some ⟨.eval operand, env, .opBody resume rest env :: stack⟩ := by
  simp [driveOp]

/-- Begin a block body: the instructions in order, then the returned term. -/
@[eval_step] def enterInstrs (instrs : List (Instr primCtx)) (result : Term primCtx) (env : Env primCtx)
    (stack : List (Frame primCtx)) : Config primCtx :=
  match instrs with
  | [] => { control := .eval result, env := env, stack := stack }
  | instr :: rest =>
      { control := .eval instr.value, env := env,
        stack := .instrs instr.name rest result env :: stack }

/-- Enter `block` with the given arguments, pushing the frame an `exit` can target. -/
@[eval_step] def enterBlock (blockName : String) (block : Block primCtx) (vargs : List (Val primCtx))
    (callerEnv : Env primCtx) (stack : List (Frame primCtx)) : Option (Config primCtx) :=
  if vargs.length = block.params.length then
    some (enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call blockName callerEnv :: stack))
  else none


/-- Calculate an application transition that cannot invoke an ambient action. A primitive function
  value is applied purely, a block reference is
  entered, and an operator continuation restarts its operator on the values it captured with
  the arguments it was applied to. The single calling convention. -/
@[eval_step] def applyValueImmediate (ctx : Ctx) (fn : Val ctx.primCtx) (vargs : List (Val ctx.primCtx))
    (env : Env ctx.primCtx) (stack : List (Frame ctx.primCtx)) : Option (Config ctx.primCtx) :=
  match fn with
  | .blockRef name _ _ =>
      match ctx.blockCtx.get? name with
      | none => none
      | some block => enterBlock name block vargs env stack
  | .opRef name captured _ _ =>
      match ctx.opCtx.get? name with
      | none => none
      | some oper =>
          match oper.body name (captured.length + vargs.length) with
          | none => none
          | some body => driveOp body (Op.Arg.ofVals (captured ++ vargs)) env stack
  | .mk fnTy fnVal =>
      match Term.evalApp (Val.mk fnTy fnVal) vargs with
      | none => none
      | some value => some { control := .ret value, env := env, stack := stack }



/-- Calculate term dispatch that cannot invoke an ambient action. Never inspects the pending stack
  -- only pushes onto it. -/
@[eval_step] def evalTermImmediate (ctx : Ctx) (term : Term ctx.primCtx) (env : Env ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Option (Config ctx.primCtx) :=
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
      | some oper =>
          match oper.body name args.length with
          | some body => driveOp body (Op.Arg.ofTerms args) env stack
          | none => none
  | .call name args =>
      match ctx.blockCtx.get? name with
      | none => none
      | some block =>
          match args with
          | [] =>
              some ⟨Action.apply
                (.blockRef name (block.params.map Prod.snd) block.outTy) [], env, stack⟩
          | arg :: rest =>
              some { control := .eval arg, env := env,
                     stack := .args .apply
                       [.blockRef name (block.params.map Prod.snd) block.outTy] rest env :: stack }
  | .app fn args =>
      some { control := .eval fn, env := env, stack := .args .apply [] args env :: stack }

/-- The current action is finished and produced `value`; `frame` becomes the current action,
  resumed with it. Never inspects a term -- there is none left. -/
@[eval_step] def resumeFrame (ctx : Ctx) (frame : Frame ctx.primCtx) (value : Val ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Option (Config ctx.primCtx) :=
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
              | fn :: vargs =>
                  some ⟨Action.apply fn vargs, env, stack⟩
              | [] => none
          | .exitTo blockName =>
              match done ++ [value] with
              | [v] => some { control := .exit blockName v, env := env, stack := stack }
              | _ => none
  | .instrs name rest result env =>
      some (enterInstrs rest result (env ++ [(name, value)]) stack)
  | .call _ callerEnv => some { control := .ret value, env := callerEnv, stack := stack }

/-- Unwinding: discard one frame. Only a `call` frame naming the target stops it. -/
@[eval_step] def unwindFrame (frame : Frame primCtx) (blockName : String) (value : Val primCtx)
    (env : Env primCtx) (stack : List (Frame primCtx)) : Option (Config primCtx) :=
  match frame with
  | .call target callerEnv =>
      if blockName = target then
        some { control := .ret value, env := callerEnv, stack := stack }
      else
        some { control := .exit blockName value, env := callerEnv, stack := stack }
  | _ => some { control := .exit blockName value, env := env, stack := stack }

/-! ### Effect sequencing

The `Immediate` helpers calculate transitions that cannot invoke ambient actions. The canonical
helpers inject those transitions into `Machine.Effect` and execute `Op.action` after its operands
have been evaluated, so every machine continuation is sequenced by the monad. -/

/-- Inject a pure partial transition into the evaluation monad. -/
def ofOption (ctx : Ctx) (next : Option α) : Effect ctx α :=
  OptionT.mk (pure next)

/-- Run an operator's ordinary body. Effectful operators use such a body to evaluate operands and
eventually apply an operator reference, where `applyValue` runs the ambient action. -/
def driveSelectedOp (ctx : Ctx) (oper : Op ctx.primCtx ctx.M) (name : String) (arity : Nat)
    (rest : List (Op.Arg ctx.primCtx)) (env : Env ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Effect ctx (Config ctx.primCtx) :=
  match oper.body name arity with
  | some body => ofOption ctx (driveOp body rest env stack)
  | none => OptionT.fail

/-- Canonical value application. Operator references may invoke ambient actions; all other
transitions come from `applyValueImmediate` and are injected into `Machine.Effect`. -/
def applyValue (ctx : Ctx) (fn : Val ctx.primCtx) (vargs : List (Val ctx.primCtx))
    (env : Env ctx.primCtx) (stack : List (Frame ctx.primCtx)) :
    Effect ctx (Config ctx.primCtx) :=
  match fn with
  | .opRef name captured _ _ =>
      match ctx.opCtx.get? name with
      | none => OptionT.fail
      | some oper =>
          let values := captured ++ vargs
          match oper.action name values with
          | some action => do
              let value? ← monadLift action
              match value? with
              | some value => pure ⟨.ret value, env, stack⟩
              | none => OptionT.fail
          | none =>
              driveSelectedOp ctx oper name values.length (Op.Arg.ofVals values) env stack
  | _ => ofOption ctx (applyValueImmediate ctx fn vargs env stack)

/-- Canonical term dispatch. Operator operands are driven by their ordinary body; ambient actions
run only when that body applies its operator reference. Other transitions come from
`evalTermImmediate` and are injected into `Machine.Effect`. -/
def evalTerm (ctx : Ctx) (term : Term ctx.primCtx) (env : Env ctx.primCtx)
    (stack : List (Frame ctx.primCtx)) : Effect ctx (Config ctx.primCtx) :=
  match term with
  | .op name args =>
      match ctx.opCtx.get? name with
      | none => OptionT.fail
      | some oper =>
          driveSelectedOp ctx oper name args.length (Op.Arg.ofTerms args) env stack
  | _ => ofOption ctx (evalTermImmediate ctx term env stack)

/-- One machine step. Immediate transitions are injected into `Machine.Effect`; an ambient action
uses `monadLift`, and the surrounding `OptionT` records a stuck transition. -/
def step (ctx : Ctx) : Config ctx.primCtx → Effect ctx (Config ctx.primCtx)
| { control := .stuck, .. } => OptionT.fail
| { control := .eval term, env, stack } => evalTerm ctx term env stack
| { control := .apply fn args, env, stack } => applyValue ctx fn args env stack
| { control := .ret _, stack := [], .. } => OptionT.fail
| { control := .ret value, stack := frame :: stack, .. } =>
    ofOption ctx (resumeFrame ctx frame value stack)
| { control := .exit _ _, stack := [], .. } => OptionT.fail
| { control := .exit blockName value, env, stack := frame :: stack } =>
    ofOption ctx (unwindFrame frame blockName value env stack)

/-- Execute exactly `fuel` machine transitions. This bounded API is executable and intended for
testing and proof construction, not as the public logical denotation. -/
def nsteps (ctx : Ctx) : Nat → Config ctx.primCtx → Effect ctx (Config ctx.primCtx)
| 0, state => pure state
| fuel + 1, state => step ctx state >>= nsteps ctx fuel

/-- Split an effectful bounded run at an intermediate machine state. -/
theorem nsteps_add (ctx : Ctx) (fuel₀ fuel₁ : Nat) (state : Config ctx.primCtx) :
    nsteps ctx (fuel₀ + fuel₁) state = nsteps ctx fuel₀ state >>= nsteps ctx fuel₁ := by
  induction fuel₀ generalizing state with
  | zero => simp [nsteps]
  | succ fuel₀ ih =>
      have ih' : nsteps ctx (fuel₀ + fuel₁) = fun state =>
          nsteps ctx fuel₀ state >>= nsteps ctx fuel₁ := funext ih
      rw [show fuel₀ + 1 + fuel₁ = (fuel₀ + fuel₁) + 1 by omega, nsteps, ih']
      simp [nsteps, bind_assoc]

/-- Run until a value is returned or the supplied executable bound is exhausted. Every
instruction, call, application, and operator continuation is crossed through `OptionT.bind`. -/
def evalConfigFuel (ctx : Ctx) : Nat → Config ctx.primCtx → Effect ctx (Val ctx.primCtx)
| fuel, state =>
    match result? state with
    | some value => pure value
    | none =>
        match fuel with
        | 0 => OptionT.fail
        | fuel + 1 => step ctx state >>= evalConfigFuel ctx fuel

/-- Executable effectful evaluation from a surface term. Fuel remains confined to this machine
API; `Zag.eval` below remains the fuel-independent logical relation bridge. -/
def evalFuel (ctx : Ctx) (fuel : Nat) (env : Env ctx.primCtx) (term : Term ctx.primCtx) :
    Effect ctx (Val ctx.primCtx) :=
  evalConfigFuel ctx fuel (start env term)

/-! ### StateM machine view -/

/-- Build a context whose ambient effect is one state. This specialized view avoids pretending
that an arbitrary `Ctx.M` can be inspected or cast to `StateM`. -/
abbrev stateCtx (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx := .empty) : Ctx where
  primCtx := primCtx
  M := StateM σ
  monad := StateT.instMonad
  opCtx := opCtx
  blockCtx := blockCtx
  postShape := .arg σ .pure
  wpMonad := inferInstance

private theorem stateT_run_apply (x : StateM σ α) (state : σ) :
    Id.run (StateT.run x state) = Id.run (x state) := by
  unfold StateT.run
  rfl

theorem stateM_pure_run (value : α) (state : σ) :
    Id.run ((pure value : StateM σ α) state) = (value, state) := by
  rfl

theorem optionT_state_bind_run (x : OptionT (StateM σ) α)
    (f : α → OptionT (StateM σ) β) (state : σ) :
    Id.run ((x >>= f).run state) =
      match Id.run (x.run state) with
      | (none, nextState) => (none, nextState)
      | (some value, nextState) => Id.run ((f value).run nextState) := by
  rw [OptionT.run_bind]
  unfold Option.elimM
  change Id.run (StateT.run (x.run >>= fun value? =>
    value?.elim (pure none) fun value => (f value).run) state) = _
  rw [StateT.run_bind]
  cases hstate : Id.run (x.run state) with
  | mk value? nextState =>
      cases value? <;> simp [Id.run_bind, StateT.run, stateM_pure_run, hstate]

/-- Expose exactly one unfinished StateM machine transition without unfolding the remaining run. -/
theorem evalConfigFuel_run_succ_of_none (primCtx : PrimitiveCtx)
    (opCtx : OpCtx primCtx (StateM σ)) (blockCtx : BlockCtx primCtx)
    (fuel : Nat) (state : Config primCtx) (initial : σ)
    (hresult : result? state = none) :
    Id.run ((evalConfigFuel (stateCtx primCtx opCtx blockCtx) (fuel + 1) state).run initial) =
      match Id.run ((step (stateCtx primCtx opCtx blockCtx) state).run initial) with
      | (none, nextState) => (none, nextState)
      | (some next, nextState) =>
          Id.run ((evalConfigFuel (stateCtx primCtx opCtx blockCtx) fuel next).run nextState) := by
  simp only [evalConfigFuel, hresult]
  change Id.run ((step (stateCtx primCtx opCtx blockCtx) state >>=
    evalConfigFuel (stateCtx primCtx opCtx blockCtx) fuel).run initial) = _
  rw [optionT_state_bind_run]
  cases hstep : Id.run ((step (stateCtx primCtx opCtx blockCtx) state).run initial) with
  | mk value? nextState => cases value? <;> simp

/-- Rewrite one unfinished StateM run when its next transition is already known. -/
theorem evalConfigFuel_run_succ_of_step (primCtx : PrimitiveCtx)
    (opCtx : OpCtx primCtx (StateM σ)) (blockCtx : BlockCtx primCtx)
    (fuel : Nat) (state next : Config primCtx) (initial nextState : σ)
    (hresult : result? state = none)
    (hstep : Id.run ((step (stateCtx primCtx opCtx blockCtx) state).run initial) =
      (some next, nextState)) :
    Id.run ((evalConfigFuel (stateCtx primCtx opCtx blockCtx) (fuel + 1) state).run initial) =
      Id.run ((evalConfigFuel (stateCtx primCtx opCtx blockCtx) fuel next).run nextState) := by
  rw [evalConfigFuel_run_succ_of_none primCtx opCtx blockCtx fuel state initial hresult,
    hstep]

private theorem result?_eq_none_of_step_run_some (primCtx : PrimitiveCtx)
    (opCtx : OpCtx primCtx (StateM σ)) (blockCtx : BlockCtx primCtx)
    (state next : Config primCtx) (initial final : σ)
    (hstep : (step (stateCtx primCtx opCtx blockCtx) state).run initial =
      (some next, final)) : result? state = none := by
  cases state with
  | mk control env stack =>
      cases control <;> cases stack <;>
        simp [result?, step, OptionT.fail] at hstep ⊢
      have hfalse := congrArg Prod.fst hstep
      contradiction

/-- A finite effectful segment ending at an empty-stack return is a successful bounded run. -/
theorem evalConfigFuel_run_of_nsteps_result (primCtx : PrimitiveCtx)
    (opCtx : OpCtx primCtx (StateM σ)) (blockCtx : BlockCtx primCtx)
    (fuel : Nat) (state : Config primCtx) (initial final : σ)
    (value : Val primCtx) (scope : Env primCtx)
    (hsteps : (nsteps (stateCtx primCtx opCtx blockCtx) fuel state).run initial =
      (some ⟨.ret value, scope, []⟩, final)) :
    (evalConfigFuel (stateCtx primCtx opCtx blockCtx) fuel state).run initial =
      (some value, final) := by
  induction fuel generalizing state initial with
  | zero =>
      simp only [nsteps] at hsteps
      change (some state, initial) = (some ⟨.ret value, scope, []⟩, final) at hsteps
      obtain ⟨rfl, rfl⟩ := hsteps
      rfl
  | succ fuel ih =>
      simp only [nsteps] at hsteps
      change Id.run (((step (stateCtx primCtx opCtx blockCtx) state >>=
        nsteps (stateCtx primCtx opCtx blockCtx) fuel).run initial)) = _ at hsteps
      rw [optionT_state_bind_run] at hsteps
      cases hstep : (step (stateCtx primCtx opCtx blockCtx) state).run initial with
      | mk next? middle =>
          cases next? with
          | none => simp [hstep, Id.run] at hsteps
          | some next =>
              simp only [hstep, Id.run] at hsteps
              have hresult := result?_eq_none_of_step_run_some primCtx opCtx blockCtx
                state next initial middle hstep
              change Id.run ((evalConfigFuel (stateCtx primCtx opCtx blockCtx)
                (fuel + 1) state).run initial) = _
              rw [evalConfigFuel_run_succ_of_step primCtx opCtx blockCtx fuel state next
                initial middle hresult hstep]
              exact ih next middle hsteps

end Machine

end Zag
