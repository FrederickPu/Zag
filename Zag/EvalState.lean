import Zag.Theory

/-!
# Small-step evaluation for the block IR

`Term.evalOutcome` and friends are big-step: five mutually recursive functions defined by
`partial_fixpoint`, which is what forces the result type to carry a `⊥` and is why the effect
type cannot be an arbitrary monad. This file writes the same semantics as a step relation over an explicit evaluation state instead.
Each of those five definitions is one kind of pending work, so each becomes one frame:

| big-step definition | frame |
| --- | --- |
| `Term.evalBodyOutcome` -- drive an `Op.Body` over operands | `Frame.opBody` |
| `Term.evalListOutcome` -- evaluate an argument list | `Frame.callArgs` / `Frame.appArgs` |
| `Term.evalInstrs` -- run instructions, extending the scope | `Frame.instrs` |
| `Term.evalBlock` -- catch an exit aimed at this block | `Frame.call` |
| `Term.evalOutcome` -- the driver | `Control` |

`EvalState.step` is *structural*: no fixpoint, no `CCPO`, nothing to prove monotone. Non-termination is not
a value here -- it is the absence of a fuel bound, which is a proposition about `EvalState.run`.

`Outcome` does not appear. What it was reifying -- "this evaluation is unwinding to a named
frame" -- is `Control.exit`, and the frame it unwinds to is `Frame.call`.

Evaluation is pure for now, matching the current operator semantics exactly so that it can be
checked against `Term.eval`. Effects thread in at one place, `applyOperator`, whose result would
become `M (Option (Val primCtx))`; `run`'s recursion is structural on fuel, so an arbitrary
`Monad M` needs nothing further.
-/

namespace Zag

/-- What evaluation is currently doing: about to evaluate a term, handing a value back to the stack, or
  unwinding towards the call frame named by an `exit`. -/
inductive Control (primCtx : PrimitiveCtx) where
| eval (term : Term primCtx)
| ret (value : Val primCtx)
| exit (blockName : String) (value : Val primCtx)

/-- One piece of pending work. Every frame carries the environment to resume under, because a
  call and an instruction both change the scope. -/
inductive Frame (primCtx : PrimitiveCtx) where
/-- evaluating the payload of `exit blockName _` -/
| exitValue (blockName : String) (env : Env primCtx)
/-- driving an operator: `resume` is waiting for the operand being evaluated, `rest` are the
  operands it has not reached yet -/
| opBody (resume : Option (Val primCtx) → Op.Body primCtx) (rest : List (Term primCtx))
    (env : Env primCtx)
/-- collecting the arguments of `call blockName` -/
| callArgs (blockName : String) (block : Block primCtx) (done : List (Val primCtx))
    (rest : List (Term primCtx)) (env : Env primCtx)
/-- evaluating the function of an application -/
| appFn (args : List (Term primCtx)) (env : Env primCtx)
/-- collecting the arguments of an application whose function has already evaluated to `fn` -/
| appArgs (fn : Val primCtx) (done : List (Val primCtx)) (rest : List (Term primCtx))
    (env : Env primCtx)
/-- running a block body: bind the incoming value to `name`, then carry on -/
| instrs (name : String) (rest : List (Instr primCtx)) (result : Term primCtx)
    (env : Env primCtx)
/-- the frame an unwind can target: an `exit` naming `blockName` stops here -/
| call (blockName : String) (env : Env primCtx)

/-- The whole state of a running program: what it is doing, the scope it is doing it in, and
  the work still pending. The heap is deliberately *not* here -- it belongs to the monad. -/
structure EvalState (primCtx : PrimitiveCtx) where
  control : Control primCtx
  env : Env primCtx
  stack : List (Frame primCtx)

namespace EvalState

variable {primCtx : PrimitiveCtx}

/-- Start evaluating `term` in `env` with nothing pending. -/
def start (env : Env primCtx) (term : Term primCtx) : EvalState primCtx :=
  { control := .eval term, env := env, stack := [] }

/-- Evaluation has finished when it is handing a value back and nothing is waiting for it. -/
def result? (state : EvalState primCtx) : Option (Val primCtx) :=
  match state.control, state.stack with
  | .ret value, [] => some value
  | _, _ => none

/-- Feed operands to an operator body until it wants one evaluated, finishes, or fails.
  This is `Term.evalBodyOutcome`'s loop, with the evaluation of an operand suspended as a
  frame rather than performed by a recursive call. -/
def driveOp (body : Op.Body primCtx) (rest : List (Term primCtx)) (env : Env primCtx)
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
def enterInstrs (instrs : List (Instr primCtx)) (result : Term primCtx) (env : Env primCtx)
    (stack : List (Frame primCtx)) : EvalState primCtx :=
  match instrs with
  | [] => { control := .eval result, env := env, stack := stack }
  | instr :: rest =>
      { control := .eval instr.value, env := env,
        stack := .instrs instr.name rest result env :: stack }

/-- Enter `block` with the given arguments, pushing the frame an `exit` can target. -/
def enterBlock (blockName : String) (block : Block primCtx) (vargs : List (Val primCtx))
    (callerEnv : Env primCtx) (stack : List (Frame primCtx)) : Option (EvalState primCtx) :=
  if vargs.length = block.params.length then
    some (enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call blockName callerEnv :: stack))
  else none

/-! ### weakening

  The stack is the ambient context of a computation, and these say what weakening always says:
  enlarging the context leaves the derivation alone. Concretely, work pending *beneath* a
  computation is never read, so the computation behaves identically and leaves that work intact.

  This is what makes a subterm compose: when an operand is evaluated, the frames belonging to
  the enclosing operator are the `base` being weakened in. It is also what an induction over a
  recursive block needs -- the hypothesis speaks about a run from an empty stack, but gets used
  part-way through a run, where the caller's frames are still pending. -/

theorem driveOp_weaken {body : Op.Body primCtx} {rest : List (Term primCtx)}
    {env : Env primCtx} {S : List (Frame primCtx)} {c' : Control primCtx} {e' : Env primCtx}
    {S' : List (Frame primCtx)} (base : List (Frame primCtx))
    (h : driveOp body rest env S = some ⟨c', e', S'⟩) :
    driveOp body rest env (S ++ base) = some ⟨c', e', S' ++ base⟩ := by
  induction rest generalizing body with
  | nil => cases body <;> simp [driveOp] at h ⊢ <;> simp [← h.1, ← h.2.1, ← h.2.2]
  | cons operand rest ih =>
      cases body with
      | fail => simp [driveOp] at h
      | done value => simp [driveOp] at h ⊢; simp [← h.1, ← h.2.1, ← h.2.2]
      | next evaluate resume =>
          cases evaluate with
          | true => simp [driveOp] at h ⊢; simp [← h.1, ← h.2.1, ← h.2.2]
          | false => rw [driveOp] at h ⊢; exact ih h

/-- Where entering a block body lands does not depend on what was already on the stack. -/
theorem enterInstrs_stack (instrs : List (Instr primCtx)) (result : Term primCtx)
    (env : Env primCtx) :
    ∃ delta c e, ∀ S : List (Frame primCtx),
      enterInstrs instrs result env S = ⟨c, e, delta ++ S⟩ := by
  cases instrs with
  | nil => exact ⟨[], .eval result, env, fun _ => rfl⟩
  | cons instr rest =>
      exact ⟨[.instrs instr.name rest result env], .eval instr.value, env, fun _ => rfl⟩

theorem enterBlock_weaken {name : String} {block : Block primCtx}
    {vargs : List (Val primCtx)} {env : Env primCtx} {S : List (Frame primCtx)}
    {c' : Control primCtx} {e' : Env primCtx} {S' : List (Frame primCtx)}
    (base : List (Frame primCtx))
    (h : enterBlock name block vargs env S = some ⟨c', e', S'⟩) :
    enterBlock name block vargs env (S ++ base) = some ⟨c', e', S' ++ base⟩ := by
  obtain ⟨delta, c, e, hI⟩ := enterInstrs_stack block.instrs block.result (block.entryEnv vargs)
  unfold enterBlock at h ⊢
  split at h
  case isTrue hlen =>
      rw [hI] at h
      rw [if_pos hlen, hI]
      obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
      simp
  case isFalse => simp at h

/-- One step. Structural: it looks at the control and the top frame and produces the next state,
  or `none` if evaluation is stuck. A finished state is stuck too -- see `EvalState.result?`. -/
def step (ctx : Ctx) : EvalState ctx.primCtx → Option (EvalState ctx.primCtx)
-- evaluating
| { control := .eval (.prim ty value), env, stack } =>
    some { control := .ret (Val.mk ty value), env := env, stack := stack }
| { control := .eval (.var name), env, stack } =>
    match Scope.get? env name with
    | some value => some { control := .ret value, env := env, stack := stack }
    | none => none
| { control := .eval (.exit blockName value), env, stack } =>
    some { control := .eval value, env := env, stack := .exitValue blockName env :: stack }
| { control := .eval (.op name args), env, stack } => do
    let oper ← ctx.opCtx.get? name
    if args.length = oper.arity then driveOp oper.body args env stack else none
| { control := .eval (.call name args), env, stack } => do
    let block ← ctx.blockCtx.get? name
    match args with
    | [] => enterBlock name block [] env stack
    | arg :: rest =>
        some { control := .eval arg, env := env,
               stack := .callArgs name block [] rest env :: stack }
| { control := .eval (.app fn args), env, stack } =>
    some { control := .eval fn, env := env, stack := .appFn args env :: stack }
-- handing a value back
| { control := .ret _, stack := [], .. } => none
| { control := .ret value, stack := .exitValue blockName env :: stack, .. } =>
    some { control := .exit blockName value, env := env, stack := stack }
| { control := .ret value, stack := .opBody resume rest env :: stack, .. } =>
    driveOp (resume (some value)) rest env stack
| { control := .ret value, stack := .callArgs name block done rest env :: stack, .. } =>
    match rest with
    | [] => enterBlock name block (done ++ [value]) env stack
    | arg :: rest =>
        some { control := .eval arg, env := env,
               stack := .callArgs name block (done ++ [value]) rest env :: stack }
| { control := .ret fn, stack := .appFn args env :: stack, .. } =>
    match args with
    | [] => (Term.evalApp fn []).map fun value =>
        { control := .ret value, env := env, stack := stack }
    | arg :: rest =>
        some { control := .eval arg, env := env,
               stack := .appArgs fn [] rest env :: stack }
| { control := .ret value, stack := .appArgs fn done rest env :: stack, .. } =>
    match rest with
    | [] => (Term.evalApp fn (done ++ [value])).map fun result =>
        { control := .ret result, env := env, stack := stack }
    | arg :: rest =>
        some { control := .eval arg, env := env,
               stack := .appArgs fn (done ++ [value]) rest env :: stack }
| { control := .ret value, stack := .instrs name rest result env :: stack, .. } =>
    some (enterInstrs rest result (env ++ [(name, value)]) stack)
| { control := .ret value, stack := .call _ callerEnv :: stack, .. } =>
    some { control := .ret value, env := callerEnv, stack := stack }
-- unwinding: every frame is discarded until the named call frame is found
| { control := .exit _ _, stack := [], .. } => none
| { control := .exit blockName value, stack := .call target callerEnv :: stack, .. } =>
    if blockName = target then
      some { control := .ret value, env := callerEnv, stack := stack }
    else
      some { control := .exit blockName value, env := callerEnv, stack := stack }
| { control := .exit blockName value, stack := _ :: stack, env } =>
    some { control := .exit blockName value, env := env, stack := stack }

/-- Run at most `fuel` steps, stopping early if evaluation gets stuck or finishes. Total, and
  structurally recursive on `fuel` -- which is what lets the effect type be any monad once
  `applyOperator` becomes `M`-valued. -/
def run (ctx : Ctx) : Nat → EvalState ctx.primCtx → EvalState ctx.primCtx
| 0, state => state
| fuel + 1, state =>
    match step ctx state with
    | none => state
    | some next => run ctx fuel next

variable {ctx : Ctx}

@[simp] theorem run_zero (state : EvalState ctx.primCtx) : run ctx 0 state = state := rfl

theorem run_succ (fuel : Nat) (state : EvalState ctx.primCtx) :
    run ctx (fuel + 1) state =
      match step ctx state with
      | none => state
      | some next => run ctx fuel next := rfl

/-- Once stuck, more fuel changes nothing. -/
theorem run_stuck {fuel : Nat} {state : EvalState ctx.primCtx} (h : step ctx state = none) :
    run ctx fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [run_succ, h]

theorem run_add (fuel₁ fuel₂ : Nat) (state : EvalState ctx.primCtx) :
    run ctx (fuel₁ + fuel₂) state = run ctx fuel₂ (run ctx fuel₁ state) := by
  induction fuel₁ generalizing state with
  | zero => rw [Nat.zero_add]; rfl
  | succ fuel₁ ih =>
      rw [show fuel₁ + 1 + fuel₂ = (fuel₁ + fuel₂) + 1 by omega, run_succ, run_succ]
      cases hstep : step ctx state with
      | none => rw [run_stuck hstep]
      | some next => exact ih next

/-- More fuel than needed is harmless, so two `EvaluatesTo` facts can always be run together. -/
theorem run_le {fuel extra : Nat} {state : EvalState ctx.primCtx} {value : Val ctx.primCtx}
    (h : (run ctx fuel state).result? = some value) :
    (run ctx (fuel + extra) state).result? = some value := by
  rw [run_add]
  have hstuck : step ctx (run ctx fuel state) = none := by
    unfold EvalState.result? at h
    split at h
    case h_1 value' hcontrol hstack =>
        rw [step.eq_def]
        split <;> simp_all
    case h_2 => simp at h
  rw [run_stuck hstuck]
  exact h


/-- Nothing ever reads below the top of the stack, so frames underneath ride along untouched.
  The two cases that *do* inspect the whole stack -- `ret` and `exit` against an empty one --
  are stuck, which is exactly what the `some` hypothesis rules out. This is what makes evaluating
  a subterm compose: the frames of the enclosing term are the `base`. -/
theorem step_weaken {c c' : Control ctx.primCtx} {e e' : Env ctx.primCtx}
    {S S' : List (Frame ctx.primCtx)} (base : List (Frame ctx.primCtx))
    (h : step ctx ⟨c, e, S⟩ = some ⟨c', e', S'⟩) :
    step ctx ⟨c, e, S ++ base⟩ = some ⟨c', e', S' ++ base⟩ := by
  match c, S with
  | .eval (.prim _ _), S =>
      simp only [step, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.var name), S =>
      simp only [step] at h ⊢
      cases hv : Scope.get? e name with
      | none => simp only [hv] at h; simp at h
      | some v =>
          simp only [hv, Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.exit _ _), S =>
      simp only [step, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.app _ _), S =>
      simp only [step, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.op name args), S =>
      simp only [step] at h ⊢
      cases hop : ctx.opCtx.get? name with
      | none => simp only [hop] at h; simp at h
      | some oper =>
          simp only [hop] at h ⊢
          have h' : (if args.length = oper.arity then driveOp oper.body args e S else none)
              = some ⟨c', e', S'⟩ := h
          show (if args.length = oper.arity then driveOp oper.body args e (S ++ base)
                else none) = _
          by_cases hlen : args.length = oper.arity
          · rw [if_pos hlen] at h' ⊢; exact driveOp_weaken base h'
          · rw [if_neg hlen] at h'; simp at h'
  | .eval (.call name args), S =>
      simp only [step] at h ⊢
      cases hb : ctx.blockCtx.get? name with
      | none => simp only [hb] at h; simp at h
      | some block =>
          simp only [hb] at h ⊢
          cases args with
          | nil => exact enterBlock_weaken base h
          | cons a r =>
              simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .ret _, [] => simp only [step] at h; simp at h
  | .exit _ _, [] => simp only [step] at h; simp at h
  | .ret v, .exitValue _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .ret v, .opBody resume r env' :: rest =>
      simp only [List.cons_append]
      exact driveOp_weaken base h
  | .ret v, .callArgs n b done r env' :: rest =>
      simp only [step, List.cons_append] at h ⊢
      cases r with
      | nil => exact enterBlock_weaken base h
      | cons a r =>
          simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .ret v, .appFn args env' :: rest =>
      simp only [step, List.cons_append] at h ⊢
      cases args with
      | nil =>
          cases hap : Term.evalApp v [] with
          | none => simp only [hap] at h; simp at h
          | some w =>
              simp only [hap, Option.map_some, Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      | cons a r =>
          simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .ret v, .appArgs f done r env' :: rest =>
      simp only [step, List.cons_append] at h ⊢
      cases r with
      | nil =>
          cases hap : Term.evalApp f (done ++ [v]) with
          | none => simp only [hap] at h; simp at h
          | some w =>
              simp only [hap, Option.map_some, Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      | cons a r =>
          simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .ret v, .instrs n r res env' :: rest =>
      obtain ⟨delta, cc, ee, hI⟩ := EvalState.enterInstrs_stack r res (env' ++ [(n, v)])
      simp only [step, List.cons_append, hI, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | .ret v, .call _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .call target env' :: rest =>
      simp only [step, List.cons_append] at h ⊢
      by_cases ht : b = target
      · simp only [if_pos ht, Option.some.injEq, EvalState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      · simp only [if_neg ht, Option.some.injEq, EvalState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .exitValue _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .opBody _ _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .callArgs _ _ _ _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .appFn _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .appArgs _ _ _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .instrs _ _ _ _ :: rest =>
      simp only [step, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp

/-- Exactly `n` steps, with no early stopping, so the count is usable for induction.
  (`run` stops when it gets stuck, which is what the tactic wants and proofs do not.) -/
def stepN (ctx : Ctx) : Nat → EvalState ctx.primCtx → Option (EvalState ctx.primCtx)
| 0, state => some state
| fuel + 1, state => (step ctx state).bind (stepN ctx fuel)

@[simp] theorem stepN_zero (state : EvalState ctx.primCtx) : stepN ctx 0 state = some state := rfl

theorem stepN_succ (fuel : Nat) (state : EvalState ctx.primCtx) :
    stepN ctx (fuel + 1) state = (step ctx state).bind (stepN ctx fuel) := rfl

theorem stepN_add (fuel₁ fuel₂ : Nat) (state : EvalState ctx.primCtx) :
    stepN ctx (fuel₁ + fuel₂) state = (stepN ctx fuel₁ state).bind (stepN ctx fuel₂) := by
  induction fuel₁ generalizing state with
  | zero => rw [Nat.zero_add]; rfl
  | succ fuel₁ ih =>
      rw [show fuel₁ + 1 + fuel₂ = (fuel₁ + fuel₂) + 1 by omega, stepN_succ, stepN_succ]
      cases hstep : step ctx state with
      | none => simp
      | some next => simpa using ih next

/-- `step_weaken`, lifted to a whole run. -/
theorem stepN_weaken {fuel : Nat} {c c' : Control ctx.primCtx} {e e' : Env ctx.primCtx}
    {S S' : List (Frame ctx.primCtx)} (base : List (Frame ctx.primCtx))
    (h : stepN ctx fuel ⟨c, e, S⟩ = some ⟨c', e', S'⟩) :
    stepN ctx fuel ⟨c, e, S ++ base⟩ = some ⟨c', e', S' ++ base⟩ := by
  induction fuel generalizing c e S with
  | zero =>
      simp only [stepN_zero, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
  | succ fuel ih =>
      rw [stepN_succ] at h ⊢
      cases hstep : step ctx ⟨c, e, S⟩ with
      | none => rw [hstep] at h; simp at h
      | some next =>
          obtain ⟨c₁, e₁, S₁⟩ := next
          rw [step_weaken base hstep]
          rw [hstep] at h
          simpa using ih (by simpa using h)

/-- A `run` that reaches a state is witnessed by an exact number of steps. -/
theorem exists_stepN_run (fuel : Nat) (state : EvalState ctx.primCtx) :
    ∃ k, stepN ctx k state = some (run ctx fuel state) := by
  induction fuel generalizing state with
  | zero => exact ⟨0, rfl⟩
  | succ fuel ih =>
      rw [run_succ]
      cases hstep : step ctx state with
      | none => exact ⟨0, rfl⟩
      | some next =>
          obtain ⟨k, hk⟩ := ih next
          exact ⟨k + 1, by rw [stepN_succ, hstep]; simpa using hk⟩

/-- Conversely, an exact run with no stuck state is what `run` computes. -/
theorem run_eq_of_stepN {fuel : Nat} {state next : EvalState ctx.primCtx}
    (h : stepN ctx fuel state = some next) : run ctx fuel state = next := by
  induction fuel generalizing state with
  | zero => simpa using h
  | succ fuel ih =>
      rw [stepN_succ] at h
      rw [run_succ]
      cases hstep : step ctx state with
      | none => rw [hstep] at h; simp at h
      | some s₁ => rw [hstep] at h; exact ih (by simpa using h)



end EvalState

/-- `term` evaluates to `value` in `env`: some finite number of steps reaches a state that is
  handing `value` back with nothing pending. -/
def EvaluatesTo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (value : Val ctx.primCtx) : Prop :=
  ∃ fuel, (EvalState.run ctx fuel (EvalState.start env term)).result? = some value


/-- Calling `name` on argument *values* produces `value`.

  Specs are stated this way, not as `EvaluatesTo … (.call name args) …`, because an induction
  hypothesis has to match the machine part-way through a run. At the recursive call the machine
  sits at `enterBlock name block [Val.nat (x+1), Val.nat y] …`, while the surface term still
  reads `.call name [op "add" .., op "sub" ..]` -- those coincide only after the arguments have
  been evaluated, so the spec must speak about the values.

  Quantifying over `env` and `base` is what makes the hypothesis applicable at the call site:
  `enterBlock` bakes the caller's environment into the `Frame.call` it pushes, so a spec fixed
  at `[] []` would not transport. -/
def EvaluatesCall (ctx : Ctx) (name : String) (vargs : List (Val ctx.primCtx))
    (value : Val ctx.primCtx) : Prop :=
  ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
    ∃ block st fuel scope,
      ctx.blockCtx.get? name = some block ∧
      EvalState.enterBlock name block vargs env base = some st ∧
      EvalState.stepN ctx fuel st = some ⟨.ret value, scope, base⟩

/-- Evaluation is deterministic, so the fuel is an artefact of the *proof*, not of the statement:
  a term has at most one value. This is what licenses reading `EvaluatesTo` as a function. -/
theorem EvaluatesTo.unique {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {v₁ v₂ : Val ctx.primCtx}
    (h₁ : EvaluatesTo ctx env term v₁) (h₂ : EvaluatesTo ctx env term v₂) : v₁ = v₂ := by
  obtain ⟨fuel₁, h₁⟩ := h₁
  obtain ⟨fuel₂, h₂⟩ := h₂
  have e₁ := EvalState.run_le (extra := fuel₂) h₁
  have e₂ := EvalState.run_le (extra := fuel₁) h₂
  rw [show fuel₂ + fuel₁ = fuel₁ + fuel₂ by omega] at e₂
  rw [e₁] at e₂
  exact Option.some.inj e₂


/-- Evaluating a term is insensitive to work already pending beneath it -- weakening, lifted to
  `EvaluatesTo`. This is what an induction over a recursive block consumes: the hypothesis is
  about a run from an empty stack, but it is applied part-way through a run, where the caller's
  frames are still there. -/
theorem EvaluatesTo.weaken {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} (h : EvaluatesTo ctx env term value)
    (base : List (Frame ctx.primCtx)) :
    ∃ fuel scope, EvalState.stepN ctx fuel ⟨.eval term, env, base⟩ =
      some ⟨.ret value, scope, base⟩ := by
  obtain ⟨fuel, hrun⟩ := h
  obtain ⟨k, hk⟩ := EvalState.exists_stepN_run fuel (EvalState.start env term)
  cases hfin : EvalState.run ctx fuel (EvalState.start env term) with
  | mk fc fe fs =>
      rw [hfin] at hk hrun
      refine ⟨k, fe, ?_⟩
      unfold EvalState.result? at hrun
      split at hrun
      case h_2 => simp at hrun
      case h_1 v hc hs =>
          simp only [Option.some.injEq] at hrun
          subst hrun
          simp only at hc hs
          subst hc
          subst hs
          have hw := EvalState.stepN_weaken (fuel := k) (base := base) hk
          simpa using hw


/-! ### the calculus, on the machine

  These replace the corresponding equations of `Zag/Eval.lean`, which are stated against the
  big-step evaluator. That evaluator cannot survive: parameterising it over the context's monad
  needs `partial_fixpoint` to recurse under that monad's `bind`, which needs a `CCPO` on its
  result type -- and the *pure* instance, `Id`, is exactly the one that has none, since
  `Id Empty = Empty` has no least element. Small-step has no fixpoint and so no such obligation.

  Each rule here is proved by stepping the machine, so it is `propext, Quot.sound` only, where
  the big-step versions inherit `Classical.choice` from the fixpoint. -/

theorem EvaluatesTo.prim (ty : Ty) (val : Ty.type ctx.primCtx ty) :
    EvaluatesTo ctx env (.prim ty val) (Val.mk ty val) :=
  ⟨1, rfl⟩

theorem EvaluatesTo.var_iff {name : String} {v : Val ctx.primCtx} :
    EvaluatesTo ctx env (.var name) v ↔ Scope.get? env name = some v := by
  constructor
  · rintro ⟨fuel, hrun⟩
    cases hv : Scope.get? env name with
    | none =>
        have hstuck : EvalState.step ctx (EvalState.start env (.var name)) = none := by
          simp [EvalState.step, EvalState.start, hv]
        rw [EvalState.run_stuck hstuck] at hrun
        simp [EvalState.start, EvalState.result?] at hrun
    | some w =>
        have hstep : EvalState.step ctx (EvalState.start env (.var name))
            = some ⟨.ret w, env, []⟩ := by simp [EvalState.step, EvalState.start, hv]
        cases fuel with
        | zero => simp [EvalState.start, EvalState.result?] at hrun
        | succ fuel =>
            simp only [EvalState.run_succ, hstep] at hrun
            have : EvalState.step ctx ⟨Control.ret w, env, []⟩ = none := by simp [EvalState.step]
            rw [EvalState.run_stuck this] at hrun
            simp [EvalState.result?] at hrun
            simp [hrun]
  · intro hv
    exact ⟨1, by simp [EvalState.run, EvalState.step, EvalState.start, EvalState.result?, hv]⟩

/-- Every term of a list evaluates, pointwise, to the corresponding value. -/
inductive EvaluatesToAll (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Term ctx.primCtx) → List (Val ctx.primCtx) → Prop where
| nil : EvaluatesToAll ctx env [] []
| cons {term terms value values} :
    EvaluatesTo ctx env term value → EvaluatesToAll ctx env terms values →
    EvaluatesToAll ctx env (term :: terms) (value :: values)

open EvalState in
/-- The argument-collecting loop: from "about to evaluate `arg`, with `done` already collected
  and `rest` still to go", the machine reaches exactly the callee's entry state. Stated as an
  equation so that an arity mismatch -- where `enterBlock` is `none` -- is covered too. -/
theorem EvalState.stepN_callArgs {name : String} {block : Block ctx.primCtx}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)} :
    ∀ (rest : List (Term ctx.primCtx)) (values : List (Val ctx.primCtx))
      (arg : Term ctx.primCtx) (value : Val ctx.primCtx) (done : List (Val ctx.primCtx)),
      EvaluatesTo ctx env arg value →
      EvaluatesToAll ctx env rest values →
      ∃ n, stepN ctx n ⟨.eval arg, env, .callArgs name block done rest env :: S⟩
        = enterBlock name block (done ++ value :: values) env S := by
  intro rest
  induction rest with
  | nil =>
      intro values arg value done harg hrest
      cases hrest
      obtain ⟨n, scope, hrun⟩ := EvaluatesTo.weaken harg (.callArgs name block done [] env :: S)
      refine ⟨n + 1, ?_⟩
      rw [stepN_add, hrun]
      simp only [Option.bind_some, stepN_succ, step]
      cases h : enterBlock name block (done ++ [value]) env S <;> simp [h]
  | cons a r ih =>
      intro values arg value done harg hrest
      cases hrest with
      | cons hva hvr =>
          rename_i va vr
          obtain ⟨n, scope, hrun⟩ := EvaluatesTo.weaken harg (.callArgs name block done (a :: r) env :: S)
          obtain ⟨m, hstep⟩ := ih vr a va (done ++ [value]) hva hvr
          refine ⟨n + 1 + m, ?_⟩
          rw [stepN_add, stepN_add, hrun]
          simp only [Option.bind_some, stepN_succ, step]
          simpa using hstep

open EvalState in
/-- A `call` reaches the callee's entry state once its arguments have evaluated. This is the
  lemma that lets a specification be stated about argument *values*. -/
theorem EvalState.stepN_call {name : String} {block : Block ctx.primCtx}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)}
    {args : List (Term ctx.primCtx)} {vargs : List (Val ctx.primCtx)}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : EvaluatesToAll ctx env args vargs) :
    ∃ n, stepN ctx n ⟨.eval (.call name args), env, S⟩
      = enterBlock name block vargs env S := by
  cases hargs with
  | nil =>
      refine ⟨1, ?_⟩
      simp only [stepN_succ, step, hblock, Option.bind_some, stepN_zero]
      cases h : enterBlock name block [] env S <;> simp [h]
  | cons harg hrest =>
      rename_i arg args value values
      obtain ⟨n, hsteps⟩ :=
        EvalState.stepN_callArgs (name := name) (block := block) (S := S)
          args values arg value [] harg hrest
      refine ⟨1 + n, ?_⟩
      rw [stepN_add]
      simp only [stepN_succ, step, hblock, Option.bind_some, stepN_zero]
      simpa using hsteps

end Zag
