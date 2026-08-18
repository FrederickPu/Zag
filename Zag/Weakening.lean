import Zag.Machine

/-!
# Weakening, and what a stuck state can be

Work pending *beneath* a computation is never read, so a computation behaves identically with
more frames underneath and leaves them intact. That is `step_weaken`, and it is what lets a
specification proved about a run from an empty stack be applied part-way through another run.

It is true because `EvalState.step` only ever inspects the top frame.
-/

namespace Zag

namespace EvalState

variable {primCtx : PrimitiveCtx}
variable {ctx : Ctx}

/-! ### weakening

  The stack is the ambient context of a computation, and these say what weakening always says:
  enlarging the context leaves the derivation alone. Concretely, work pending *beneath* a
  computation is never read, so the computation behaves identically and leaves that work intact.

  This is what makes a subterm compose: when an operand is evaluated, the frames belonging to
  the enclosing operator are the `base` being weakened in. It is also what an induction over a
  recursive block needs -- the hypothesis speaks about a run from an empty stack, but gets used
  part-way through a run, where the caller's frames are still pending. -/

theorem driveOp_weaken {body : Op.Body primCtx} {rest : List (Term primCtx)}
    {env : Env primCtx} {S : List (Frame primCtx)} {c' : Action primCtx} {e' : Env primCtx}
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
      | apply fn args resume =>
          simp [driveOp] at h ⊢
          simp [← h.1, ← h.2.1, ← h.2.2]

theorem driveOpVals_weaken {body : Op.Body primCtx} {rest : List (Val primCtx)}
    {env : Env primCtx} {S : List (Frame primCtx)} {c' : Action primCtx} {e' : Env primCtx}
    {S' : List (Frame primCtx)} (base : List (Frame primCtx))
    (h : driveOpVals body rest env S = some ⟨c', e', S'⟩) :
    driveOpVals body rest env (S ++ base) = some ⟨c', e', S' ++ base⟩ := by
  induction rest generalizing body with
  | nil => cases body <;> simp [driveOpVals] at h ⊢ <;> simp [← h.1, ← h.2.1, ← h.2.2]
  | cons value rest ih =>
      cases body with
      | fail => simp [driveOpVals] at h
      | done result => simp [driveOpVals] at h ⊢; simp [← h.1, ← h.2.1, ← h.2.2]
      | next evaluate resume =>
          cases evaluate <;> rw [driveOpVals] at h ⊢ <;> exact ih h
      | apply fn args resume =>
          simp [driveOpVals] at h ⊢
          simp [← h.1, ← h.2.1, ← h.2.2]

/-- Where entering a block body lands does not depend on what was already on the stack. -/
theorem enterInstrs_stack (instrs : List (Instr primCtx)) (result : Term primCtx)
    (env : Env primCtx) :
    ∃ delta c e, ∀ S : List (Frame primCtx),
      enterInstrs instrs result env S = ⟨c, e, delta ++ S⟩ := by
  cases instrs with
  | nil => exact ⟨[], .eval result, env, fun _ => rfl⟩
  | cons instr rest =>
      exact ⟨[.instrs instr.name rest result env], .eval instr.value, env, by
        intro S; simp [enterInstrs]⟩

theorem enterBlock_weaken {name : String} {block : Block primCtx}
    {vargs : List (Val primCtx)} {env : Env primCtx} {S : List (Frame primCtx)}
    {c' : Action primCtx} {e' : Env primCtx} {S' : List (Frame primCtx)}
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

/-- Applying a value does not depend on what was already pending beneath it. Both halves are
  already weakening-safe: a primitive application leaves the stack alone, and entering a block is
  `enterBlock_weaken`. -/
theorem applyValue_weaken {ctx : Ctx} {fn : Val ctx.primCtx} {vargs : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)} {c' : Action ctx.primCtx}
    {e' : Env ctx.primCtx} {S' : List (Frame ctx.primCtx)} (base : List (Frame ctx.primCtx))
    (h : applyValue ctx fn vargs env S = some ⟨c', e', S'⟩) :
    applyValue ctx fn vargs env (S ++ base) = some ⟨c', e', S' ++ base⟩ := by
  cases fn with
  | blockRef name argTys outTy =>
      simp only [applyValue] at h ⊢
      cases hblk : ctx.blockCtx.get? name with
      | none => simp [hblk] at h
      | some block =>
          simp only [hblk] at h ⊢
          exact enterBlock_weaken base h
  | opRef name captured argTys outTy =>
      simp only [applyValue] at h ⊢
      cases hop : ctx.opCtx.get? name with
      | none => simp [hop] at h
      | some oper =>
          simp only [hop] at h ⊢
          cases hbody : oper.body name (captured.length + vargs.length) with
          | none => simp [hbody] at h
          | some body =>
              simp only [hbody] at h ⊢
              exact driveOpVals_weaken base h
  | mk fnTy fnVal =>
      simp only [applyValue] at h ⊢
      cases hap : Term.evalApp (Val.mk fnTy fnVal) vargs with
      | none => simp [hap] at h
      | some w =>
          simp only [hap, Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; simp


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
theorem step_weaken {c c' : Action ctx.primCtx} {e e' : Env ctx.primCtx}
    {S S' : List (Frame ctx.primCtx)} (base : List (Frame ctx.primCtx))
    (h : step ctx ⟨c, e, S⟩ = some ⟨c', e', S'⟩) :
    step ctx ⟨c, e, S ++ base⟩ = some ⟨c', e', S' ++ base⟩ := by
  match c, S with
  | .stuck, S => exact absurd h (by simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame])
  | .eval (.prim _ _), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.var name), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h ⊢
      cases hv : Scope.get? e name with
      | none =>
          simp only [hv] at h ⊢
          cases hblk : ctx.blockCtx.get? name with
          | none => simp only [hblk] at h; simp at h
          | some block =>
              simp only [hblk, Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      | some v =>
          simp only [hv, Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.exit _ _), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.app _ _), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .eval (.op name args), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h ⊢
      cases hop : ctx.opCtx.get? name with
      | none => simp only [hop] at h; simp at h
      | some oper =>
          simp only [hop] at h ⊢
          cases hbody : oper.body name args.length with
          | none => simp [hbody] at h
          | some body =>
              simp only [hbody] at h ⊢
              exact driveOp_weaken base h
  | .eval (.call name args), S =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h ⊢
      cases hb : ctx.blockCtx.get? name with
      | none => simp only [hb] at h; simp at h
      | some block =>
          simp only [hb] at h ⊢
          cases args with
          | nil =>
              simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp
          | cons a r =>
              simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .apply fn args, S => exact applyValue_weaken base h
  | .ret _, [] => simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h; simp at h
  | .exit _ _, [] => simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h; simp at h
  | .ret v, .opBody resume r env' :: rest =>
      simp only [List.cons_append]
      exact driveOp_weaken base h
  | .ret v, .opBodyVals resume r env' :: rest =>
      simp only [List.cons_append]
      exact driveOpVals_weaken base h
  | .ret v, .args sink done r env' :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append] at h ⊢
      cases r with
      | cons a r =>
          simp only [Option.some.injEq, EvalState.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      | nil =>
          cases sink with
          | apply =>
              cases hvals : done ++ [v] with
              | nil => simp [hvals] at h
              | cons fn vargs =>
                  simp only [hvals, Option.some.injEq, EvalState.mk.injEq] at h ⊢
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  simp
          | exitTo blockName =>
              cases hvals : done ++ [v] with
              | nil => simp [hvals] at h
              | cons v₀ tl =>
                  cases tl with
                  | nil =>
                      simp only [hvals, Option.some.injEq, EvalState.mk.injEq] at h ⊢
                      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
                  | cons _ _ => simp [hvals] at h
  | .ret v, .instrs n r res env' :: rest =>
      obtain ⟨delta, cc, ee, hI⟩ := EvalState.enterInstrs_stack r res (env' ++ [(n, v)])
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, hI, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | .ret v, .call _ _ :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .args _ _ _ _ :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .opBody _ _ _ :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .opBodyVals _ _ _ :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .instrs _ _ _ _ :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append, Option.some.injEq, EvalState.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
  | .exit b v, .call target env' :: rest =>
      simp only [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append] at h ⊢
      by_cases ht : b = target
      · simp only [if_pos ht, Option.some.injEq, EvalState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp
      · simp only [if_neg ht, Option.some.injEq, EvalState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h; first | rfl | simp


theorem stepN_add (fuel₁ fuel₂ : Nat) (state : EvalState ctx.primCtx) :
    stepN ctx (fuel₁ + fuel₂) state = (stepN ctx fuel₁ state).bind (stepN ctx fuel₂) := by
  induction fuel₁ generalizing state with
  | zero => rw [Nat.zero_add]; rfl
  | succ fuel₁ ih =>
      rw [show fuel₁ + 1 + fuel₂ = (fuel₁ + fuel₂) + 1 by omega, stepN_succ, stepN_succ]
      cases hstep : step ctx state with
      | none => simp
      | some next => simpa using ih next

theorem stepN_ret_empty_none {fuel : Nat} {value : Val ctx.primCtx}
    {scope : Env ctx.primCtx} {state : EvalState ctx.primCtx}
    (h : stepN ctx (fuel + 1) ⟨.ret value, scope, []⟩ = some state) : False := by
  rw [stepN_succ] at h
  simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at h

/-- `step_weaken`, lifted to a whole run. -/
theorem stepN_weaken {fuel : Nat} {c c' : Action ctx.primCtx} {e e' : Env ctx.primCtx}
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

theorem result?_appendStack_ne_nil {state : EvalState ctx.primCtx}
    {base : List (Frame ctx.primCtx)} (hne : base ≠ []) :
    (appendStack state base).result? = none := by
  cases state with
  | mk control env stack =>
      cases control <;> cases stack <;> simp [appendStack, result?, hne]

theorem run_exit_opBodies_result?_none {fuel : Nat} {name : String}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (hbase : Frame.OpBodies base) :
    (run ctx fuel ⟨.exit name value, env, base⟩).result? = none := by
  induction fuel generalizing base env with
  | zero =>
      cases base <;> simp [run, result?]
  | succ fuel ih =>
      rw [run_succ]
      cases hbase with
      | nil => simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, result?]
      | cons hrest =>
          simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame]
          exact ih hrest
      | consVals hrest =>
          simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame]
          exact ih hrest

theorem driveOp_append_eq_none {body : Op.Body ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} :
    driveOp body terms env (stack ++ base) = none ↔ driveOp body terms env stack = none := by
  induction terms generalizing body with
  | nil => cases body <;> simp [driveOp]
  | cons term terms ih =>
      cases body with
      | fail => simp [driveOp]
      | done value => simp [driveOp]
      | next evaluate resume =>
          cases evaluate <;> simp [driveOp, ih]
      | apply fn args resume => simp [driveOp]

theorem driveOpVals_append_eq_none {body : Op.Body ctx.primCtx}
    {values : List (Val ctx.primCtx)} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} :
    driveOpVals body values env (stack ++ base) = none ↔
      driveOpVals body values env stack = none := by
  induction values generalizing body with
  | nil => cases body <;> simp [driveOpVals]
  | cons value values ih =>
      cases body with
      | fail => simp [driveOpVals]
      | done result => simp [driveOpVals]
      | next evaluate resume => cases evaluate <;> simp [driveOpVals, ih]
      | apply fn args resume => simp [driveOpVals]

theorem enterBlock_append_eq_none {name : String} {block : Block ctx.primCtx}
    {vargs : List (Val ctx.primCtx)} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} :
    enterBlock name block vargs env (stack ++ base) = none ↔
      enterBlock name block vargs env stack = none := by
  unfold enterBlock
  by_cases hlen : vargs.length = block.params.length <;> simp [hlen]

theorem applyValue_append_eq_none {ctx : Ctx} {fn : Val ctx.primCtx}
    {vargs : List (Val ctx.primCtx)} {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)}
    (base : List (Frame ctx.primCtx)) :
    (applyValue ctx fn vargs env (S ++ base) = none) ↔ (applyValue ctx fn vargs env S = none) := by
  cases fn with
  | blockRef name argTys outTy =>
      simp only [applyValue]
      cases hblk : ctx.blockCtx.get? name with
      | none => simp [hblk]
      | some block => simp only [hblk]; exact enterBlock_append_eq_none (base := base)
  | opRef name captured argTys outTy =>
      simp only [applyValue]
      cases hop : ctx.opCtx.get? name with
      | none => simp [hop]
      | some oper =>
          simp only [hop]
          cases hbody : oper.body name (captured.length + vargs.length) with
          | none => simp [hbody]
          | some body =>
              simp only [hbody]
              exact driveOpVals_append_eq_none (base := base)
  | mk fnTy fnVal =>
      simp only [applyValue]
      cases Term.evalApp (Val.mk fnTy fnVal) vargs <;> simp

set_option linter.unusedSimpArgs false in
theorem step_appendStack_none_or_exit {state : EvalState ctx.primCtx}
    {base : List (Frame ctx.primCtx)}
    (hresult : state.result? = none) (hstep : step ctx state = none) :
    step ctx (appendStack state base) = none ∨
      ∃ name value env, state = ⟨.exit name value, env, []⟩ := by
  cases state with
  | mk control env stack =>
      cases control with
      | stuck => left; rfl
      | eval term =>
          left
          cases term with
          | prim ty val => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
          | var name =>
              cases hv : Scope.get? env name with
              | some v => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hv] at hstep
              | none =>
                  cases hblk : ctx.blockCtx.get? name with
                  | none => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hv, hblk]
                  | some block => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hv, hblk] at hstep
          | app fn args => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
          | op name args =>
              simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame]
              cases hop : ctx.opCtx.get? name with
              | none => simp [hop]
              | some oper =>
                  simp [hop] at hstep ⊢
                  cases hbody : oper.body name args.length with
                  | none => simp [hbody]
                  | some body =>
                      have hdrive : driveOp body args env stack = none := by
                        simpa [step, EvalState.evalStep, EvalState.resumeFrame,
                          EvalState.unwindFrame, hop, hbody] using hstep
                      simp [hbody]
                      exact (driveOp_append_eq_none (base := base)).mpr hdrive
          | call name args =>
              simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame]
              cases hblock : ctx.blockCtx.get? name with
              | none => simp [hblock]
              | some block =>
                  cases args <;>
                    simp [step, EvalState.evalStep, EvalState.resumeFrame,
                      EvalState.unwindFrame, hblock] at hstep
          | exit blockName value => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
      | apply fn args =>
          left
          simp [appendStack, step] at hstep ⊢
          exact (applyValue_append_eq_none (base := base)).mpr hstep
      | ret value =>
          cases stack with
          | nil => simp [result?] at hresult
          | cons frame rest =>
              left
              cases frame with
              | opBody resume terms frameEnv =>
                  simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep ⊢
                  exact (driveOp_append_eq_none (base := base)).mpr hstep
              | opBodyVals resume values frameEnv =>
                  simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep ⊢
                  exact (driveOpVals_append_eq_none (base := base)).mpr hstep
              | args sink done terms frameEnv =>
                  cases terms with
                  | cons arg terms => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
                  | nil =>
                      simp only [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append] at hstep ⊢
                      cases sink with
                      | apply =>
                          cases hvals : done ++ [value] with
                          | nil => simp [hvals]
                           | cons fn vargs =>
                               simp [hvals] at hstep
                      | exitTo blockName =>
                          cases hvals : done ++ [value] with
                          | nil => simp [hvals]
                          | cons v₀ tl =>
                              cases tl with
                              | nil => simp [hvals] at hstep
                              | cons _ _ => simp [hvals]
              | instrs name instrs result frameEnv => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
              | call blockName frameEnv => simp [appendStack, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
      | exit name value =>
          cases stack with
          | nil =>
              right
              exact ⟨name, value, env, rfl⟩
          | cons frame rest =>
              exfalso
              cases frame with
              | args sink done terms frameEnv => simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
              | opBody resume terms frameEnv => simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
              | opBodyVals resume values frameEnv => simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
              | instrs instrName instrs result frameEnv => simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame] at hstep
              | call blockName frameEnv =>
                  by_cases htarget : name = blockName <;> simp [step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, htarget] at hstep




end EvalState

end Zag
