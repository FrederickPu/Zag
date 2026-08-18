import Zag.EvalAttr
import Zag.Theory
import Zag.Weakening

/-!
# What it means to evaluate

`EvaluatesTo` / `EvaluatesCall` / `EvaluatesFrom` and the calculus over them. The machine itself
is in `Zag/Machine.lean` and its weakening metatheory in `Zag/Weakening.lean`.

Specifications are stated over argument *values* rather than terms, because an induction
hypothesis has to match the machine part-way through a run -- see `EvaluatesCall`.
-/

namespace Zag

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

/-- `state` eventually hands `value` to `base`, leaving the intermediate scope existential.

  This is the compositional form used by proof automation: a proof can step to a call,
  consume an `EvaluatesCall` hypothesis for that call, then keep stepping the continuation. -/
def EvaluatesFrom (ctx : Ctx) (state : EvalState ctx.primCtx)
    (value : Val ctx.primCtx) (base : List (Frame ctx.primCtx)) : Prop :=
  ∃ fuel scope, EvalState.stepN ctx fuel state = some ⟨.ret value, scope, base⟩

namespace EvaluatesFrom

theorem done {ctx : Ctx} {value : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {base : List (Frame ctx.primCtx)} :
    EvaluatesFrom ctx ⟨.ret value, scope, base⟩ value base :=
  ⟨0, scope, rfl⟩

theorem of_result? {ctx : Ctx} {state : EvalState ctx.primCtx}
    {value : Val ctx.primCtx} (h : state.result? = some value) :
    EvaluatesFrom ctx state value [] := by
  cases state with
  | mk control env stack =>
      cases control <;> cases stack <;> simp [EvalState.result?] at h
      subst h
      exact done

theorem ret_empty_eq {ctx : Ctx} {result value : Val ctx.primCtx}
    {scope : Env ctx.primCtx}
    (h : EvaluatesFrom ctx ⟨.ret result, scope, []⟩ value []) : value = result := by
  obtain ⟨fuel, finalScope, hsteps⟩ := h
  cases fuel with
  | zero =>
      simp only [EvalState.stepN_zero, Option.some.injEq, EvalState.mk.injEq,
        Action.ret.injEq] at hsteps
      exact hsteps.1.symm
  | succ fuel =>
      exact False.elim (EvalState.stepN_ret_empty_none (fuel := fuel)
        (value := result) (scope := scope) hsteps)

theorem step {ctx : Ctx} {state next : EvalState ctx.primCtx}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (hstep : EvalState.step ctx state = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx state value base := by
  obtain ⟨fuel, scope, hnext⟩ := hnext
  refine ⟨fuel + 1, scope, ?_⟩
  rw [EvalState.stepN_succ, hstep]
  exact hnext

theorem trans_stepN {ctx : Ctx} {fuel₀ : Nat} {state mid : EvalState ctx.primCtx}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (hprefix : EvalState.stepN ctx fuel₀ state = some mid)
    (hmid : EvaluatesFrom ctx mid value base) :
    EvaluatesFrom ctx state value base := by
  obtain ⟨fuel₁, scope, hmid⟩ := hmid
  refine ⟨fuel₀ + fuel₁, scope, ?_⟩
  rw [EvalState.stepN_add, hprefix]
  exact hmid

theorem bind {ctx : Ctx} {state : EvalState ctx.primCtx}
    {value finalValue : Val ctx.primCtx}
    {base finalBase : List (Frame ctx.primCtx)}
    (h : EvaluatesFrom ctx state value base)
    (hcont : ∀ scope, EvaluatesFrom ctx ⟨.ret value, scope, base⟩ finalValue finalBase) :
    EvaluatesFrom ctx state finalValue finalBase := by
  obtain ⟨fuel₀, scope₀, h₀⟩ := h
  obtain ⟨fuel₁, scope₁, h₁⟩ := hcont scope₀
  refine ⟨fuel₀ + fuel₁, scope₁, ?_⟩
  rw [EvalState.stepN_add, h₀]
  exact h₁

/-- If a run with only operator frames underneath eventually finishes, the computation above those
  frames must first have produced a value for its empty-stack continuation. -/
theorem exists_of_run_append_opBodies {ctx : Ctx} {state : EvalState ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {fuel : Nat} {final : Val ctx.primCtx}
    (hbase : Frame.OpBodies base) (hne : base ≠ [])
    (h : (EvalState.run ctx fuel (EvalState.appendStack state base)).result? = some final) :
    ∃ value, EvaluatesFrom ctx state value [] := by
  induction fuel generalizing state with
  | zero =>
      rw [EvalState.run_zero] at h
      rw [EvalState.result?_appendStack_ne_nil (state := state) hne] at h
      simp at h
  | succ fuel ih =>
      cases hresult : state.result? with
      | some value => exact ⟨value, of_result? hresult⟩
      | none =>
          have hfull := h
          rw [EvalState.run_succ] at h
          cases hstep : EvalState.step ctx state with
          | some next =>
              have happ : EvalState.step ctx (EvalState.appendStack state base) =
                  some (EvalState.appendStack next base) := by
                cases state
                cases next
                simpa [EvalState.appendStack] using EvalState.step_weaken base hstep
              rw [happ] at h
              obtain ⟨value, hvalue⟩ := ih h
              exact ⟨value, step hstep hvalue⟩
          | none =>
              obtain hnone | hexit :=
                EvalState.step_appendStack_none_or_exit hresult hstep
              · rw [hnone] at h
                rw [EvalState.result?_appendStack_ne_nil (state := state) hne] at h
                simp at h
              · obtain ⟨name, value, env, hstate⟩ := hexit
                subst state
                have hnoneRun :
                    (EvalState.run ctx (fuel + 1)
                      (EvalState.appendStack ⟨.exit name value, env, []⟩ base)).result? =
                      none := by
                  simpa [EvalState.appendStack] using
                    (EvalState.run_exit_opBodies_result?_none (ctx := ctx) (fuel := fuel + 1)
                      (name := name) (value := value) (env := env) hbase)
                rw [hnoneRun] at hfull
                simp at hfull

theorem drop_prefix {ctx : Ctx} {fuel₀ : Nat} {state mid : EvalState ctx.primCtx}
    {value : Val ctx.primCtx}
    (hprefix : EvalState.stepN ctx fuel₀ state = some mid)
    (hfrom : EvaluatesFrom ctx state value []) :
    EvaluatesFrom ctx mid value [] := by
  obtain ⟨fuel, scope, hsteps⟩ := hfrom
  by_cases hle : fuel₀ ≤ fuel
  · let rest := fuel - fuel₀
    have hfuel : fuel = fuel₀ + rest := by omega
    refine ⟨rest, scope, ?_⟩
    rw [hfuel, EvalState.stepN_add, hprefix] at hsteps
    simpa using hsteps
  · have hlt : fuel < fuel₀ := by omega
    let rest := fuel₀ - fuel - 1
    have hfuel₀ : fuel₀ = fuel + (rest + 1) := by omega
    rw [hfuel₀, EvalState.stepN_add, hsteps] at hprefix
    have hbad : EvalState.stepN ctx (rest + 1) ⟨.ret value, scope, []⟩ = some mid := by
      simpa using hprefix
    exact False.elim (EvalState.stepN_ret_empty_none (fuel := rest)
      (value := value) (scope := scope) hbad)

end EvaluatesFrom

theorem EvaluatesFrom.of_evaluatesTo {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx}
    (h : EvaluatesTo ctx env term value) :
    EvaluatesFrom ctx (EvalState.start env term) value [] := by
  obtain ⟨fuel, hrun⟩ := h
  obtain ⟨steps, hsteps⟩ := EvalState.exists_stepN_run fuel (EvalState.start env term)
  cases hstate : EvalState.run ctx fuel (EvalState.start env term) with
  | mk control scope stack =>
      rw [hstate] at hsteps hrun
      cases control <;> cases stack <;> simp [EvalState.result?] at hrun
      subst hrun
      exact ⟨steps, scope, hsteps⟩

theorem EvaluatesTo.of_evaluatesFrom {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx}
    (h : EvaluatesFrom ctx (EvalState.start env term) value []) :
    EvaluatesTo ctx env term value := by
  obtain ⟨fuel, scope, hsteps⟩ := h
  refine ⟨fuel, ?_⟩
  have hrun := EvalState.run_eq_of_stepN hsteps
  rw [hrun]
  rfl

namespace EvaluatesCall

theorem of_evaluatesFrom {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx}
    (h : ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
      ∃ block state,
        ctx.blockCtx.get? name = some block ∧
        EvalState.enterBlock name block vargs env base = some state ∧
        EvaluatesFrom ctx state value base) :
    EvaluatesCall ctx name vargs value := by
  intro env base
  obtain ⟨block, state, hblock, henter, hfrom⟩ := h env base
  obtain ⟨fuel, scope, hsteps⟩ := hfrom
  exact ⟨block, state, fuel, scope, hblock, henter, hsteps⟩

end EvaluatesCall

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

def Term.Terminates (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx) : Prop :=
  ∃ v, EvaluatesTo ctx env term v

/- two terms are equal at a type when they evaluate alike under every environment matching the
  scope they are stated in -/
structure Term.eq (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) (t₁ t₂ : Term ctx.primCtx) : Prop where
  hasType₁ : hasType ctx varCtx t₁ ty
  hasType₂ : hasType ctx varCtx t₂ ty
  eq : ∀ env : Env ctx.primCtx, env.Models varCtx → ∀ v,
    EvaluatesTo ctx env t₁ v ↔ EvaluatesTo ctx env t₂ v

/- Zag propositions can only be assigned semantics under a fixed `Ctx` -/
def Pr.interp (ctx : Ctx) :
    (ctxTy : Scope Ty) → (ctxTerm : Scope (Term ctx.primCtx)) → Pr (Term ctx.primCtx) → Prop
| ctxTy, ctxTerm, .eq varCtx ty x y =>
  Term.eq ctx (VarCtx.subst ctxTy varCtx) (Ty.subst ctxTy ty)
    (Term.subst ctxTerm x) (Term.subst ctxTerm y)
| ctxTy, ctxTerm, .hasType varCtx t ty =>
  Term.hasType ctx (VarCtx.subst ctxTy varCtx) (Term.subst ctxTerm t) (Ty.subst ctxTy ty)
| ctxTy, ctxTerm, .and p q =>
  Pr.interp ctx ctxTy ctxTerm p ∧ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .or p q =>
  Pr.interp ctx ctxTy ctxTerm p ∨ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .implies p q =>
  Pr.interp ctx ctxTy ctxTerm p → Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .forallTy name p =>
  ∀ (α : Ty), Pr.interp ctx (ctxTy ++ [(name, α)]) ctxTerm p
| ctxTy, ctxTerm, .forallTerm name p =>
  ∀ (x : Term ctx.primCtx), Pr.interp ctx ctxTy (ctxTerm ++ [(name, x)]) p

/- metatheory (in this case lean) determines which Zag propositions are provable -/
inductive Pr.Provable (ctx : Ctx)
    (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx)) (p : Pr (Term ctx.primCtx)) : Prop
| ofProof (proof : Pr.interp ctx ctxTy ctxTerm p)


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

/-- A name resolves to a local binding if there is one, and otherwise to the block of that name
  as a value -- which is why this needs `name` not to be a block. The `←` direction holds
  unconditionally, since a local binding shadows a block. -/
theorem EvaluatesTo.var_iff {name : String} {v : Val ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = none) :
    EvaluatesTo ctx env (.var name) v ↔ Scope.get? env name = some v := by
  constructor
  · rintro ⟨fuel, hrun⟩
    cases hv : Scope.get? env name with
    | none =>
        have hstuck : EvalState.step ctx (EvalState.start env (.var name)) = none := by
          simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, hv, hblock]
        rw [EvalState.run_stuck hstuck] at hrun
        simp [EvalState.start, EvalState.result?] at hrun
    | some w =>
        have hstep : EvalState.step ctx (EvalState.start env (.var name))
            = some ⟨.ret w, env, []⟩ := by simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, hv]
        cases fuel with
        | zero => simp [EvalState.start, EvalState.result?] at hrun
        | succ fuel =>
            simp only [EvalState.run_succ, hstep] at hrun
            have : EvalState.step ctx ⟨Action.ret w, env, []⟩ = none := by simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame]
            rw [EvalState.run_stuck this] at hrun
            simp [EvalState.result?] at hrun
            simp [hrun]
  · intro hv
    exact ⟨1, by simp [EvalState.run, EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, EvalState.result?, hv]⟩

/-- A block named where a value is expected evaluates to a reference to it. This is what makes
  `call f [x]` and `app (var f) [x]` agree. -/
theorem EvaluatesTo.var_block {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {block : Block ctx.primCtx}
    (hlocal : Scope.get? env name = none) (hblock : ctx.blockCtx.get? name = some block) :
    EvaluatesTo ctx env (.var name)
      (.blockRef name (block.params.map Prod.snd) block.outTy) :=
  ⟨1, by simp [EvalState.run, EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, EvalState.result?,
    hlocal, hblock]⟩

/-- Every term of a list evaluates, pointwise, to the corresponding value. -/
inductive EvaluatesToAll (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Term ctx.primCtx) → List (Val ctx.primCtx) → Prop where
| nil : EvaluatesToAll ctx env [] []
| cons {term terms value values} :
    EvaluatesTo ctx env term value → EvaluatesToAll ctx env terms values →
    EvaluatesToAll ctx env (term :: terms) (value :: values)

namespace EvaluatesToAll

theorem length_eq {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    (h : EvaluatesToAll ctx env terms values) : terms.length = values.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end EvaluatesToAll

namespace EvaluatesFrom

theorem driveOp {ctx : Ctx} {body : Op.Body ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)} {result : Val ctx.primCtx}
    (hargs : EvaluatesToAll ctx env terms values)
    (hbody : body.applyVals values = some result) :
    ∃ state, EvalState.driveOp body terms env S = some state ∧
      EvaluatesFrom ctx state result S := by
  induction terms generalizing body values S with
  | nil =>
      cases hargs
      cases body with
      | fail => simp [Op.Body.applyVals] at hbody
      | done value =>
          have hvalue : value = result := by simpa [Op.Body.applyVals] using hbody
          subst result
          exact ⟨⟨.ret value, env, S⟩, by simp [EvalState.driveOp], EvaluatesFrom.done⟩
      | next evaluate resume => simp [Op.Body.applyVals] at hbody
      | apply fn args resume => simp [Op.Body.applyVals] at hbody
  | cons term terms ih =>
      cases hargs with
      | cons hterm hterms =>
          rename_i termValue termValues
          cases body with
          | fail => simp [Op.Body.applyVals] at hbody
          | done value =>
              have hvalue : value = result := by simpa [Op.Body.applyVals] using hbody
              subst result
              exact ⟨⟨.ret value, env, S⟩, by simp [EvalState.driveOp], EvaluatesFrom.done⟩
          | next evaluate resume =>
              cases evaluate with
              | false =>
                  have hbody' : (resume none).applyVals termValues = some result := by
                    simpa [Op.Body.applyVals] using hbody
                  obtain ⟨state, hdrive, hfrom⟩ :=
                    ih (body := resume none) (values := termValues) (S := S) hterms hbody'
                  exact ⟨state, by simpa [EvalState.driveOp] using hdrive, hfrom⟩
              | true =>
                  have hbody' : (resume (some termValue)).applyVals termValues = some result := by
                    simpa [Op.Body.applyVals] using hbody
                  obtain ⟨state, hdrive, hfrom⟩ :=
                    ih (body := resume (some termValue)) (values := termValues) (S := S)
                      hterms hbody'
                  obtain ⟨fuel, scope, htermSteps⟩ :=
                    EvaluatesTo.weaken hterm (.opBody resume terms env :: S)
                  have hretStep : EvalState.step ctx
                      ⟨.ret termValue, scope, .opBody resume terms env :: S⟩ = some state := by
                    simpa [EvalState.step, hdrive]
                  exact ⟨⟨.eval term, env, .opBody resume terms env :: S⟩,
                    by simp [EvalState.driveOp],
                    EvaluatesFrom.trans_stepN htermSteps (EvaluatesFrom.step hretStep hfrom)⟩
          | apply fn args resume => simp [Op.Body.applyVals] at hbody

end EvaluatesFrom

theorem EvaluatesTo.op_applyVals {ctx : Ctx} {env : Env ctx.primCtx}
    {name : String} {args : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    {oper : Op ctx.primCtx} {result : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hargs : EvaluatesToAll ctx env args values)
    (happly : Op.applyValsAt name oper values = some result) :
    EvaluatesTo ctx env (.op name args) result := by
  have hargsLen : args.length = values.length := EvaluatesToAll.length_eq hargs
  unfold Op.applyValsAt at happly
  cases hstart : oper.body name values.length with
  | none => simp [hstart] at happly
  | some body =>
      have hbody : body.applyVals values = some result := by simpa [hstart] using happly
      obtain ⟨state, hdrive, hfrom⟩ :=
        EvaluatesFrom.driveOp (S := []) hargs hbody
      exact EvaluatesTo.of_evaluatesFrom
        (EvaluatesFrom.step (by
          simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame,
            EvalState.start, hop, hargsLen, hstart, hdrive]) hfrom)

open EvalState in
/-- Applying a block reference is entering that block. -/
theorem EvalState.applyValue_blockRef {name : String} {block : Block ctx.primCtx}
    {argTys : List Ty} {outTy : Ty} {vargs : List (Val ctx.primCtx)} {env : Env ctx.primCtx}
    {S : List (Frame ctx.primCtx)} (hblock : ctx.blockCtx.get? name = some block) :
    applyValue ctx (.blockRef name argTys outTy) vargs env S
      = enterBlock name block vargs env S := by
  simp [applyValue, hblock]

open EvalState in
/-- The argument-collecting loop: from "about to evaluate `arg`, with `done` already collected
  and `rest` still to go", the machine reaches exactly the application of `fn`. One lemma now
  serves calls and applications alike, because they share the frame. -/
theorem EvalState.stepN_applyArgs {fn : Val ctx.primCtx}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)} :
    ∀ (rest : List (Term ctx.primCtx)) (values : List (Val ctx.primCtx))
      (arg : Term ctx.primCtx) (value : Val ctx.primCtx) (done : List (Val ctx.primCtx)),
      EvaluatesTo ctx env arg value →
      EvaluatesToAll ctx env rest values →
      ∃ n, stepN ctx n ⟨.eval arg, env, .args .apply (fn :: done) rest env :: S⟩
        = some ⟨.apply fn (done ++ value :: values), env, S⟩ := by
  intro rest
  induction rest with
  | nil =>
      intro values arg value done harg hrest
      cases hrest
      obtain ⟨n, scope, hrun⟩ :=
        EvaluatesTo.weaken harg (.args .apply (fn :: done) [] env :: S)
      refine ⟨n + 1, ?_⟩
      rw [stepN_add, hrun]
      simp only [Option.bind_some, stepN_succ, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append]
      rfl
  | cons a r ih =>
      intro values arg value done harg hrest
      cases hrest with
      | cons hva hvr =>
          rename_i va vr
          obtain ⟨n, scope, hrun⟩ :=
            EvaluatesTo.weaken harg (.args .apply (fn :: done) (a :: r) env :: S)
          obtain ⟨m, hstep⟩ := ih vr a va (done ++ [value]) hva hvr
          refine ⟨n + 1 + m, ?_⟩
          rw [stepN_add, stepN_add, hrun]
          simp only [Option.bind_some, stepN_succ, step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, List.cons_append]
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
      refine ⟨2, ?_⟩
      simp [stepN, step, EvalState.evalStep, applyValue, hblock]
  | cons harg hrest =>
      rename_i arg args value values
      obtain ⟨n, hsteps⟩ :=
        EvalState.stepN_applyArgs
          (fn := .blockRef name (block.params.map Prod.snd) block.outTy) (S := S)
          args values arg value [] harg hrest
      let argState : EvalState ctx.primCtx :=
        ⟨.eval arg, env,
          .args .apply [.blockRef name (block.params.map Prod.snd) block.outTy] args env :: S⟩
      let applyState : EvalState ctx.primCtx :=
        ⟨.apply (.blockRef name (block.params.map Prod.snd) block.outTy) (value :: values),
          env, S⟩
      have hfirst : stepN ctx 1 ⟨.eval (.call name (arg :: args)), env, S⟩ = some argState := by
        simp [argState, stepN_succ, step, EvalState.evalStep, hblock]
      have hmiddle : stepN ctx n argState = some applyState := by
        simpa [argState, applyState] using hsteps
      have hlast : stepN ctx 1 applyState = enterBlock name block (value :: values) env S := by
        simp [applyState, stepN_succ, step, applyValue, hblock]
        cases enterBlock name block (value :: values) env S <;> rfl
      refine ⟨1 + n + 1, ?_⟩
      rw [show 1 + n + 1 = 1 + (n + 1) by omega, stepN_add]
      rw [hfirst]
      simp only [Option.bind_some]
      rw [stepN_add, hmiddle]
      exact hlast

/-- Finish a walk whose value is only *propositionally* equal to the target. This is what turns
  a leftover machine state into an arithmetic obligation: normalisation runs to the end and hands
  back `result = value` rather than an `EvaluatesFrom` the reader has to decode. -/
theorem EvaluatesFrom.done_of {ctx : Ctx} {result value : Val ctx.primCtx}
    {scope : Env ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (h : result = value) :
    EvaluatesFrom ctx ⟨.ret result, scope, base⟩ value base := by
  subst h
  exact EvaluatesFrom.done

/-- A no-op that only typechecks when the machine is about to make a call. Proof automation
  uses it as a *stopping condition*: normalisation walks the machine until it reaches a call and
  hands the goal back, rather than stepping into the callee -- which is where a run would either
  diverge or need an induction hypothesis. Discharging the call is the caller's job. -/
theorem EvaluatesFrom.atCall {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {env : Env ctx.primCtx} {S : List (Frame ctx.primCtx)}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (h : EvaluatesFrom ctx ⟨.eval (.call name args), env, S⟩ value base) :
    EvaluatesFrom ctx ⟨.eval (.call name args), env, S⟩ value base := h

/- Proof automation uses this identity rule to recognize a named operator before stepping it. -/
theorem EvaluatesFrom.atOp {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {value : Val ctx.primCtx}
    (h : EvaluatesFrom ctx ⟨.eval (.op name args), env, stack⟩ value base) :
    EvaluatesFrom ctx ⟨.eval (.op name args), env, stack⟩ value base := h

/- The application counterpart used when a CPS body reaches its operator continuation. -/
theorem EvaluatesFrom.atApply {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} {value : Val ctx.primCtx}
    (h : EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ value base) :
    EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ value base := h

theorem EvaluatesFrom.call_then {ctx : Ctx} {name : String}
    {args : List (Term ctx.primCtx)} {vargs : List (Val ctx.primCtx)}
    {value finalValue : Val ctx.primCtx}
    {env : Env ctx.primCtx} {S finalBase : List (Frame ctx.primCtx)}
    {block : Block ctx.primCtx}
    (hcall : EvaluatesCall ctx name vargs value)
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : EvaluatesToAll ctx env args vargs)
    (hcont : ∀ scope, EvaluatesFrom ctx ⟨.ret value, scope, S⟩ finalValue finalBase) :
    EvaluatesFrom ctx ⟨.eval (.call name args), env, S⟩ finalValue finalBase := by
  obtain ⟨n, hargsSteps⟩ := EvalState.stepN_call (ctx := ctx) (name := name)
    (block := block) (env := env) (S := S) (args := args) (vargs := vargs) hblock hargs
  obtain ⟨block', state, fuel, scope, hblock', henter, hsteps⟩ := hcall env S
  have hbeq : block = block' := by simpa [hblock] using hblock'
  subst block'
  have hprefix : EvalState.stepN ctx n ⟨.eval (.call name args), env, S⟩ = some state := by
    simpa [henter] using hargsSteps
  exact EvaluatesFrom.trans_stepN hprefix (EvaluatesFrom.bind ⟨fuel, scope, hsteps⟩ hcont)

theorem EvaluatesTo.call {ctx : Ctx} {name : String}
    {args : List (Term ctx.primCtx)} {vargs : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {block : Block ctx.primCtx}
    (hcall : EvaluatesCall ctx name vargs value)
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : EvaluatesToAll ctx env args vargs) :
    EvaluatesTo ctx env (.call name args) value :=
  EvaluatesTo.of_evaluatesFrom <|
    EvaluatesFrom.call_then (S := []) (finalBase := []) (block := block)
      (hcall := hcall) hblock hargs (fun _ => EvaluatesFrom.done)


end Zag
