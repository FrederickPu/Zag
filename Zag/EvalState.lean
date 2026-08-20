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

/-- `state` eventually hands `value` to `base`, leaving the intermediate scope existential.

  This is the compositional form used by proof automation: a proof can step to a call,
  consume an `EvaluatesCall` hypothesis for that call, then keep stepping the continuation. -/
def EvaluatesFrom (ctx : Ctx) (state : EvalState ctx.primCtx)
    (value : Val ctx.primCtx) (base : List (Frame ctx.primCtx)) : Prop :=
  ∃ fuel scope, EvalState.stepN ctx fuel state = some ⟨.ret value, scope, base⟩

/-- `term` evaluates to `value` in `env`: some finite number of steps reaches a state that is
  handing `value` back with nothing pending. -/
def EvaluatesTo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (value : Val ctx.primCtx) : Prop :=
  EvaluatesFrom ctx (EvalState.start env term) value []

/-- Evaluate a block body from top to bottom. Each instruction returns a value, that value is
  bound in the block environment, and the remaining instructions continue under the binding. -/
inductive EvaluatesInstrs (ctx : Ctx) :
    List (Instr ctx.primCtx) → Term ctx.primCtx → Env ctx.primCtx → Val ctx.primCtx → Prop where
| nil {result env value} :
    EvaluatesTo ctx env result value →
    EvaluatesInstrs ctx [] result env value
| cons {instr instrs result env instrValue value} :
    EvaluatesTo ctx env instr.value instrValue →
    EvaluatesInstrs ctx instrs result (env ++ [(instr.name, instrValue)]) value →
    EvaluatesInstrs ctx (instr :: instrs) result env value

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

/-- An executable, sound comparison with one expected evaluation result. Concrete value families
  provide instances without requiring equality on every possible `Val`. -/
class EvalResultMatcher {primCtx : PrimitiveCtx} (expected : Val primCtx) where
  test : Val primCtx → Bool
  eq_of_test {actual : Val primCtx} : test actual = true → actual = expected

/-- Execute a normally returning block body and compare its result. The caller frame is omitted
  while computing; `EvaluatesCall.of_runCallBodyMatches` installs it by weakening. -/
def EvalState.callBodyResult? (name : String) (state : EvalState primCtx) : Option (Val primCtx) :=
  match state.control, state.stack with
  | .ret value, [] => some value
  | .exit target value, [] => if target = name then some value else none
  | _, _ => none

/-- Execute a block body and compare either its normal result or an exit targeting that block. -/
def EvalState.runCallBodyMatches (ctx : Ctx) (fuel : Nat) (name : String)
    (vargs : List (Val ctx.primCtx)) (expected : Val ctx.primCtx)
    [matcher : EvalResultMatcher expected] : Bool :=
  match ctx.blockCtx.get? name with
  | none => false
  | some block =>
      if vargs.length = block.params.length then
        match (EvalState.run ctx fuel
            (EvalState.enterInstrs block.instrs block.result
              (block.entryEnv vargs) [])).callBodyResult? name with
        | some actual => matcher.test actual
        | none => false
      else
        false

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

/-- Start a non-operator term, then continue from the resulting machine state. -/
theorem eval_step {ctx : Ctx} {term : Term ctx.primCtx} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} {next : EvalState ctx.primCtx}
    {value : Val ctx.primCtx}
    (hstep : EvalState.evalStep ctx term env stack = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx ⟨.eval term, env, stack⟩ value base :=
  EvaluatesFrom.step ((EvalState.step_eval ctx term env stack).trans hstep) hnext

/-- Start an operator through its three semantic phases, then continue from its result. -/
theorem op_step {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {oper : Op ctx.primCtx} {body : Op.Body ctx.primCtx} {next : EvalState ctx.primCtx}
    {value : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.body name args.length = some body)
    (hdrive : EvalState.driveOp body (Op.Arg.ofTerms args) env stack = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx ⟨.eval (.op name args), env, stack⟩ value base :=
  EvaluatesFrom.step (EvalState.step_op hop hbody hdrive) hnext

/-- Apply a value, then continue from the resulting machine state. -/
theorem apply_step {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {next : EvalState ctx.primCtx} {value : Val ctx.primCtx}
    (hstep : EvalState.applyValue ctx fn args env stack = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ value base :=
  EvaluatesFrom.step ((EvalState.step_apply ctx fn args env stack).trans hstep) hnext

/-- Resume exactly the top frame, then continue from the resulting machine state. -/
theorem ret_step {ctx : Ctx} {result : Val ctx.primCtx} {env : Env ctx.primCtx}
    {frame : Frame ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {next : EvalState ctx.primCtx} {value : Val ctx.primCtx}
    (hstep : EvalState.resumeFrame ctx frame result stack = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx ⟨.ret result, env, frame :: stack⟩ value base :=
  EvaluatesFrom.step ((EvalState.step_ret ctx result env frame stack).trans hstep) hnext

/-- Unwind exactly the top frame, then continue from the resulting machine state. -/
theorem exit_step {ctx : Ctx} {name : String} {result : Val ctx.primCtx}
    {env : Env ctx.primCtx} {frame : Frame ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} {next : EvalState ctx.primCtx}
    {value : Val ctx.primCtx}
    (hstep : EvalState.unwindFrame frame name result env stack = some next)
    (hnext : EvaluatesFrom ctx next value base) :
    EvaluatesFrom ctx ⟨.exit name result, env, frame :: stack⟩ value base :=
  EvaluatesFrom.step ((EvalState.step_exit ctx name result env frame stack).trans hstep) hnext

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

/-- A successful bounded run supplies an `EvaluatesFrom` witness for an arbitrary start state. -/
theorem EvaluatesFrom.of_run {ctx : Ctx} {state : EvalState ctx.primCtx}
    {value : Val ctx.primCtx} {fuel : Nat}
    (h : (EvalState.run ctx fuel state).result? = some value) :
    EvaluatesFrom ctx state value [] := by
  obtain ⟨steps, hsteps⟩ := EvalState.exists_stepN_run fuel state
  cases hstate : EvalState.run ctx fuel state with
  | mk control scope stack =>
      rw [hstate] at hsteps h
      cases control <;> cases stack <;> simp [EvalState.result?] at h
      subst h
      exact ⟨steps, scope, hsteps⟩

theorem EvaluatesFrom.of_evaluatesTo {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx}
    (h : EvaluatesTo ctx env term value) :
    EvaluatesFrom ctx (EvalState.start env term) value [] := by
  simpa [EvaluatesTo] using h

theorem EvaluatesTo.of_evaluatesFrom {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx}
    (h : EvaluatesFrom ctx (EvalState.start env term) value []) :
    EvaluatesTo ctx env term value := by
  simpa [EvaluatesTo] using h

/-- A successful bounded execution supplies the exact step witness used by `EvaluatesTo`.
  This is the bridge used when evaluation must compute and infer the result value. -/
theorem EvaluatesTo.of_run {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx} {fuel : Nat}
    (h : (EvalState.run ctx fuel (EvalState.start env term)).result? = some value) :
    EvaluatesTo ctx env term value := by
  exact EvaluatesTo.of_evaluatesFrom (EvaluatesFrom.of_run h)

theorem EvaluatesTo.iff_run {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {value : Val ctx.primCtx} :
    EvaluatesTo ctx env term value ↔
      ∃ fuel, (EvalState.run ctx fuel (EvalState.start env term)).result? = some value := by
  constructor
  · intro h
    obtain ⟨fuel, scope, hsteps⟩ := EvaluatesFrom.of_evaluatesTo h
    refine ⟨fuel, ?_⟩
    rw [EvalState.run_eq_of_stepN hsteps]
    rfl
  · rintro ⟨fuel, h⟩
    exact EvaluatesTo.of_run h

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

/-- A native execution of a closed block body proves the full call specification. The closed run
  is weakened beneath the caller frame, which then handles either a normal return or an exit
  targeting this call. -/
theorem of_runCallBodyMatches {ctx : Ctx} {name : String}
    {vargs : List (Val ctx.primCtx)} {value : Val ctx.primCtx} {fuel : Nat}
    [matcher : EvalResultMatcher value]
    (h : EvalState.runCallBodyMatches ctx fuel name vargs value = true) :
    EvaluatesCall ctx name vargs value := by
  unfold EvalState.runCallBodyMatches at h
  cases hblock : ctx.blockCtx.get? name with
  | none => simp [hblock] at h
  | some block =>
      by_cases hargs : vargs.length = block.params.length
      · let initial := EvalState.enterInstrs block.instrs block.result (block.entryEnv vargs) []
        cases hresult : (EvalState.run ctx fuel initial).callBodyResult? name with
        | none => simp [hblock, hargs, initial, hresult] at h
        | some actual =>
            have hmatch : matcher.test actual = true := by
              simpa [hblock, hargs, initial, hresult] using h
            have hvalue : actual = value := matcher.eq_of_test hmatch
            subst value
            obtain ⟨steps, hsteps⟩ := EvalState.exists_stepN_run fuel initial
            cases hrun : EvalState.run ctx fuel initial with
            | mk control scope stack =>
                rw [hrun] at hsteps hresult
                cases control <;> cases stack <;>
                  simp [EvalState.callBodyResult?] at hresult
                · rename_i returned
                  have hreturned : returned = actual := hresult
                  intro callerEnv base
                  let callStack : List (Frame ctx.primCtx) := .call name callerEnv :: base
                  let state := EvalState.enterInstrs block.instrs block.result
                    (block.entryEnv vargs) callStack
                  refine ⟨block, state, steps + 1, callerEnv, hblock, ?_, ?_⟩
                  · simp [state, callStack, EvalState.enterBlock, hargs]
                  · have hbodySteps : EvalState.stepN ctx steps state =
                        some ⟨.ret returned, scope, callStack⟩ := by
                      have hweaken := EvalState.stepN_weaken callStack hsteps
                      have hinitial : EvalState.appendStack initial callStack = state :=
                        EvalState.enterInstrs_appendStack block.instrs block.result
                          (block.entryEnv vargs) callStack
                      rw [← hinitial]
                      exact hweaken
                    rw [EvalState.stepN_add, hbodySteps]
                    simp [callStack, EvalState.stepN_succ, EvalState.step,
                      EvalState.resumeFrame, hreturned]
                · rename_i target returned
                  have htarget : target = name := hresult.1
                  have hreturned : returned = actual := hresult.2
                  intro callerEnv base
                  let callStack : List (Frame ctx.primCtx) := .call name callerEnv :: base
                  let state := EvalState.enterInstrs block.instrs block.result
                    (block.entryEnv vargs) callStack
                  refine ⟨block, state, steps + 1, callerEnv, hblock, ?_, ?_⟩
                  · simp [state, callStack, EvalState.enterBlock, hargs]
                  · have hbodySteps : EvalState.stepN ctx steps state =
                        some ⟨.exit target returned, scope, callStack⟩ := by
                      have hweaken := EvalState.stepN_weaken callStack hsteps
                      have hinitial : EvalState.appendStack initial callStack = state :=
                        EvalState.enterInstrs_appendStack block.instrs block.result
                          (block.entryEnv vargs) callStack
                      rw [← hinitial]
                      exact hweaken
                    rw [EvalState.stepN_add, hbodySteps]
                    simp [callStack, EvalState.stepN_succ, EvalState.step, EvalState.unwindFrame,
                      htarget, hreturned]
      · simp [hblock, hargs] at h

end EvaluatesCall

/-- Evaluation is deterministic, so the fuel is an artefact of the *proof*, not of the statement:
  a term has at most one value. This is what licenses reading `EvaluatesTo` as a function. -/
theorem EvaluatesTo.unique {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {v₁ v₂ : Val ctx.primCtx}
    (h₁ : EvaluatesTo ctx env term v₁) (h₂ : EvaluatesTo ctx env term v₂) : v₁ = v₂ := by
  have h₁' := EvaluatesFrom.of_evaluatesTo h₁
  have h₂' := EvaluatesFrom.of_evaluatesTo h₂
  obtain ⟨fuel₁, scope₁, hsteps₁⟩ := h₁'
  have htail := EvaluatesFrom.drop_prefix hsteps₁ h₂'
  exact (EvaluatesFrom.ret_empty_eq htail).symm

/-- Once a canonical evaluation is known, any other claimed result is exactly an equality with
  that result. This packages determinism for semantic reduction lemmas. -/
theorem EvaluatesTo.iff_eq_of {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {canonical expected : Val ctx.primCtx}
    (hcanonical : EvaluatesTo ctx env term canonical) :
    EvaluatesTo ctx env term expected ↔ canonical = expected := by
  constructor
  · exact fun h => EvaluatesTo.unique hcanonical h
  · rintro rfl
    exact hcanonical

/-- Transport a canonical evaluation result to an equal expected result. -/
theorem EvaluatesTo.of_eq {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {canonical expected : Val ctx.primCtx}
    (hcanonical : EvaluatesTo ctx env term canonical) (h : canonical = expected) :
    EvaluatesTo ctx env term expected :=
  (EvaluatesTo.iff_eq_of hcanonical).2 h

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
  obtain ⟨fuel, scope, hsteps⟩ := EvaluatesFrom.of_evaluatesTo h
  refine ⟨fuel, scope, ?_⟩
  simpa [EvalState.start, EvalState.appendStack] using
    (EvalState.stepN_weaken (base := base) hsteps)

/-- Install the machine continuations represented by `EvaluatesInstrs`. The relation itself can
  therefore be used as a block-level WP without repeatedly simplifying `enterInstrs`. -/
theorem EvaluatesInstrs.to_evaluatesFrom {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env callerEnv : Env ctx.primCtx}
    {value : Val ctx.primCtx} {name : String} {base : List (Frame ctx.primCtx)}
    (h : EvaluatesInstrs ctx instrs result env value) :
    EvaluatesFrom ctx
      (EvalState.enterInstrs instrs result env (.call name callerEnv :: base)) value base := by
  induction h with
  | nil hresult =>
      apply EvaluatesFrom.bind (EvaluatesTo.weaken hresult _)
      intro scope
      exact EvaluatesFrom.ret_step rfl EvaluatesFrom.done
  | @cons instr instrs result env instrValue value hinstr hrest ih =>
      apply EvaluatesFrom.bind (EvaluatesTo.weaken hinstr _)
      intro scope
      exact EvaluatesFrom.ret_step rfl ih

namespace EvaluatesCall

/-- A block lookup, arity check, and instruction-sequence WP suffice to prove a call spec. -/
theorem of_evaluatesInstrs {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : vargs.length = block.params.length)
    (hbody : EvaluatesInstrs ctx block.instrs block.result (block.entryEnv vargs) value) :
    EvaluatesCall ctx name vargs value := by
  apply of_evaluatesFrom
  intro callerEnv base
  refine ⟨block,
    EvalState.enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call name callerEnv :: base), hblock, ?_, hbody.to_evaluatesFrom⟩
  simp [EvalState.enterBlock, hargs]

/-- Transport a call specification from its canonical result to an equal expected result. -/
theorem of_eq {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {canonical value : Val ctx.primCtx}
    (hcall : EvaluatesCall ctx name vargs canonical) (hvalue : canonical = value) :
    EvaluatesCall ctx name vargs value := by
  rwa [hvalue] at hcall

end EvaluatesCall


/-! ### the calculus, on the machine

  These replace the corresponding equations of the old big-step evaluator. Small-step exposes
  the intermediate states needed by the compositional proof rules below.

  Each rule here is proved by stepping the machine, so it is `propext, Quot.sound` only, where
  the big-step versions inherit `Classical.choice` from the fixpoint. -/

theorem EvaluatesTo.prim (ty : Ty) (val : Ty.type ctx.primCtx ty) :
    EvaluatesTo ctx env (.prim ty val) (Val.mk ty val) :=
  ⟨1, env, rfl⟩

/-- A name resolves to a local binding if there is one, and otherwise to the block of that name
  as a value -- which is why this needs `name` not to be a block. The `←` direction holds
  unconditionally, since a local binding shadows a block. -/
theorem EvaluatesTo.var_iff {name : String} {v : Val ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = none) :
    EvaluatesTo ctx env (.var name) v ↔ Scope.get? env name = some v := by
  constructor
  · intro h
    cases hv : Scope.get? env name with
    | none =>
        have hstuck : EvalState.step ctx (EvalState.start env (.var name)) = none := by
          simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, hv, hblock]
        obtain ⟨fuel, scope, hsteps⟩ := EvaluatesFrom.of_evaluatesTo h
        cases fuel with
        | zero => simp [EvalState.start] at hsteps
        | succ fuel => rw [EvalState.stepN_succ, hstuck] at hsteps; simp at hsteps
    | some w =>
        have hstep : EvalState.step ctx (EvalState.start env (.var name))
            = some ⟨.ret w, env, []⟩ := by simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, hv]
        have hw : EvaluatesTo ctx env (.var name) w :=
          EvaluatesTo.of_evaluatesFrom (EvaluatesFrom.step hstep
            (EvaluatesFrom.done (ctx := ctx) (value := w) (scope := env) (base := [])))
        have heq : v = w := EvaluatesTo.unique h hw
        simpa [heq] using hv
  · intro hv
    apply EvaluatesTo.of_evaluatesFrom
    exact EvaluatesFrom.step (by
      simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame,
        EvalState.unwindFrame, EvalState.start, hv])
      (EvaluatesFrom.done (ctx := ctx) (value := v) (scope := env) (base := []))

/-- A local binding evaluates directly, independently of whether a block has the same name. -/
@[eval_semantic] theorem EvaluatesTo.var_local {ctx : Ctx} {env : Env ctx.primCtx}
    {name : String} {v : Val ctx.primCtx}
    (hlocal : Scope.get? env name = some v) :
    EvaluatesTo ctx env (.var name) v := by
  apply EvaluatesTo.of_evaluatesFrom
  exact EvaluatesFrom.step (by
    simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame,
      EvalState.unwindFrame, EvalState.start, hlocal])
    (EvaluatesFrom.done (ctx := ctx) (value := v) (scope := env) (base := []))

/-- A block named where a value is expected evaluates to a reference to it. This is what makes
  `call f [x]` and `app (var f) [x]` agree. -/
theorem EvaluatesTo.var_block {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {block : Block ctx.primCtx}
    (hlocal : Scope.get? env name = none) (hblock : ctx.blockCtx.get? name = some block) :
    EvaluatesTo ctx env (.var name)
      (.blockRef name (block.params.map Prod.snd) block.outTy) := by
  apply EvaluatesTo.of_evaluatesFrom
  exact EvaluatesFrom.step (by
    simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame,
      EvalState.unwindFrame, EvalState.start, hlocal, hblock])
    (EvaluatesFrom.done (ctx := ctx)
      (value := .blockRef name (block.params.map Prod.snd) block.outTy)
      (scope := env) (base := []))

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
    ∃ state, EvalState.driveOp body (Op.Arg.ofTerms terms) env S = some state ∧
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
                  exact ⟨state, by simpa [EvalState.driveOp, Op.Arg.ofTerms] using hdrive, hfrom⟩
              | true =>
                  have hbody' : (resume (some termValue)).applyVals termValues = some result := by
                    simpa [Op.Body.applyVals] using hbody
                  obtain ⟨state, hdrive, hfrom⟩ :=
                    ih (body := resume (some termValue)) (values := termValues) (S := S)
                      hterms hbody'
                  obtain ⟨fuel, scope, htermSteps⟩ :=
                    EvaluatesTo.weaken hterm (.opBody resume (Op.Arg.ofTerms terms) env :: S)
                  have hretStep : EvalState.step ctx
                      ⟨.ret termValue, scope, .opBody resume (Op.Arg.ofTerms terms) env :: S⟩ =
                        some state := by
                    simpa [EvalState.step, hdrive]
                  exact ⟨⟨.eval term, env, .opBody resume (Op.Arg.ofTerms terms) env :: S⟩,
                    by simp [EvalState.driveOp, Op.Arg.ofTerms],
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

namespace EvaluatesInstrs

/-- Consume a call-valued instruction and continue under the value supplied by its specification.
  Keeping the tail in this rule prevents automation from exposing it before `hcall` fixes the
  instruction's result. -/
theorem cons_call {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {vargs : List (Val ctx.primCtx)} {instrName : String}
    {instrs : List (Instr ctx.primCtx)} {result : Term ctx.primCtx}
    {env : Env ctx.primCtx} {instrValue value : Val ctx.primCtx}
    (hcall : EvaluatesCall ctx name vargs instrValue)
    (hargs : EvaluatesToAll ctx env args vargs)
    (hrest : EvaluatesInstrs ctx instrs result
      (env ++ [(instrName, instrValue)]) value) :
    EvaluatesInstrs ctx (Instr.ofTerm instrName (.call name args) :: instrs)
      result env value := by
  obtain ⟨block, _, _, _, hblock, _, _⟩ := hcall env []
  exact .cons (EvaluatesTo.call hcall hblock hargs) hrest

end EvaluatesInstrs


end Zag
