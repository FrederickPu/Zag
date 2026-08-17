import Zag.EvalState

/-!
# The loop rule

`tail_induction` proves a specification of a block that calls itself. A loop written as a control
*instruction* never makes a call -- re-entry comes from `Frame.control` -- so this is its
counterpart: an invariant indexed by the iteration, plus an explicit iteration count for
termination. The argument for that shape is in `HANDOFF.md`.
-/

namespace Zag

/-! ### loops

  `tail_induction` proves a specification of a block that calls itself. A loop written as a
  control *instruction* never makes a call -- re-entry comes from `Frame.control`, not from a
  term -- so nothing there applies to it. These are its counterpart.

  The invariant `I` is indexed by the *iteration*, and stated over the phi values, which is where
  a loop's state lives. Termination is the separate hypothesis `N`: the iteration at which the
  condition stops the loop. It is deliberately *not* a decreasing measure -- keeping progress and
  termination apart is the whole reason this rule exists rather than a well-founded recursion.

  A loop may carry several variables. A block returns one value, so one turn runs one block per
  variable: role `0` is the condition and role `k+1` computes the new value of variable `k`. The
  rule is stated over an arbitrary control, described by equations on its `next`, subject to one
  structural assumption -- that the control asks for role `p` while sitting at phase `p`, so a
  phase names the block that is running. `whileControl` satisfies it and so would `for`. -/

/-- One turn's body sweep: `m` bodies still to run, the control parked at `phase` with state
  `args`, and role `phase`'s block running. `P` is what must hold where the sweep lands.

  A recursive `def` rather than an inductive, so that a concrete arity unfolds under `simp` into
  exactly `m` obligations, one per loop variable. -/
def BodySweep (ctx : Ctx) (ctrl : Control ctx.primCtx) (blockNames : List String)
    (P : Nat → List (Val ctx.primCtx) → Prop) :
    Nat → Nat → List (Val ctx.primCtx) → Prop
| 0, phase, args => P phase args
| m + 1, phase, args =>
    ∃ bodyName value phase' args',
      blockNames[phase]? = some bodyName ∧
      EvaluatesCall ctx bodyName args value ∧
      ctrl.next phase args value = some (phase', .call phase' args') ∧
      BodySweep ctx ctrl blockNames P m phase' args'

open EvalState in
/-- Running the sweep: each body in turn, then the landing state handed to `cont`. -/
private theorem EvaluatesFrom.sweep_run {ctx : Ctx} {ctrl : Control ctx.primCtx}
    {controlName : String} {blockNames : List String}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {Q : List (Val ctx.primCtx) → Prop} {final : Val ctx.primCtx}
    (hctrl : Scope.get? ctx.controlCtx controlName = some ctrl)
    (cont : ∀ args, Q args → ∃ st,
      driveControl ctx controlName 0 (.call 0 args) blockNames env stack
        = some st ∧ EvaluatesFrom ctx st final base) :
    ∀ m phase args,
      BodySweep ctx ctrl blockNames (fun p a => p = 0 ∧ Q a) m phase args →
      ∃ st, driveControl ctx controlName phase (.call phase args) blockNames env stack = some st ∧ EvaluatesFrom ctx st final base := by
  intro m
  induction m with
  | zero =>
      intro phase args hsweep
      obtain ⟨rfl, hQ⟩ := hsweep
      exact cont args hQ
  | succ m ih =>
      intro phase args hsweep
      obtain ⟨bodyName, value, phase', args', hrole, hcall, hnext, hrest⟩ := hsweep
      obtain ⟨bodyBlock, st, fuel, scope, hblk, henter, hsteps⟩ :=
        hcall env (.control controlName phase blockNames args env :: stack)
      obtain ⟨st', hdrive', hfrom'⟩ := ih phase' args' hrest
      have hstep : EvalState.step ctx
          ⟨.ret value, scope,
            .control controlName phase blockNames args env :: stack⟩
            = some st' := by
        simp only [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hctrl, hnext]
        exact hdrive'
      exact ⟨st, by simp only [EvalState.driveControl, hrole, hblk]; exact henter,
        EvaluatesFrom.trans_stepN hsteps (EvaluatesFrom.step hstep hfrom')⟩

open EvalState in
/-- One turn of the loop, and then the rest of it. Induction is on `k`, the iterations still to
  come, so that the invariant is carried forwards while the recursion runs backwards from `N`. -/
private theorem EvaluatesFrom.control_loop_aux {ctx : Ctx} {ctrl : Control ctx.primCtx}
    {controlName condName : String} {blockNames : List String}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N bodies : Nat}
    {loopResult final : Val ctx.primCtx}
    (hctrl : Scope.get? ctx.controlCtx controlName = some ctrl)
    (hcondRole : blockNames[0]? = some condName)
    (round : ∀ n args, n < N → I n args → ∃ w,
      EvaluatesCall ctx condName args w ∧
      ctrl.next 0 args w = some (1, .call 1 args) ∧
      BodySweep ctx ctrl blockNames (fun p a => p = 0 ∧ I (n + 1) a) bodies 1 args)
    (stop : ∀ args, I N args → ∃ w,
      EvaluatesCall ctx condName args w ∧
      ctrl.next 0 args w = some (0, .done loopResult))
    (cont : EvaluatesFrom ctx ⟨.ret loopResult, env, stack⟩ final base) :
    ∀ k n args, n + k = N → I n args →
      ∃ st, driveControl ctx controlName 0 (.call 0 args) blockNames env stack = some st ∧ EvaluatesFrom ctx st final base := by
  intro k
  induction k with
  | zero =>
      intro n args hk hI
      subst_vars
      obtain ⟨w, hcondCall, hnext⟩ := stop args (by simpa using hI)
      obtain ⟨condBlock, st, fuel, scope, hblk, henter, hsteps⟩ :=
        hcondCall env (.control controlName 0 blockNames args env :: stack)
      refine ⟨st, by simp only [EvalState.driveControl, hcondRole, hblk]; exact henter, ?_⟩
      refine EvaluatesFrom.trans_stepN hsteps (EvaluatesFrom.step ?_ cont)
      simp only [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hctrl, hnext, EvalState.driveControl]
  | succ k ih =>
      intro n args hk hI
      obtain ⟨w, hcondCall, hnext, hsweep⟩ := round n args (by omega) hI
      obtain ⟨condBlock, st, fuel, scope, hblk, henter, hsteps⟩ :=
        hcondCall env (.control controlName 0 blockNames args env :: stack)
      -- the sweep lands on a state the next iteration's hypothesis accepts
      obtain ⟨st', hdrive', hfrom'⟩ :=
        EvaluatesFrom.sweep_run hctrl (fun a hI' => ih (n + 1) a (by omega) hI') bodies 1 args
          hsweep
      -- leaving `cond`, the control asks for the first body on the same phi
      have hintoBody : EvalState.step ctx
          ⟨.ret w, scope,
            .control controlName 0 blockNames args env :: stack⟩
            = some st' := by
        simp only [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hctrl, hnext]
        exact hdrive'
      exact ⟨st, by simp only [EvalState.driveControl, hcondRole, hblk]; exact henter,
        EvaluatesFrom.trans_stepN hsteps (EvaluatesFrom.step hintoBody hfrom')⟩

open EvalState in
/-- A loop, from the point where its last initial phi value has just been produced.

  This is the state proof automation reaches on its own: the control instruction's arguments are
  ordinary terms, so the machine evaluates them one at a time under a `Frame.controlArgs`, and
  the moment the last one lands the control takes over. Everything after that -- entering `cond`,
  coming back, sweeping the bodies, coming back -- is what this rule replaces. -/
theorem EvaluatesFrom.control_loop {ctx : Ctx} {ctrl : Control ctx.primCtx}
    {controlName condName : String} {blockNames : List String}
    {env scope : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {done : List (Val ctx.primCtx)} {v : Val ctx.primCtx}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N bodies : Nat}
    {loopResult final : Val ctx.primCtx}
    (hctrl : Scope.get? ctx.controlCtx controlName = some ctrl)
    (hcondRole : blockNames[0]? = some condName)
    (hinit : ctrl.init (done ++ [v]) = some (0, .call 0 (done ++ [v])))
    (init : I 0 (done ++ [v]))
    (round : ∀ n args, n < N → I n args → ∃ w,
      EvaluatesCall ctx condName args w ∧
      ctrl.next 0 args w = some (1, .call 1 args) ∧
      BodySweep ctx ctrl blockNames (fun p a => p = 0 ∧ I (n + 1) a) bodies 1 args)
    (stop : ∀ args, I N args → ∃ w,
      EvaluatesCall ctx condName args w ∧
      ctrl.next 0 args w = some (0, .done loopResult))
    (cont : EvaluatesFrom ctx ⟨.ret loopResult, env, stack⟩ final base) :
    EvaluatesFrom ctx
      ⟨.ret v, scope,
        .args (.control controlName blockNames) done [] env :: stack⟩
      final base := by
  obtain ⟨st, hdrive, hfrom⟩ :=
    EvaluatesFrom.control_loop_aux (bodies := bodies) hctrl hcondRole round stop cont
      N 0 (done ++ [v]) (Nat.zero_add N) init
  refine EvaluatesFrom.step ?_ hfrom
  simp only [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, hctrl, hinit]
  exact hdrive


end Zag
