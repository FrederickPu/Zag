import Zag.EvalState
import Zag.Refinement

/-!
# Continuation-passing operator loops

An operator can ask the machine to apply a value and resume its body with the answer. In
particular, applying an `opRef` restarts the named operator on its captured values followed by the
new arguments. This file gives that machine action a compositional specification and records how
the answer returns through either kind of operator frame.
-/

namespace Zag

namespace EvalState

/- Feeding a collected value list reaches the continuation built from exactly those values. -/
theorem driveOpVals_collect {ctx : Ctx} (finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx)
    (vals acc : List (Val ctx.primCtx)) {remaining : Nat} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} (hlen : vals.length = remaining) :
    driveOpVals (Op.Body.collect finish remaining acc) vals env stack =
      driveOpVals (finish (acc ++ vals)) [] env stack := by
  induction vals generalizing remaining acc with
  | nil =>
      simp at hlen
      subst remaining
      simp [Op.Body.collect]
  | cons value vals ih =>
      cases remaining with
      | zero => simp at hlen
      | succ remaining =>
          have hlen' : vals.length = remaining := by simpa using hlen
          rw [Op.Body.collect, driveOpVals]
          simpa [List.append_assoc] using ih (remaining := remaining) (acc := acc ++ [value]) hlen'

end EvalState

/-- Applying `fn` to already-evaluated arguments produces `value`, independently of the caller's
environment and pending stack. Quantifying over both is what makes the specification usable for
an application made from inside an operator body. -/
def EvaluatesApply (ctx : Ctx) (fn : Val ctx.primCtx) (args : List (Val ctx.primCtx))
    (value : Val ctx.primCtx) : Prop :=
  ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
    EvaluatesFrom ctx ⟨.apply fn args, env, base⟩ value base

namespace EvaluatesApply

/-- Establish an application specification directly from `applyValue` and the computation it
starts. -/
theorem of_applyValue {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx}
    (h : ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
      ∃ state, EvalState.applyValue ctx fn args env base = some state ∧
        EvaluatesFrom ctx state value base) :
    EvaluatesApply ctx fn args value := by
  intro env base
  obtain ⟨state, happly, hfrom⟩ := h env base
  exact EvaluatesFrom.step (by simpa [EvalState.step] using happly) hfrom

/-- An `EvaluatesCall` specification is also a specification of applying the corresponding block
reference. The type annotation carried by the reference does not affect machine execution. -/
theorem blockRef {ctx : Ctx} {name : String} {args : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {argTys : List Ty} {outTy : Ty}
    (hcall : EvaluatesCall ctx name args value) :
    EvaluatesApply ctx (.blockRef name argTys outTy) args value := by
  intro env base
  obtain ⟨block, state, fuel, scope, hblock, henter, hsteps⟩ := hcall env base
  refine EvaluatesFrom.step ?_ ⟨fuel, scope, hsteps⟩
  simp [EvalState.step, EvalState.applyValue, hblock, henter]

/-- Applying an operator reference starts the body selected by the named operator. The premise is
deliberately relational rather than `Op.Body.applyVals`: a body containing `.apply` needs the
machine and cannot be interpreted by the pure helper. -/
theorem opRef {ctx : Ctx} {name : String} {captured args : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {oper : Op ctx.primCtx} {body : Op.Body ctx.primCtx}
    {value : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.body name (captured.length + args.length) = some body)
    (hrun : ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
      ∃ state, EvalState.driveOpVals body (captured ++ args) env base = some state ∧
        EvaluatesFrom ctx state value base) :
    EvaluatesApply ctx (.opRef name captured argTys outTy) args value := by
  apply of_applyValue
  intro env base
  obtain ⟨state, hdrive, hfrom⟩ := hrun env base
  exact ⟨state, by simp [EvalState.applyValue, hop, hbody, hdrive], hfrom⟩

/-- Finite induction for a continuation-passing loop. A running iteration receives the semantic
specification of every invariant-preserving next application as its continuation hypothesis.
Unlike a tail-call rule, `round` may use that hypothesis under operator and call frames, so the
recursive answer is allowed to return through the current iteration. -/
theorem loop {ctx : Ctx} {fn : Val ctx.primCtx} {I : Nat → List (Val ctx.primCtx) → Prop}
    {N : Nat} {result : Val ctx.primCtx} {initial : List (Val ctx.primCtx)}
    (init : I 0 initial)
    (round : ∀ n args, n < N → I n args →
      (∀ nextArgs, I (n + 1) nextArgs → EvaluatesApply ctx fn nextArgs result) →
      EvaluatesApply ctx fn args result)
    (stop : ∀ args, I N args → EvaluatesApply ctx fn args result) :
    EvaluatesApply ctx fn initial result := by
  have aux : ∀ k n args, n + k = N → I n args → EvaluatesApply ctx fn args result := by
    intro k
    induction k with
    | zero =>
        intro n args hn hI
        have : n = N := by omega
        subst n
        exact stop args hI
    | succ k ih =>
        intro n args hn hI
        apply round n args (by omega) hI
        intro nextArgs hnext
        exact ih (n + 1) nextArgs (by omega) hnext
  exact aux N 0 initial (Nat.zero_add N) init

end EvaluatesApply

namespace EvaluatesFrom

/-- Evaluate a term with pending frames and then continue from the value it returns. -/
theorem eval_then {ctx : Ctx} {term : Term ctx.primCtx} {value final : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    (heval : EvaluatesTo ctx env term value)
    (hcont : ∀ scope, EvaluatesFrom ctx ⟨.ret value, scope, stack⟩ final base) :
    EvaluatesFrom ctx ⟨.eval term, env, stack⟩ final base :=
  EvaluatesFrom.bind (EvaluatesTo.weaken heval stack) hcont

/-- Evaluate and collect term operands, then continue from the body built from their values. -/
theorem driveOp_collect {ctx : Ctx}
    (finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx)
    {terms : List (Term ctx.primCtx)} {values acc : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {result : Val ctx.primCtx}
    (hargs : EvaluatesToAll ctx env terms values)
    (hfinish : ∃ state,
      EvalState.driveOp (finish (acc ++ values)) [] env stack = some state ∧
        EvaluatesFrom ctx state result base) :
    ∃ state,
      EvalState.driveOp (Op.Body.collect finish values.length acc) terms env stack = some state ∧
        EvaluatesFrom ctx state result base := by
  induction hargs generalizing acc stack with
  | nil => simpa [Op.Body.collect] using hfinish
  | @cons term terms value values hterm hterms ih =>
      obtain ⟨state, hdrive, hfrom⟩ := ih (acc := acc ++ [value]) (stack := stack) (by
        simpa [List.append_assoc] using hfinish)
      let resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
        | some value => Op.Body.collect finish values.length (acc ++ [value])
        | none => .fail
      obtain ⟨fuel, scope, hsteps⟩ :=
        EvaluatesTo.weaken hterm (.opBody resume terms env :: stack)
      have hret : EvalState.step ctx
          ⟨.ret value, scope, .opBody resume terms env :: stack⟩ = some state := by
        simpa [EvalState.step, EvalState.resumeFrame, resume] using hdrive
      refine ⟨⟨.eval term, env, .opBody resume terms env :: stack⟩, ?_,
        EvaluatesFrom.trans_stepN hsteps (EvaluatesFrom.step hret hfrom)⟩
      simp [EvalState.driveOp, Op.Body.collect, resume]
      funext input
      cases input <;> rfl

/-- Run an application and then continue from the value it returns. -/
theorem apply_then {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {value final : Val ctx.primCtx} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)}
    (happly : EvaluatesApply ctx fn args value)
    (hcont : ∀ scope, EvaluatesFrom ctx ⟨.ret value, scope, stack⟩ final base) :
    EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ final base :=
  EvaluatesFrom.bind (happly env stack) hcont

/-- An application made by a term-driven operator returns through its `opBody` frame and resumes
the suspended body. -/
theorem apply_opBody {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {value final : Val ctx.primCtx} {env frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {rest : List (Term ctx.primCtx)} {stack base : List (Frame ctx.primCtx)}
    {state : EvalState ctx.primCtx}
    (happly : EvaluatesApply ctx fn args value)
    (hdrive : EvalState.driveOp (resume (some value)) rest frameEnv stack = some state)
    (hfrom : EvaluatesFrom ctx state final base) :
    EvaluatesFrom ctx
      ⟨.apply fn args, env, .opBody resume rest frameEnv :: stack⟩ final base := by
  apply EvaluatesFrom.apply_then happly
  intro scope
  exact EvaluatesFrom.step
    (by simp [EvalState.step, EvalState.resumeFrame, hdrive]) hfrom

/-- An application made by a value-driven operator returns through its `opBodyVals` frame and
resumes the suspended body. This is the frame used after applying an `opRef`. -/
theorem apply_opBodyVals {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {value final : Val ctx.primCtx}
    {env frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {rest : List (Val ctx.primCtx)} {stack base : List (Frame ctx.primCtx)}
    {state : EvalState ctx.primCtx}
    (happly : EvaluatesApply ctx fn args value)
    (hdrive : EvalState.driveOpVals (resume (some value)) rest frameEnv stack = some state)
    (hfrom : EvaluatesFrom ctx state final base) :
    EvaluatesFrom ctx
      ⟨.apply fn args, env, .opBodyVals resume rest frameEnv :: stack⟩ final base := by
  apply EvaluatesFrom.apply_then happly
  intro scope
  exact EvaluatesFrom.step
    (by simp [EvalState.step, EvalState.resumeFrame, hdrive]) hfrom

/-- Execute an `.apply` node reached by `driveOp`, including the return through the frame that the
driver installs. -/
theorem driveOp_apply {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {resume : Val ctx.primCtx → Op.Body ctx.primCtx} {operands : List (Term ctx.primCtx)}
    {value final : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {state : EvalState ctx.primCtx}
    (happly : EvaluatesApply ctx fn args value)
    (hdrive : EvalState.driveOp (resume value) operands env stack = some state)
    (hfrom : EvaluatesFrom ctx state final base) :
    ∃ start, EvalState.driveOp (.apply fn args resume) operands env stack = some start ∧
      EvaluatesFrom ctx start final base := by
  let k : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
    | some result => resume result
    | none => .fail
  refine ⟨⟨.apply fn args, env, .opBody k operands env :: stack⟩, ?_, ?_⟩
  · simp [EvalState.driveOp, k]
    funext input
    cases input <;> rfl
  · exact EvaluatesFrom.apply_opBody happly (by simpa [k] using hdrive) hfrom

/-- Execute an `.apply` node reached by `driveOpVals`. This is the composition rule used when a
restarted operator calls another continuation and then returns its answer. -/
theorem driveOpVals_apply {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {resume : Val ctx.primCtx → Op.Body ctx.primCtx}
    {operands : List (Val ctx.primCtx)} {value final : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {state : EvalState ctx.primCtx}
    (happly : EvaluatesApply ctx fn args value)
    (hdrive : EvalState.driveOpVals (resume value) operands env stack = some state)
    (hfrom : EvaluatesFrom ctx state final base) :
    ∃ start, EvalState.driveOpVals (.apply fn args resume) operands env stack = some start ∧
      EvaluatesFrom ctx start final base := by
  let k : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
    | some result => resume result
    | none => .fail
  refine ⟨⟨.apply fn args, env, .opBodyVals k operands env :: stack⟩, ?_, ?_⟩
  · simp [EvalState.driveOpVals, k]
    funext input
    cases input <;> rfl
  · exact EvaluatesFrom.apply_opBodyVals happly (by simpa [k] using hdrive) hfrom

end EvaluatesFrom

namespace PropRefinement

/-- Lift a refinement for evaluating a term through a pending machine continuation. -/
def evalThen {ctx : Ctx} {term : Term ctx.primCtx} {value final : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    (refinement : PropRefinement (EvaluatesTo ctx env term value))
    (hcont : ∀ scope, EvaluatesFrom ctx ⟨.ret value, scope, stack⟩ final base) :
    PropRefinement (EvaluatesFrom ctx ⟨.eval term, env, stack⟩ final base) where
  goals := refinement.goals
  prove := fun proveSubgoals =>
    EvaluatesFrom.eval_then (refinement.prove proveSubgoals) hcont

end PropRefinement

/-- An ordinary operator whose body collects all operands can use a relational continuation after
the collected values have been produced. -/
theorem EvaluatesTo.op_collect {ctx : Ctx} {env : Env ctx.primCtx}
    {name : String} {terms : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    {oper : Op ctx.primCtx} {finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {result : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.body name values.length = some (Op.Body.collect finish values.length []))
    (hargs : EvaluatesToAll ctx env terms values)
    (hfinish : ∃ state, EvalState.driveOp (finish values) [] env [] = some state ∧
      EvaluatesFrom ctx state result []) :
    EvaluatesTo ctx env (.op name terms) result := by
  have hargsLen := EvaluatesToAll.length_eq hargs
  obtain ⟨state, hdrive, hfrom⟩ :=
    EvaluatesFrom.driveOp_collect (acc := []) finish hargs (by simpa using hfinish)
  exact EvaluatesTo.of_evaluatesFrom
    (EvaluatesFrom.step (by
      simp [EvalState.step, EvalState.evalStep, EvalState.start, hop, hargsLen, hbody, hdrive]) hfrom)

end Zag
