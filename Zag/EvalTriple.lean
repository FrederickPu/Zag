import Zag.Machine
import Batteries.Control.OptionT

/-!
# Generic monadic evaluator triples

This module is a migration-safe total-correctness core for the machine. It only
observes `Machine.step`; in particular, it does not define evaluation by a shared fuel bound.
A derivation is a finite proof tree.  A step rules out the `OptionT` failure used for machine
stuckness, while retaining the ambient monad's exception conditions unchanged.
-/

namespace Std.Do

instance instWPPredTrans {ps : PostShape} : WP (PredTrans ps) ps where
  wp x := x

instance instWPMonadPredTrans {ps : PostShape} : WPMonad (PredTrans ps) ps where
  wp_pure _ := rfl
  wp_bind _ _ := rfl

end Std.Do

namespace Zag

namespace EvalTriple

open scoped Std.Do

/-- User-facing total view of a partial relation. `none` is an ordinary return used when the
relation has no result. -/
def total? {α : Type} (R : α → Prop) : Std.Do.PredTrans .pure (Option α) where
  trans Q := Std.Do.SPred.pure
    ((∀ value, R value → (Q.1 (some value)).down) ∧
      ((∀ value, ¬ R value) → (Q.1 none).down))
  conjunctiveRaw := by
    intro Q₁ Q₂
    dsimp [Std.Do.PredTrans.apply, Std.Do.SPred.bientails, Std.Do.SPred.and]
    constructor
    · intro h
      exact ⟨⟨fun value hvalue => (h.1 value hvalue).1,
          fun hnone => (h.2 hnone).1⟩,
        ⟨fun value hvalue => (h.1 value hvalue).2,
          fun hnone => (h.2 hnone).2⟩⟩
    · intro h
      exact ⟨fun value hvalue => ⟨h.1.1 value hvalue, h.2.1 value hvalue⟩,
        fun hnone => ⟨h.1.2 hnone, h.2.2 hnone⟩⟩

def somePost {α : Type} (success : α → Std.Do.Assertion .pure) :
    Std.Do.PostCond (Option α) .pure :=
  Std.Do.PostCond.noThrow fun
    | some value => success value
    | none => Std.Do.SPred.pure False

def someEqPost {α : Type} (expected : α) : Std.Do.PostCond (Option α) .pure :=
  somePost fun actual => Std.Do.SPred.pure (actual = expected)

@[simp] theorem somePost_some {α : Type} (success : α → Std.Do.Assertion .pure)
    (value : α) : (somePost success).1 (some value) = success value := rfl

@[simp] theorem somePost_none {α : Type} (success : α → Std.Do.Assertion .pure) :
    (somePost success).1 none = Std.Do.SPred.pure False := rfl

@[simp] theorem someEqPost_some {α : Type} (expected actual : α) :
    (someEqPost expected).1 (some actual) = Std.Do.SPred.pure (actual = expected) := rfl

@[simp] theorem someEqPost_none {α : Type} (expected : α) :
    (someEqPost expected).1 none = Std.Do.SPred.pure False := rfl

theorem total?_some_of_wp {α : Type} {R : α → Prop}
    {success : α → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (total? R)).apply (somePost success)).down) :
    ∃ value, R value ∧ (success value).down := by
  change ((∀ value, R value → ((somePost success).1 (some value)).down) ∧
    ((∀ value, ¬ R value) → ((somePost success).1 none).down)) at h
  by_cases hexists : ∃ value, R value
  · obtain ⟨value, hvalue⟩ := hexists
    exact ⟨value, hvalue, h.1 value hvalue⟩
  · exact (h.2 (fun value hvalue => hexists ⟨value, hvalue⟩)).elim

abbrev Assertion (ctx : Ctx) := Std.Do.Assertion ctx.postShape

abbrev PostCond (ctx : Ctx) (α : Type) := Std.Do.PostCond α ctx.postShape

abbrev ExceptConds (ctx : Ctx) := Std.Do.ExceptConds ctx.postShape

/-- The assertion assigned to an impossible machine-stuck result. -/
def Stuck (ctx : Ctx) : Assertion ctx :=
  Std.Do.SPred.pure False

/-- Restrict an assertion to one statically known machine state. -/
def At (ctx : Ctx) (expected actual : Machine.Config ctx.primCtx) (P : Assertion ctx) :
    Assertion ctx :=
  spred(⌜actual = expected⌝ ∧ P)

/-- The postcondition for one machine step. `none` is machine stuckness, not an ambient
exception, and is therefore impossible. -/
def StepPost (ctx : Ctx) (next : Machine.Config ctx.primCtx → Assertion ctx)
    (exceptional : ExceptConds ctx) : PostCond ctx (Option (Machine.Config ctx.primCtx)) :=
  (fun
    | none => Stuck ctx
    | some state => next state,
    exceptional)

/-- The postcondition required of an ambient operator action. Returning `none` is machine
stuckness; ambient exceptions retain the judgment's exception condition. -/
def ActionPost (ctx : Ctx) (next : Val ctx.primCtx → Assertion ctx)
    (exceptional : ExceptConds ctx) : PostCond ctx (Option (Val ctx.primCtx)) :=
  (fun
    | none => Stuck ctx
    | some value => next value,
   exceptional)

/-- A finite, possibly logically branching derivation made solely from monadic machine steps.
`Done` describes the permitted leaves and may inspect both the final machine state and the
assertion established there. -/
inductive Steps (ctx : Ctx) (exceptional : ExceptConds ctx)
    (Done : Machine.Config ctx.primCtx → Assertion ctx → Prop) :
    Machine.Config ctx.primCtx → Assertion ctx → Prop where
| done {state P} (h : Done state P) : Steps ctx exceptional Done state P
| step {state P} (next : Machine.Config ctx.primCtx → Assertion ctx)
    (head : Std.Do.Triple (Machine.step ctx state).run P
      (StepPost ctx next exceptional))
    (tail : ∀ nextState, Steps ctx exceptional Done nextState (next nextState)) :
    Steps ctx exceptional Done state P
| split {ι : Type} {state P} (cases : ι → Assertion ctx)
    (cover : P ⊢ₛ spred(∃ i, cases i))
    (branches : ∀ i, Steps ctx exceptional Done state (cases i)) :
    Steps ctx exceptional Done state P
| subst {state state' P I}
    (eq_state : P ⊢ₛ spred(⌜state = state'⌝))
    (hpre : P ⊢ₛ I)
    (next : Steps ctx exceptional Done state' I) :
    Steps ctx exceptional Done state P

namespace Steps

/-- Consequence for a derivation. The leaf transformer makes the rule useful for arbitrary
terminal judgments, not just evaluator returns. -/
theorem consequence {ctx : Ctx} {E E' : ExceptConds ctx}
    {Done Done' : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state : Machine.Config ctx.primCtx} {P P' : Assertion ctx}
    (h : Steps ctx E Done state P) (hpre : P' ⊢ₛ P) (hE : E ⊢ₑ E')
    (hDone : ∀ {state P P'}, (hpre : P' ⊢ₛ P) →
      (hdone : Done state P) → Done' state P') :
    Steps ctx E' Done' state P' := by
  induction h generalizing P' with
  | done h => exact .done (hDone hpre h)
  | step next head tail ih =>
      apply Steps.step next
      · exact Std.Do.Triple.iff_conseq.mp head hpre
          ⟨fun value => by cases value <;> rfl, hE⟩
      · intro nextState
        exact ih nextState .rfl
  | split cases cover branches ih =>
      exact .split cases (hpre.trans cover) fun i => ih i .rfl
  | subst eq_state hnext next ih =>
      exact .subst (hpre.trans eq_state) (hpre.trans hnext) (ih .rfl)

/-- Replace the terminal judgment without changing preconditions or ambient exceptions. -/
theorem mapDone {ctx : Ctx} {E : ExceptConds ctx}
    {Done Done' : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (h : Steps ctx E Done state P)
    (f : ∀ {state P}, (h : Done state P) → Done' state P) :
    Steps ctx E Done' state P := by
  induction h with
  | done h => exact .done (f h)
  | step cases head tail ih => exact .step cases head ih
  | split cases cover branches ih => exact .split cases cover ih
  | subst eq_state hpre next ih => exact .subst eq_state hpre ih

/-- Sequentially replace every terminal leaf with another finite derivation. Branches may have
different finite depths; no uniform fuel is introduced. -/
theorem bind {ctx : Ctx} {E : ExceptConds ctx}
    {Done Done' : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (h : Steps ctx E Done state P)
    (next : ∀ {state P}, (h : Done state P) → Steps ctx E Done' state P) :
    Steps ctx E Done' state P := by
  induction h with
  | done h => exact next h
  | step cases head tail ih => exact .step cases head ih
  | split cases cover branches ih => exact .split cases cover ih
  | subst eq_state hpre next ih => exact .subst eq_state hpre ih

/-- Prepend a step whose successful result is one exact machine state. -/
theorem prependExact {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state nextState : Machine.Config ctx.primCtx} {P I : Assertion ctx}
    (head : Std.Do.Triple (Machine.step ctx state).run P
      (StepPost ctx (fun actual => At ctx nextState actual I) E))
    (tail : Steps ctx E Done nextState I) :
    Steps ctx E Done state P := by
  apply Steps.step (fun actual => At ctx nextState actual I) head
  intro actual
  apply Steps.subst (state' := nextState)
  · exact Std.Do.SPred.and_elim_l
  · exact Std.Do.SPred.and_elim_r
  exact tail

/-- The exact one-step rule. -/
theorem one {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state nextState : Machine.Config ctx.primCtx} {P I : Assertion ctx}
    (head : Std.Do.Triple (Machine.step ctx state).run P
      (StepPost ctx (fun actual => At ctx nextState actual I) E))
    (done : Done nextState I) : Steps ctx E Done state P :=
  prependExact head (.done done)

/-- Prepend a pure machine transition. This is the only rule used by the VC walker for a
transition that does not execute an ambient action. -/
theorem pureStep {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state nextState : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (hstep : (Machine.step ctx state).run = pure (some nextState))
    (tail : Steps ctx E Done nextState P) :
    Steps ctx E Done state P := by
  apply Steps.step (fun actual => At ctx nextState actual P)
  · rw [hstep]
    apply Std.Do.Triple.pure
    exact Std.Do.SPred.and_intro (Std.Do.SPred.pure_intro rfl) .rfl
  · intro actual
    apply Steps.subst (state' := nextState)
    · exact Std.Do.SPred.and_elim_l
    · exact Std.Do.SPred.and_elim_r
    exact tail

/-- Prepend a transition that is visibly pure before running `OptionT`. This form lets symbolic
machine reduction determine `nextState` directly. -/
theorem pureMachineStep {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state nextState : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (hstep : Machine.step ctx state = Machine.ofOption ctx (some nextState))
    (tail : Steps ctx E Done nextState P) :
    Steps ctx E Done state P := by
  apply pureStep (nextState := nextState)
  · rw [hstep]
    rfl
  · exact tail

/-- Resume a returned value through one pending frame without normalizing the whole machine
transition. -/
theorem resumeReturn {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {frame : Frame ctx.primCtx} {stack : List (Frame ctx.primCtx)}
    {next : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (hresume : Machine.resumeFrame ctx frame value stack = some next)
    (tail : Steps ctx E Done next P) :
    Steps ctx E Done ⟨.ret value, scope, frame :: stack⟩ P := by
  apply pureMachineStep (nextState := next)
  · simp only [Machine.step, hresume]
  · exact tail

@[zspec] theorem resumeOpBodyDone {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value result : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {rest : List (Op.Arg ctx.primCtx)} {stack : List (Frame ctx.primCtx)}
    {P : Assertion ctx}
    (hbody : resume (some value) = .done result)
    (tail : Steps ctx E Done ⟨.ret result, frameEnv, stack⟩ P) :
    Steps ctx E Done ⟨.ret value, scope, .opBody resume rest frameEnv :: stack⟩ P := by
  apply resumeReturn (next := ⟨.ret result, frameEnv, stack⟩)
  · change Machine.driveOp (resume (some value)) rest frameEnv stack = some _
    rw [hbody, Machine.driveOp]
  · exact tail

@[zspec] theorem resumeOpBodyApply {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {scope frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {next : Val ctx.primCtx → Op.Body ctx.primCtx}
    {rest : List (Op.Arg ctx.primCtx)} {stack : List (Frame ctx.primCtx)}
    {P : Assertion ctx}
    (hbody : resume (some value) = .apply fn args next)
    (tail : Steps ctx E Done ⟨.apply fn args, frameEnv,
      .opBody (fun | some result => next result | none => .fail) rest frameEnv :: stack⟩ P) :
    Steps ctx E Done ⟨.ret value, scope, .opBody resume rest frameEnv :: stack⟩ P := by
  apply resumeReturn (next := ⟨.apply fn args, frameEnv,
    .opBody (fun | some result => next result | none => .fail) rest frameEnv :: stack⟩)
  · change Machine.driveOp (resume (some value)) rest frameEnv stack = some _
    rw [hbody, Machine.driveOp]
    congr 3
    apply congrArg (fun k => Frame.opBody k rest frameEnv)
    funext input
    cases input <;> rfl
  · exact tail

@[zspec] theorem resumeOpBodyNextTerm {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {resume nextResume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {operand : Term ctx.primCtx} {rest : List (Op.Arg ctx.primCtx)}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (hbody : resume (some value) = .next true nextResume)
    (tail : Steps ctx E Done ⟨.eval operand, frameEnv,
      .opBody nextResume rest frameEnv :: stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .opBody resume (.inl operand :: rest) frameEnv :: stack⟩ P := by
  apply resumeReturn (next := ⟨.eval operand, frameEnv,
    .opBody nextResume rest frameEnv :: stack⟩)
  · change Machine.driveOp (resume (some value)) (.inl operand :: rest) frameEnv stack = some _
    rw [hbody]
    exact Machine.driveOp_next_term nextResume operand rest frameEnv stack
  · exact tail

@[zspec] theorem resumeOpBodySkipTerm {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {resume nextResume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {operand : Term ctx.primCtx} {rest : List (Op.Arg ctx.primCtx)}
    {stack : List (Frame ctx.primCtx)} {next : Machine.Config ctx.primCtx} {P : Assertion ctx}
    (hbody : resume (some value) = .next false nextResume)
    (hnext : Machine.driveOp (nextResume none) rest frameEnv stack = some next)
    (tail : Steps ctx E Done next P) :
    Steps ctx E Done
      ⟨.ret value, scope, .opBody resume (.inl operand :: rest) frameEnv :: stack⟩ P := by
  apply resumeReturn (next := next)
  · change Machine.driveOp (resume (some value)) (.inl operand :: rest) frameEnv stack = some next
    rw [hbody, Machine.driveOp]
    exact hnext
  · exact tail

@[zspec] theorem resumeOpBodySkipThenDone {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value result : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {resume nextResume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {skipped : Term ctx.primCtx} {rest : List (Op.Arg ctx.primCtx)}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (hbody : resume (some value) = .next false nextResume)
    (hnext : nextResume none = .done result)
    (tail : Steps ctx E Done ⟨.ret result, frameEnv, stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .opBody resume (.inl skipped :: rest) frameEnv :: stack⟩ P := by
  apply resumeReturn (next := ⟨.ret result, frameEnv, stack⟩)
  · change Machine.driveOp (resume (some value)) (.inl skipped :: rest) frameEnv stack = some _
    rw [hbody, Machine.driveOp, hnext, Machine.driveOp]
  · exact tail

@[zspec] theorem resumeOpBodySkipThenNextTerm {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {resume nextResume finalResume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {skipped operand : Term ctx.primCtx} {rest : List (Op.Arg ctx.primCtx)}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (hbody : resume (some value) = .next false nextResume)
    (hnext : nextResume none = .next true finalResume)
    (tail : Steps ctx E Done ⟨.eval operand, frameEnv,
      .opBody finalResume rest frameEnv :: stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope,
        .opBody resume (.inl skipped :: .inl operand :: rest) frameEnv :: stack⟩ P := by
  apply resumeReturn (next := ⟨.eval operand, frameEnv,
    .opBody finalResume rest frameEnv :: stack⟩)
  · change Machine.driveOp (resume (some value))
      (.inl skipped :: .inl operand :: rest) frameEnv stack = some _
    rw [hbody, Machine.driveOp, hnext]
    exact Machine.driveOp_next_term finalResume operand rest frameEnv stack
  · exact tail

@[zspec] theorem resumeArgsCons {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {sink : Sink ctx.primCtx} {done : List (Val ctx.primCtx)}
    {operand : Term ctx.primCtx} {rest : List (Term ctx.primCtx)}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.eval operand, frameEnv,
      .args sink (done ++ [value]) rest frameEnv :: stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .args sink done (operand :: rest) frameEnv :: stack⟩ P := by
  apply resumeReturn
  · rfl
  · exact tail

@[zspec] theorem resumeArgsApply {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value fn : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {args : List (Val ctx.primCtx)} {stack : List (Frame ctx.primCtx)}
    {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.apply fn (args ++ [value]), frameEnv, stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .args .apply (fn :: args) [] frameEnv :: stack⟩ P := by
  apply resumeReturn
  · rfl
  · exact tail

@[zspec] theorem resumeArgsExit {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope frameEnv : Env ctx.primCtx}
    {name : String} {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.exit name value, frameEnv, stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .args (.exitTo name) [] [] frameEnv :: stack⟩ P := by
  apply resumeReturn
  · rfl
  · exact tail

theorem resumeInstrs {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope env : Env ctx.primCtx}
    {name : String} {rest : List (Instr ctx.primCtx)} {result : Term ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done
      (Machine.enterInstrs rest result (env ++ [(name, value)]) stack) P) :
    Steps ctx E Done ⟨.ret value, scope, .instrs name rest result env :: stack⟩ P := by
  apply resumeReturn
  · rfl
  · exact tail

@[zspec] theorem resumeInstrsNil {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope env : Env ctx.primCtx}
    {name : String} {result : Term ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.eval result, env ++ [(name, value)], stack⟩ P) :
    Steps ctx E Done ⟨.ret value, scope, .instrs name [] result env :: stack⟩ P := by
  apply resumeReturn (next := ⟨.eval result, env ++ [(name, value)], stack⟩)
  · rfl
  · exact tail

@[zspec] theorem resumeInstrsCons {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope env : Env ctx.primCtx}
    {name : String} {instr : Instr ctx.primCtx} {rest : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done
      ⟨.eval instr.value, env ++ [(name, value)], .instrs instr.name rest result
        (env ++ [(name, value)]) :: stack⟩ P) :
    Steps ctx E Done
      ⟨.ret value, scope, .instrs name (instr :: rest) result env :: stack⟩ P := by
  apply resumeReturn (next :=
    ⟨.eval instr.value, env ++ [(name, value)], .instrs instr.name rest result
      (env ++ [(name, value)]) :: stack⟩)
  · rfl
  · exact tail

@[zspec] theorem resumeCall {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope callerEnv : Env ctx.primCtx}
    {name : String} {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.ret value, callerEnv, stack⟩ P) :
    Steps ctx E Done ⟨.ret value, scope, .call name callerEnv :: stack⟩ P := by
  apply resumeReturn
  · rfl
  · exact tail

/-- Execute an ordinary operator reference by applying its lookup, purity, body, and drive
equations separately. -/
@[zspec] theorem applyOpPure {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {captured vargs : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {oper : Op ctx.primCtx ctx.M} {body : Op.Body ctx.primCtx}
    {next : Machine.Config ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hpure : oper.action name (captured ++ vargs) = none)
    (hbody : oper.body name (captured ++ vargs).length = some body)
    (hdrive : Machine.driveOp body (Op.Arg.ofVals (captured ++ vargs)) env stack =
      some next)
    (tail : Steps ctx E Done next P) :
    Steps ctx E Done ⟨.apply (.opRef name captured argTys outTy) vargs, env, stack⟩ P := by
  apply pureMachineStep (nextState := next)
  · simp only [Machine.step, Machine.applyValue, Machine.driveSelectedOp, hop,
      hpure, hbody, hdrive]
  · exact tail

@[zspec] theorem evalPrim {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {ty : Ty} {raw : Ty.type ctx.primCtx ty} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.ret (.mk ty raw), env, stack⟩ P) :
    Steps ctx E Done ⟨.eval (.prim ty raw), env, stack⟩ P := by
  apply pureMachineStep (nextState := ⟨.ret (.mk ty raw), env, stack⟩)
  · rfl
  · exact tail

@[zspec] theorem evalVar {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {value : Val ctx.primCtx} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (hvar : Scope.get? env name = some value)
    (tail : Steps ctx E Done ⟨.ret value, env, stack⟩ P) :
    Steps ctx E Done ⟨.eval (.var name), env, stack⟩ P := by
  apply pureMachineStep (nextState := ⟨.ret value, env, stack⟩)
  · simp only [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, hvar]
  · exact tail

@[zspec] theorem evalExit {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {term : Term ctx.primCtx} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done
      ⟨.eval term, env, .args (.exitTo name) [] [] env :: stack⟩ P) :
    Steps ctx E Done ⟨.eval (.exit name term), env, stack⟩ P := by
  apply pureMachineStep (nextState :=
    ⟨.eval term, env, .args (.exitTo name) [] [] env :: stack⟩)
  · rfl
  · exact tail

@[zspec] theorem evalCallNil {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {env : Env ctx.primCtx} {stack : List (Frame ctx.primCtx)}
    {P : Assertion ctx} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (tail : Steps ctx E Done ⟨.apply (.blockRef name (block.params.map Prod.snd) block.outTy) [],
      env, stack⟩ P) :
    Steps ctx E Done ⟨.eval (.call name []), env, stack⟩ P := by
  apply pureMachineStep (nextState :=
    ⟨.apply (.blockRef name (block.params.map Prod.snd) block.outTy) [], env, stack⟩)
  · simp only [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, hblock]
  · exact tail

@[zspec] theorem evalCallCons {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {operand : Term ctx.primCtx} {args : List (Term ctx.primCtx)}
    {env : Env ctx.primCtx} {stack : List (Frame ctx.primCtx)}
    {P : Assertion ctx} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (tail : Steps ctx E Done ⟨.eval operand, env,
      .args .apply [.blockRef name (block.params.map Prod.snd) block.outTy] args env :: stack⟩ P) :
    Steps ctx E Done ⟨.eval (.call name (operand :: args)), env, stack⟩ P := by
  apply pureMachineStep (nextState := ⟨.eval operand, env,
    .args .apply [.blockRef name (block.params.map Prod.snd) block.outTy] args env :: stack⟩)
  · simp only [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, hblock]
  · exact tail

@[zspec] theorem evalOp {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {args : List (Term ctx.primCtx)} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {oper : Op ctx.primCtx ctx.M} {body : Op.Body ctx.primCtx}
    {next : Machine.Config ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.body name args.length = some body)
    (hdrive : Machine.driveOp body (Op.Arg.ofTerms args) env stack = some next)
    (tail : Steps ctx E Done next P) :
    Steps ctx E Done ⟨.eval (.op name args), env, stack⟩ P := by
  apply pureMachineStep (nextState := next)
  · simp only [Machine.step, Machine.evalTerm, Machine.driveSelectedOp, hop,
      hbody, hdrive]
  · exact tail

@[zspec] theorem evalOpNextTerm {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {operand : Term ctx.primCtx} {args : List (Term ctx.primCtx)}
    {env : Env ctx.primCtx} {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {oper : Op ctx.primCtx ctx.M}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.body name (operand :: args).length = some (.next true resume))
    (tail : Steps ctx E Done ⟨.eval operand, env,
      .opBody resume (Op.Arg.ofTerms args) env :: stack⟩ P) :
    Steps ctx E Done ⟨.eval (.op name (operand :: args)), env, stack⟩ P := by
  apply evalOp (oper := oper) (body := .next true resume)
      (next := ⟨.eval operand, env, .opBody resume (Op.Arg.ofTerms args) env :: stack⟩)
  · exact hop
  · exact hbody
  · change Machine.driveOp (.next true resume)
      (.inl operand :: Op.Arg.ofTerms args) env stack = some _
    exact Machine.driveOp_next_term resume operand (Op.Arg.ofTerms args) env stack
  · exact tail

@[zspec] theorem applyBlock {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {argTys : List Ty} {outTy : Ty}
    {args : List (Val ctx.primCtx)} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (harity : args.length = block.params.length)
    (tail : Steps ctx E Done
      (Machine.enterInstrs block.instrs block.result (block.entryEnv args)
        (.call name env :: stack)) P) :
    Steps ctx E Done ⟨.apply (.blockRef name argTys outTy) args, env, stack⟩ P := by
  apply pureMachineStep (nextState := Machine.enterInstrs block.instrs block.result
    (block.entryEnv args) (.call name env :: stack))
  · simp only [Machine.step, Machine.applyValue, Machine.applyValueImmediate, hblock,
      Machine.enterBlock]
    rw [if_pos harity]
  · exact tail

@[zspec] theorem unwindExitCall {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {value : Val ctx.primCtx} {env callerEnv : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    (tail : Steps ctx E Done ⟨.ret value, callerEnv, stack⟩ P) :
    Steps ctx E Done ⟨.exit name value, env, .call name callerEnv :: stack⟩ P := by
  apply pureMachineStep (nextState := ⟨.ret value, callerEnv, stack⟩)
  · change Machine.ofOption ctx
      (Machine.unwindFrame (.call name callerEnv) name value env stack) = _
    rw [Machine.unwindFrame, if_pos rfl]
  · exact tail

/-- Prepend the machine transition that executes one `Op.action`. The exposed triple is
about the actual ambient action, not a sampled or state-specialized execution. -/
theorem actionStep {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {state : Machine.Config ctx.primCtx} {P : Assertion ctx}
    {action : ctx.M (Option (Val ctx.primCtx))}
    {nextState : Val ctx.primCtx → Machine.Config ctx.primCtx}
    {I : Val ctx.primCtx → Assertion ctx}
    (hstep : (Machine.step ctx state).run =
      action >>= fun value? => pure (value?.map nextState))
    (head : Std.Do.Triple action P (ActionPost ctx I E))
    (tail : ∀ value, Steps ctx E Done (nextState value) (I value)) :
    Steps ctx E Done state P := by
  apply Steps.step (fun actual => spred(∃ value, ⌜actual = nextState value⌝ ∧ I value))
  · rw [hstep]
    apply Std.Do.Triple.bind action _ head
    intro value?
    cases value? with
    | none =>
        apply Std.Do.Triple.pure
        exact .rfl
    | some value =>
        apply Std.Do.Triple.pure
        exact Std.Do.SPred.exists_intro' value <|
          Std.Do.SPred.and_intro (Std.Do.SPred.pure_intro rfl) .rfl
  · intro actual
    apply Steps.split (fun value => spred(⌜actual = nextState value⌝ ∧ I value))
    · exact .rfl
    · intro value
      apply Steps.subst (state' := nextState value)
      · exact Std.Do.SPred.and_elim_l
      · exact Std.Do.SPred.and_elim_r
      exact tail value

/-- Execute an effectful operator reference. The lookup and `action` equations identify the
actual ambient action without requiring callers to unfold the `OptionT` implementation. -/
@[zspec] theorem applyOpAction {ctx : Ctx} {E : ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → Assertion ctx → Prop}
    {name : String} {captured vargs : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {oper : Op ctx.primCtx ctx.M} {action : ctx.M (Option (Val ctx.primCtx))}
    {I : Val ctx.primCtx → Assertion ctx}
    (hop : ctx.opCtx.get? name = some oper)
    (hbody : oper.action name (captured ++ vargs) = some action)
    (head : Std.Do.Triple action P (ActionPost ctx I E))
    (tail : ∀ value, Steps ctx E Done ⟨.ret value, env, stack⟩ (I value)) :
    Steps ctx E Done ⟨.apply (.opRef name captured argTys outTy) vargs, env, stack⟩ P := by
  apply actionStep (action := action)
    (nextState := fun value => ⟨.ret value, env, stack⟩) (I := I)
  · simp only [Machine.step, Machine.applyValue, hop, hbody]
    simp [OptionT.run_bind, OptionT.run_monadLift]
    rw [map_eq_pure_bind]
    apply congrArg (fun k : Option (Val ctx.primCtx) →
      ctx.M (Option (Machine.Config ctx.primCtx)) => action >>= k)
    funext value?
    cases value? <;> rfl
  · exact head
  · exact tail

end Steps

/-- A permitted leaf returns a value to exactly `base` and establishes its normal postcondition. -/
inductive ReturnsTo (ctx : Ctx) (base : List (Frame ctx.primCtx))
    (Q : PostCond ctx (Val ctx.primCtx)) :
    Machine.Config ctx.primCtx → Assertion ctx → Prop where
| intro {value scope P} (h : P ⊢ₛ Q.1 value) :
    ReturnsTo ctx base Q ⟨.ret value, scope, base⟩ P

attribute [zspec] ReturnsTo.intro

/-- Evaluation from an arbitrary machine state. -/
abbrev EvaluatesFrom (ctx : Ctx) (state : Machine.Config ctx.primCtx)
    (base : List (Frame ctx.primCtx)) (P : Assertion ctx)
    (Q : PostCond ctx (Val ctx.primCtx)) : Prop :=
  Steps ctx Q.2 (ReturnsTo ctx base Q) state P

/-- Evaluation of a surface term from an empty machine stack. -/
abbrev EvaluatesTo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (P : Assertion ctx) (Q : PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvaluatesFrom ctx (Machine.start env term) [] P Q

/-- Evaluation of a surface block call whose arguments are terms. -/
abbrev EvaluatesCall (ctx : Ctx) (name : String) (args : List (Term ctx.primCtx))
    (P : Assertion ctx) (Q : PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvaluatesTo ctx [] (.call name args) P Q

/-- Application of already evaluated values, valid in every caller environment and stack. -/
def EvaluatesApply (ctx : Ctx) (fn : Val ctx.primCtx) (vargs : List (Val ctx.primCtx))
    (P : Assertion ctx) (Q : PostCond ctx (Val ctx.primCtx)) : Prop :=
  ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
    EvaluatesFrom ctx ⟨.apply fn vargs, env, base⟩ base P Q

/-- A value-level block call. The looked-up signature is used to form the canonical block value. -/
def EvaluatesCallValues (ctx : Ctx) (name : String) (vargs : List (Val ctx.primCtx))
    (P : Assertion ctx) (Q : PostCond ctx (Val ctx.primCtx)) : Prop :=
  ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
    ∃ block state, ctx.blockCtx.get? name = some block ∧
      Machine.enterBlock name block vargs env base = some state ∧
      EvaluatesFrom ctx state base P Q

namespace EvaluatesFrom

@[zspec] theorem done {ctx : Ctx} {base : List (Frame ctx.primCtx)}
    {value : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {P : Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)}
    (h : P ⊢ₛ Q.1 value) :
    EvaluatesFrom ctx ⟨.ret value, scope, base⟩ base P Q :=
  Steps.done (ReturnsTo.intro h)

theorem consequence {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {P P' : Assertion ctx}
    {Q Q' : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesFrom ctx state base P Q)
    (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    EvaluatesFrom ctx state base P' Q' := by
  apply Steps.consequence h hpre hpost.2
  intro final finalP finalP' hP hreturn
  cases hreturn with
  | intro hQ => exact .intro ((hP.trans hQ).trans (hpost.1 _))

/-- Compose a returning segment with a continuation. The first segment uses the final ambient
exception condition, exactly as `Std.Do.Triple.bind` does. -/
theorem bind {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {base finalBase : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {I : Val ctx.primCtx → Assertion ctx} {R : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesFrom ctx state base P (I, R.2))
    (next : ∀ value scope,
      EvaluatesFrom ctx ⟨.ret value, scope, base⟩ finalBase (I value) R) :
    EvaluatesFrom ctx state finalBase P R := by
  apply Steps.bind h
  intro final finalP hreturn
  cases hreturn with
  | @intro value scope _ hI =>
      exact (next value scope).consequence hI .rfl

/-- Prepend one exact monadic machine step. -/
theorem step {ctx : Ctx} {state nextState : Machine.Config ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {P I : Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (head : Std.Do.Triple (Machine.step ctx state).run P
      (StepPost ctx (fun actual => At ctx nextState actual I) Q.2))
    (tail : EvaluatesFrom ctx nextState base I Q) :
    EvaluatesFrom ctx state base P Q :=
  Steps.prependExact head tail

/-- Prepend a transition that does not execute an ambient action. -/
theorem pureStep {ctx : Ctx} {state nextState : Machine.Config ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (hstep : Machine.step ctx state = Machine.ofOption ctx (some nextState))
    (tail : EvaluatesFrom ctx nextState base P Q) :
    EvaluatesFrom ctx state base P Q :=
  Steps.pureMachineStep hstep tail

/-- Returning through a call frame is a pure machine step, so it preserves every ambient state. -/
theorem callReturn {ctx : Ctx} {name : String} {callerEnv scope : Env ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {value : Val ctx.primCtx}
    {P : Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)}
    (h : P ⊢ₛ Q.1 value) :
    EvaluatesFrom ctx ⟨.ret value, scope, .call name callerEnv :: base⟩ base P Q := by
  let final : Machine.Config ctx.primCtx := ⟨.ret value, callerEnv, base⟩
  apply EvaluatesFrom.step (nextState := final) (I := P)
  · rw [show (Machine.step ctx
        ⟨.ret value, scope, .call name callerEnv :: base⟩).run =
        pure (some final) by rfl]
    apply Std.Do.Triple.pure
    exact Std.Do.SPred.and_intro (Std.Do.SPred.pure_intro rfl) .rfl
  exact EvaluatesFrom.done h

end EvaluatesFrom

namespace EvaluatesTo

theorem consequence {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {P P' : Assertion ctx} {Q Q' : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesTo ctx env term P Q) (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    EvaluatesTo ctx env term P' Q' :=
  EvaluatesFrom.consequence h hpre hpost

end EvaluatesTo

namespace EvaluatesCall

theorem consequence {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {P P' : Assertion ctx} {Q Q' : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesCall ctx name args P Q) (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    EvaluatesCall ctx name args P' Q' :=
  EvaluatesTo.consequence h hpre hpost

end EvaluatesCall

namespace EvaluatesCallValues

/-- Build a value-call specification from a block-body derivation. -/
theorem of_body {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {P : Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)} {block : Block ctx.primCtx}
    (hblock : ctx.blockCtx.get? name = some block)
    (hbody : ∀ env base, ∃ state,
      Machine.enterBlock name block vargs env base = some state ∧
        EvaluatesFrom ctx state base P Q) :
    EvaluatesCallValues ctx name vargs P Q := by
  intro env base
  obtain ⟨state, henter, hfrom⟩ := hbody env base
  exact ⟨block, state, hblock, henter, hfrom⟩

end EvaluatesCallValues

namespace EvaluatesApply

theorem consequence {ctx : Ctx} {fn : Val ctx.primCtx}
    {vargs : List (Val ctx.primCtx)} {P P' : Assertion ctx}
    {Q Q' : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesApply ctx fn vargs P Q) (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    EvaluatesApply ctx fn vargs P' Q' := by
  intro env base
  exact (h env base).consequence hpre hpost

theorem blockRef {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {P : Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesCallValues ctx name vargs P Q) :
    EvaluatesApply ctx (.blockRef name argTys outTy) vargs P Q := by
  intro env base
  obtain ⟨block, state, hblock, henter, hfrom⟩ := h env base
  apply Steps.pureMachineStep (nextState := state)
  · simp [Machine.step, Machine.applyValue, Machine.applyValueImmediate,
      Machine.ofOption, hblock, henter]
  exact hfrom

end EvaluatesApply

namespace EvaluatesCallValues

theorem consequence {ctx : Ctx} {name : String}
    {vargs : List (Val ctx.primCtx)} {P P' : Assertion ctx}
    {Q Q' : PostCond ctx (Val ctx.primCtx)}
    (h : EvaluatesCallValues ctx name vargs P Q)
    (hpre : P' ⊢ₛ P) (hpost : Q ⊢ₚ Q') :
    EvaluatesCallValues ctx name vargs P' Q' := by
  intro env base
  obtain ⟨block, state, hblock, henter, hfrom⟩ := h env base
  exact ⟨block, state, hblock, henter, hfrom.consequence hpre hpost⟩

end EvaluatesCallValues

/-! Exact singleton adapters used by focused concrete proofs. -/

namespace Singleton

def idPre (P : Prop) : Std.Do.Assertion (.pure) :=
  Std.Do.SPred.pure P

def idPost {α : Type} (Q : α → Prop) : Std.Do.PostCond α (.pure) :=
  Std.Do.PostCond.noThrow fun value => Std.Do.SPred.pure (Q value)

def statePre {σ : Type} (initial : σ) : Std.Do.Assertion (.arg σ .pure) :=
  fun state => ULift.up (state = initial)

def statePost {σ α : Type} (Q : α → σ → Prop) :
    Std.Do.PostCond α (.arg σ .pure) :=
  Std.Do.PostCond.noThrow fun value state => ULift.up (Q value state)

@[simp] theorem idPre_down (P : Prop) : (idPre P).down ↔ P := Iff.rfl

@[simp] theorem statePre_apply {σ : Type} (initial state : σ) :
    (statePre initial state).down ↔ state = initial := Iff.rfl

@[simp] theorem idPost_down {α : Type} (Q : α → Prop) (value : α) :
    ((idPost Q).1 value).down ↔ Q value := Iff.rfl

@[simp] theorem statePost_apply {σ α : Type} (Q : α → σ → Prop)
    (value : α) (state : σ) :
    ((statePost Q).1 value state).down ↔ Q value state := Iff.rfl

end Singleton

/-! Exact-result notation remains useful for pure proofs, but is only a specialization of the
canonical Hoare judgments. It does not define an operational relation. -/

namespace Exact

abbrev idOpCtx (ctx : Ctx) (hM : ctx.M = Id) : OpCtx ctx.primCtx Id :=
  hM ▸ ctx.opCtx

abbrev idView (ctx : Ctx) (hM : ctx.M = Id) : Ctx where
  primCtx := ctx.primCtx
  M := Id
  monad := Id.instMonad
  opCtx := idOpCtx ctx hM
  blockCtx := ctx.blockCtx
  postShape := .pure
  wpMonad := Std.Do.Id.instWPMonad

def idOp (ctx : Ctx) (hM : ctx.M = Id) (oper : Op ctx.primCtx ctx.M) :
    Op ctx.primCtx Id :=
  hM ▸ oper

@[simp] theorem idView_get?_of_get? {ctx : Ctx} {name : String} {oper : Op ctx.primCtx ctx.M}
    (hM : ctx.M = Id) (hop : ctx.opCtx.get? name = some oper) :
    (idView ctx hM).opCtx.get? name = some (idOp ctx hM oper) := by
  rcases ctx with ⟨primCtx, M, monad, opCtx, blockCtx, postShape, wpMonad⟩
  dsimp at hM oper hop ⊢
  subst M
  exact hop

theorem idOp_property (ctx : Ctx) (hM : ctx.M = Id) (oper : Op ctx.primCtx ctx.M)
    (P : ∀ M, Op ctx.primCtx M → Prop) (h : P ctx.M oper) :
    P Id (idOp ctx hM oper) := by
  rcases ctx with ⟨primCtx, M, monad, opCtx, blockCtx, postShape, wpMonad⟩
  dsimp at hM oper h ⊢
  subst M
  exact h

@[simp] theorem idOp_body (ctx : Ctx) (hM : ctx.M = Id) (oper : Op ctx.primCtx ctx.M)
    (name : String) (arity : Nat) :
    (idOp ctx hM oper).body name arity = oper.body name arity := by
  exact idOp_property ctx hM oper
    (fun _ selected => selected.body name arity = oper.body name arity) rfl

/-! The following execution lemmas are deliberately confined to the `Id` view.  They support
inversion of exact judgments without asserting determinism for an arbitrary ambient effect. -/

namespace Machine

private def runId {ctx : Ctx} (hM : ctx.M = Id) {α : Type}
    (x : Machine.Effect (idView ctx hM) α) : Option α :=
  Id.run x.run

private theorem driveOp_appendStack {primCtx : PrimitiveCtx} (body : Op.Body primCtx)
    (rest : List (Op.Arg primCtx)) (env : Env primCtx) (stack base : List (Frame primCtx)) :
    Machine.driveOp body rest env (stack ++ base) =
      (Machine.driveOp body rest env stack).map (Machine.appendStack · base) := by
  induction rest generalizing body with
  | nil => cases body <;> simp [Machine.driveOp, Machine.appendStack]
  | cons arg rest ih =>
      cases body with
      | fail => simp [Machine.driveOp]
      | done => simp [Machine.driveOp, Machine.appendStack]
      | next eager resume =>
          cases eager <;> cases arg <;> simp [Machine.driveOp, Machine.appendStack, ih]
      | apply => simp [Machine.driveOp, Machine.appendStack]

private theorem enterInstrs_appendStack {primCtx : PrimitiveCtx} (instrs : List (Instr primCtx))
    (result : Term primCtx) (env : Env primCtx) (stack base : List (Frame primCtx)) :
    Machine.enterInstrs instrs result env (stack ++ base) =
      Machine.appendStack (Machine.enterInstrs instrs result env stack) base := by
  cases instrs <;> rfl

private theorem enterBlock_appendStack {primCtx : PrimitiveCtx} (name : String)
    (block : Block primCtx) (args : List (Val primCtx)) (env : Env primCtx)
    (stack base : List (Frame primCtx)) :
    Machine.enterBlock name block args env (stack ++ base) =
      (Machine.enterBlock name block args env stack).map (Machine.appendStack · base) := by
  by_cases hlen : args.length = block.params.length
  · simp only [Machine.enterBlock, if_pos hlen, Option.map_some]
    rw [show Frame.call name env :: (stack ++ base) =
      (Frame.call name env :: stack) ++ base by simp, enterInstrs_appendStack]
  · simp [Machine.enterBlock, hlen]

private theorem applyValueImmediate_appendStack {ctx : Ctx} (fn : Val ctx.primCtx)
    (args : List (Val ctx.primCtx)) (env : Env ctx.primCtx)
    (stack base : List (Frame ctx.primCtx)) :
    Machine.applyValueImmediate ctx fn args env (stack ++ base) =
      (Machine.applyValueImmediate ctx fn args env stack).map (Machine.appendStack · base) := by
  cases fn with
  | blockRef name argTys outTy =>
      simp only [Machine.applyValueImmediate]
      cases ctx.blockCtx.get? name <;> simp [enterBlock_appendStack]
  | opRef name captured argTys outTy =>
      simp only [Machine.applyValueImmediate]
      cases ctx.opCtx.get? name with
      | none => simp
      | some oper =>
          cases hbody : oper.body name (captured.length + args.length) <;>
            simp [hbody, driveOp_appendStack]
  | mk ty value =>
      simp only [Machine.applyValueImmediate]
      cases Term.evalApp (.mk ty value) args <;> simp [Machine.appendStack]

private theorem evalTermImmediate_appendStack {ctx : Ctx} (term : Term ctx.primCtx)
    (env : Env ctx.primCtx) (stack base : List (Frame ctx.primCtx)) :
    Machine.evalTermImmediate ctx term env (stack ++ base) =
      (Machine.evalTermImmediate ctx term env stack).map (Machine.appendStack · base) := by
  cases term with
  | prim => simp [Machine.evalTermImmediate, Machine.appendStack]
  | var name =>
      simp only [Machine.evalTermImmediate]
      cases Scope.get? env name <;> simp [Machine.appendStack]
      cases ctx.blockCtx.get? name <;> simp
  | exit => simp [Machine.evalTermImmediate, Machine.appendStack]
  | op name args =>
      simp only [Machine.evalTermImmediate]
      cases ctx.opCtx.get? name with
      | none => simp
      | some oper =>
          cases hbody : oper.body name args.length <;> simp [hbody, driveOp_appendStack]
  | call name args =>
      simp only [Machine.evalTermImmediate]
      cases ctx.blockCtx.get? name <;> cases args <;> simp [Machine.appendStack]
  | app => simp [Machine.evalTermImmediate, Machine.appendStack]

private theorem resumeFrame_appendStack {ctx : Ctx} (frame : Frame ctx.primCtx)
    (value : Val ctx.primCtx) (stack base : List (Frame ctx.primCtx)) :
    Machine.resumeFrame ctx frame value (stack ++ base) =
      (Machine.resumeFrame ctx frame value stack).map (Machine.appendStack · base) := by
  cases frame with
  | opBody resume rest env => simp [Machine.resumeFrame, driveOp_appendStack]
  | args sink done rest env =>
      cases rest with
      | cons => simp [Machine.resumeFrame, Machine.appendStack]
      | nil =>
          cases sink <;> cases done <;> simp [Machine.resumeFrame, Machine.appendStack]
  | instrs name rest result env =>
      simp [Machine.resumeFrame, enterInstrs_appendStack]
  | call => simp [Machine.resumeFrame, Machine.appendStack]

private theorem unwindFrame_appendStack {primCtx : PrimitiveCtx} (frame : Frame primCtx)
    (name : String) (value : Val primCtx) (env : Env primCtx)
    (stack base : List (Frame primCtx)) :
    Machine.unwindFrame frame name value env (stack ++ base) =
      (Machine.unwindFrame frame name value env stack).map (Machine.appendStack · base) := by
  cases frame <;> simp [Machine.unwindFrame, Machine.appendStack]
  split <;> simp

private theorem applyValue_appendStack {ctx : Ctx} {hM : ctx.M = Id}
    (fn : Val ctx.primCtx) (args : List (Val ctx.primCtx)) (env : Env ctx.primCtx)
    (stack base : List (Frame ctx.primCtx)) :
    runId hM (Machine.applyValue (idView ctx hM) fn args env (stack ++ base)) =
      Option.map (Machine.appendStack · base)
        (runId hM (Machine.applyValue (idView ctx hM) fn args env stack)) := by
  cases fn with
  | opRef name captured argTys outTy =>
      simp only [Machine.applyValue]
      cases hop : (idView ctx hM).opCtx.get? name with
      | none => simp only [hop, OptionT.fail, runId]; rfl
      | some oper =>
          simp only [hop]
          cases hactionDef : oper.action name (captured ++ args) with
          | none =>
              simp only [hactionDef, Machine.driveSelectedOp]
              cases hbody : oper.body name (captured ++ args).length with
              | none => simp only [hbody, OptionT.fail, runId]; rfl
              | some body =>
                  simp only [hbody, Machine.ofOption, OptionT.run_mk, runId]
                  rw [driveOp_appendStack]
                  rfl
          | some action =>
              simp only [hactionDef]
              cases haction : action with
              | none =>
                  change (none : Option (Machine.Config ctx.primCtx)) =
                    Option.map (Machine.appendStack · base) none
                  rfl
              | some value =>
                  change some ⟨.ret value, env, stack ++ base⟩ =
                    Option.map (Machine.appendStack · base)
                      (some ⟨.ret value, env, stack⟩)
                  rfl
  | blockRef name argTys outTy =>
      simp only [Machine.applyValue, Machine.ofOption, OptionT.run_mk, runId]
      rw [applyValueImmediate_appendStack]
      rfl
  | mk ty value =>
      simp only [Machine.applyValue, Machine.ofOption, OptionT.run_mk, runId]
      rw [applyValueImmediate_appendStack]
      rfl

private theorem evalTerm_appendStack {ctx : Ctx} {hM : ctx.M = Id}
    (term : Term ctx.primCtx) (env : Env ctx.primCtx)
    (stack base : List (Frame ctx.primCtx)) :
    runId hM (Machine.evalTerm (idView ctx hM) term env (stack ++ base)) =
      Option.map (Machine.appendStack · base)
        (runId hM (Machine.evalTerm (idView ctx hM) term env stack)) := by
  cases term with
  | op name args =>
      simp only [Machine.evalTerm]
      cases hop : (idView ctx hM).opCtx.get? name with
      | none => simp only [hop, OptionT.fail, runId]; rfl
      | some oper =>
          simp only [hop, Machine.driveSelectedOp]
          cases hbody : oper.body name args.length with
          | none => simp only [hbody, OptionT.fail, runId]; rfl
          | some body =>
              simp only [hbody, Machine.ofOption, OptionT.run_mk, runId]
              rw [driveOp_appendStack]
              rfl
  | prim =>
      simp only [Machine.evalTerm, Machine.ofOption, OptionT.run_mk, runId]
      rw [evalTermImmediate_appendStack]
      rfl
  | var =>
      simp only [Machine.evalTerm, Machine.ofOption, OptionT.run_mk, runId]
      rw [evalTermImmediate_appendStack]
      rfl
  | exit =>
      simp only [Machine.evalTerm, Machine.ofOption, OptionT.run_mk, runId]
      rw [evalTermImmediate_appendStack]
      rfl
  | call =>
      simp only [Machine.evalTerm, Machine.ofOption, OptionT.run_mk, runId]
      rw [evalTermImmediate_appendStack]
      rfl
  | app =>
      simp only [Machine.evalTerm, Machine.ofOption, OptionT.run_mk, runId]
      rw [evalTermImmediate_appendStack]
      rfl

theorem step_appendStack {ctx : Ctx} {hM : ctx.M = Id}
    {state next : Machine.Config ctx.primCtx} (base : List (Frame ctx.primCtx))
    (h : runId hM (Machine.step (idView ctx hM) state) = some next) :
    runId hM (Machine.step (idView ctx hM) (Machine.appendStack state base)) =
      some (Machine.appendStack next base) := by
  rcases state with ⟨control, env, stack⟩
  cases control with
  | stuck => simp [Machine.step, OptionT.fail, runId] at h
  | eval term =>
      simp only [Machine.appendStack, Machine.step]
      change runId hM (Machine.evalTerm (idView ctx hM) term env (stack ++ base)) = _
      rw [evalTerm_appendStack]
      exact congrArg (Option.map (Machine.appendStack · base)) h
  | apply fn args =>
      simp only [Machine.appendStack, Machine.step]
      change runId hM (Machine.applyValue (idView ctx hM) fn args env (stack ++ base)) = _
      rw [applyValue_appendStack]
      exact congrArg (Option.map (Machine.appendStack · base)) h
  | ret value =>
      cases stack with
      | nil => simp [Machine.step, OptionT.fail, runId] at h
      | cons frame stack =>
          simp only [Machine.appendStack, List.cons_append, Machine.step,
            Machine.ofOption, OptionT.run_mk, runId] at h ⊢
          rw [resumeFrame_appendStack]
          exact congrArg (Option.map (Machine.appendStack · base)) h
  | exit name value =>
      cases stack with
      | nil => simp [Machine.step, OptionT.fail, runId] at h
      | cons frame stack =>
          simp only [Machine.appendStack, List.cons_append, Machine.step,
            Machine.ofOption, OptionT.run_mk, runId] at h ⊢
          rw [unwindFrame_appendStack]
          exact congrArg (Option.map (Machine.appendStack · base)) h

theorem nsteps_appendStack {ctx : Ctx} {hM : ctx.M = Id} {fuel : Nat}
    {state next : Machine.Config ctx.primCtx} (base : List (Frame ctx.primCtx))
    (h : Id.run (Machine.nsteps (idView ctx hM) fuel state).run = some next) :
    Id.run (Machine.nsteps (idView ctx hM) fuel (Machine.appendStack state base)).run =
      some (Machine.appendStack next base) := by
  change runId hM (Machine.nsteps (idView ctx hM) fuel state) = some next at h
  change runId hM (Machine.nsteps (idView ctx hM) fuel
    (Machine.appendStack state base)) = some (Machine.appendStack next base)
  induction fuel generalizing state with
  | zero =>
      simp only [Machine.nsteps, runId] at h ⊢
      change some state = some next at h
      have hstate : state = next := Option.some.inj h
      subst next
      rfl
  | succ fuel ih =>
      simp only [Machine.nsteps, runId] at h ⊢
      rw [OptionT.run_bind] at h ⊢
      cases hstep : (Machine.step (idView ctx hM) state).run with
      | none => rw [hstep] at h; contradiction
      | some first =>
          rw [hstep] at h
          have hfull : (Machine.step (idView ctx hM)
              (Machine.appendStack state base)).run =
              (some (Machine.appendStack first base) :
                Id (Option (Machine.Config ctx.primCtx))) := by
            exact step_appendStack base (by exact hstep)
          rw [hfull]
          exact ih h

theorem nsteps_ret_empty_succ_none {ctx : Ctx} {hM : ctx.M = Id} (fuel : Nat)
    (value : Val ctx.primCtx) (env : Env ctx.primCtx) :
    Id.run (Machine.nsteps (idView ctx hM) (fuel + 1) ⟨.ret value, env, []⟩).run = none := by
  change runId hM (Machine.nsteps (idView ctx hM) (fuel + 1)
    ⟨.ret value, env, []⟩) = none
  unfold runId
  simp [Machine.nsteps, Machine.step, OptionT.fail]

private theorem step_appendStack_eq_of_not_boundary {ctx : Ctx} {hM : ctx.M = Id}
    (state : Machine.Config ctx.primCtx) (base : List (Frame ctx.primCtx))
    (hret : ∀ value env, state ≠ ⟨.ret value, env, []⟩)
    (hexit : ∀ name value env, state ≠ ⟨.exit name value, env, []⟩) :
    runId hM (Machine.step (idView ctx hM) (Machine.appendStack state base)) =
      Option.map (Machine.appendStack · base)
        (runId hM (Machine.step (idView ctx hM) state)) := by
  rcases state with ⟨control, env, stack⟩
  cases control with
  | stuck => rfl
  | eval term => exact evalTerm_appendStack term env stack base
  | apply fn args => exact applyValue_appendStack fn args env stack base
  | ret value =>
      cases stack with
      | nil => exact (hret value env rfl).elim
      | cons frame stack =>
          simp only [Machine.appendStack, List.cons_append, Machine.step,
            Machine.ofOption, OptionT.run_mk, runId]
          rw [resumeFrame_appendStack]
          rfl
  | exit name value =>
      cases stack with
      | nil => exact (hexit name value env rfl).elim
      | cons frame stack =>
          simp only [Machine.appendStack, List.cons_append, Machine.step,
            Machine.ofOption, OptionT.run_mk, runId]
          rw [unwindFrame_appendStack]
          rfl

private theorem nsteps_exit_opBodies_ne_result {ctx : Ctx} {hM : ctx.M = Id}
    {base : List (Frame ctx.primCtx)} (hbase : Frame.OpBodies base) (fuel : Nat)
    (name : String) (value final : Val ctx.primCtx) (env finalEnv : Env ctx.primCtx) :
    runId hM (Machine.nsteps (idView ctx hM) fuel ⟨.exit name value, env, base⟩) ≠
      some ⟨.ret final, finalEnv, []⟩ := by
  induction fuel generalizing base env with
  | zero =>
      simp only [Machine.nsteps, runId]
      intro h
      cases h
  | succ fuel ih =>
      cases hbase with
      | nil =>
          simp [Machine.nsteps, Machine.step, OptionT.fail, runId]
      | @cons resume rest frameEnv frames hframes =>
          simp only [Machine.nsteps, Machine.step, Machine.ofOption,
            Machine.unwindFrame, OptionT.run_bind, OptionT.run_mk, runId]
          exact ih hframes env

/-- If a successful Id run starts above a nonempty suffix of operator frames and consumes that
suffix, the computation above it must first have returned a value on an empty stack. -/
theorem exists_nsteps_of_append_opBodies {ctx : Ctx} {hM : ctx.M = Id}
    {state : Machine.Config ctx.primCtx} {base : List (Frame ctx.primCtx)}
    {fuel : Nat} {final : Val ctx.primCtx} {finalEnv : Env ctx.primCtx}
    (hbase : Frame.OpBodies base) (hne : base ≠ [])
    (hrun : runId hM (Machine.nsteps (idView ctx hM) fuel
      (Machine.appendStack state base)) = some ⟨.ret final, finalEnv, []⟩) :
    ∃ value steps env, runId hM (Machine.nsteps (idView ctx hM) steps state) =
      some ⟨.ret value, env, []⟩ := by
  induction fuel generalizing state with
  | zero =>
      simp only [Machine.nsteps, runId] at hrun
      rcases state with ⟨control, env, stack⟩
      simp [Machine.appendStack, hne] at hrun
  | succ fuel ih =>
      rcases state with ⟨control, env, stack⟩
      have continueRun :
          (∀ value env', (⟨control, env, stack⟩ : Machine.Config ctx.primCtx) ≠
            ⟨.ret value, env', []⟩) →
          (∀ name value env', (⟨control, env, stack⟩ : Machine.Config ctx.primCtx) ≠
            ⟨.exit name value, env', []⟩) →
          ∃ value steps resultEnv,
            runId hM (Machine.nsteps (idView ctx hM) steps
              ⟨control, env, stack⟩) = some ⟨.ret value, resultEnv, []⟩ := by
        intro hret hexit
        simp only [Machine.nsteps, runId] at hrun
        rw [OptionT.run_bind] at hrun
        have hstepEq := step_appendStack_eq_of_not_boundary (hM := hM)
          (⟨control, env, stack⟩ : Machine.Config ctx.primCtx) base hret hexit
        have hstepEq' : (Machine.step (idView ctx hM)
            (Machine.appendStack ⟨control, env, stack⟩ base)).run =
            (Option.map (Machine.appendStack · base)
              (Id.run (Machine.step (idView ctx hM) ⟨control, env, stack⟩).run) :
                Id (Option (Machine.Config ctx.primCtx))) := by
          exact hstepEq
        rw [hstepEq'] at hrun
        cases hstep : Id.run (Machine.step (idView ctx hM)
            ⟨control, env, stack⟩).run with
        | none =>
            have hstep' : (Machine.step (idView ctx hM)
                ⟨control, env, stack⟩).run =
                (none : Id (Option (Machine.Config ctx.primCtx))) := by exact hstep
            rw [hstep'] at hrun
            contradiction
        | some next =>
            have hstep' : (Machine.step (idView ctx hM)
                ⟨control, env, stack⟩).run =
                (some next : Id (Option (Machine.Config ctx.primCtx))) := by exact hstep
            rw [hstep'] at hrun
            obtain ⟨result, steps, resultEnv, hresult⟩ := ih hrun
            refine ⟨result, steps + 1, resultEnv, ?_⟩
            simp only [Machine.nsteps, runId, OptionT.run_bind]
            rw [show (Machine.step (idView ctx hM) ⟨control, env, stack⟩).run =
              (some next : Id (Option (Machine.Config ctx.primCtx))) by exact hstep]
            exact hresult
      cases control with
      | ret value =>
          cases stack with
          | nil => exact ⟨value, 0, env, rfl⟩
          | cons frame stack =>
              have hboundary :
                  (∀ value' env', (⟨.ret value, env, frame :: stack⟩ :
                    Machine.Config ctx.primCtx) ≠ ⟨.ret value', env', []⟩) ∧
                  (∀ name value' env', (⟨.ret value, env, frame :: stack⟩ :
                    Machine.Config ctx.primCtx) ≠ ⟨.exit name value', env', []⟩) := by
                constructor <;> intros <;> simp
              exact continueRun hboundary.1 hboundary.2
      | exit name value =>
          cases stack with
          | nil =>
              exact (nsteps_exit_opBodies_ne_result hbase (fuel + 1)
                name value final env finalEnv hrun).elim
          | cons frame stack =>
              have hboundary :
                  (∀ value' env', (⟨.exit name value, env, frame :: stack⟩ :
                    Machine.Config ctx.primCtx) ≠ ⟨.ret value', env', []⟩) ∧
                  (∀ name' value' env', (⟨.exit name value, env, frame :: stack⟩ :
                    Machine.Config ctx.primCtx) ≠ ⟨.exit name' value', env', []⟩) := by
                constructor <;> intros <;> simp
              exact continueRun hboundary.1 hboundary.2
      | stuck =>
          exact continueRun (by intros; simp) (by intros; simp)
      | eval term =>
          exact continueRun (by intros; simp) (by intros; simp)
      | apply fn args =>
          exact continueRun (by intros; simp) (by intros; simp)

end Machine

def pre (ctx : Ctx) (hM : ctx.M = Id) : Assertion (idView ctx hM) :=
  Std.Do.SPred.pure True

def post (ctx : Ctx) (hM : ctx.M = Id) (expected : Val ctx.primCtx) :
    PostCond (idView ctx hM) (Val ctx.primCtx) :=
  Std.Do.PostCond.noThrow fun actual => Std.Do.SPred.pure (actual = expected)

abbrev EvaluatesFrom (ctx : Ctx) (state : Machine.Config ctx.primCtx)
    (expected : Val ctx.primCtx) (base : List (Frame ctx.primCtx))
    (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  EvalTriple.EvaluatesFrom (idView ctx hM) state base (pre ctx hM) (post ctx hM expected)

abbrev EvaluatesTo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (expected : Val ctx.primCtx) (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  ∀ base : List (Frame ctx.primCtx),
    EvaluatesFrom ctx ⟨.eval term, env, base⟩ expected base hM

abbrev EvaluatesApply (ctx : Ctx) (fn : Val ctx.primCtx) (args : List (Val ctx.primCtx))
    (expected : Val ctx.primCtx) (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  EvalTriple.EvaluatesApply (idView ctx hM) fn args (pre ctx hM) (post ctx hM expected)

abbrev EvaluatesCall (ctx : Ctx) (name : String) (args : List (Term ctx.primCtx))
    (expected : Val ctx.primCtx) (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  EvaluatesTo ctx [] (.call name args) expected hM

abbrev EvaluatesCallValues (ctx : Ctx) (name : String) (args : List (Val ctx.primCtx))
    (expected : Val ctx.primCtx) (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  EvalTriple.EvaluatesCallValues (idView ctx hM) name args (pre ctx hM) (post ctx hM expected)

/-- Pointwise exact Hoare judgments for a list of terms. -/
inductive EvaluatesList (ctx : Ctx) (env : Env ctx.primCtx)
    : List (Term ctx.primCtx) → List (Val ctx.primCtx) →
      (hM : ctx.M = Id := by first | assumption | rfl) → Prop where
| nil {hM} : EvaluatesList ctx env [] [] hM
| cons {term terms value values hM} :
    EvaluatesTo ctx env term value hM → EvaluatesList ctx env terms values hM →
      EvaluatesList ctx env (term :: terms) (value :: values) hM

attribute [zspec] Exact.EvaluatesList.nil Exact.EvaluatesList.cons

theorem EvaluatesList.length_eq {ctx : Ctx} {env : Env ctx.primCtx}
    {hM : ctx.M = Id}
    {terms : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    (h : EvaluatesList ctx env terms values hM) : terms.length = values.length := by
  induction h <;> simp_all

namespace EvaluatesFrom

theorem done {ctx : Ctx} {value : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {hM : ctx.M = Id} :
    Exact.EvaluatesFrom ctx ⟨.ret value, scope, base⟩ value base hM :=
  EvalTriple.EvaluatesFrom.done (Std.Do.SPred.pure_intro rfl)

theorem pureStep {ctx : Ctx} {state next : Machine.Config ctx.primCtx}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)} {hM : ctx.M = Id}
    (hstep : Machine.step (idView ctx hM) state =
      Machine.ofOption (idView ctx hM) (some next))
    (hnext : Exact.EvaluatesFrom ctx next value base hM) :
    Exact.EvaluatesFrom ctx state value base hM :=
  EvalTriple.EvaluatesFrom.pureStep hstep hnext

theorem toNsteps {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {hM : ctx.M = Id} {P : Assertion (idView ctx hM)} {value : Val ctx.primCtx}
    {base : List (Frame ctx.primCtx)}
    (h : Steps (idView ctx hM) (post ctx hM value).2
      (ReturnsTo (idView ctx hM) base (post ctx hM value)) state P)
    (hP : P.down) :
    ∃ fuel scope, Id.run (Machine.nsteps (idView ctx hM) fuel state).run =
      some ⟨.ret value, scope, base⟩ := by
  revert hP
  induction h using @Steps.rec (idView ctx hM) (post ctx hM value).2
    (ReturnsTo (idView ctx hM) base (post ctx hM value)) with
  | done hdone =>
      intro hP
      cases hdone with
      | @intro returned scope terminalP hpost =>
          have heq := hpost hP
          change returned = value at heq
          subst returned
          exact ⟨0, scope, rfl⟩
  | @step state stepP nextP head tail ih =>
      intro hP
      unfold Std.Do.Triple at head
      dsimp only [Ctx.instWPMonadMPostShape, Ctx.instMonadM,
        Std.Do.WP.wp, Std.Do.Id.instWP, Std.Do.SPred.entails_nil] at head
      have hhead := head hP
      simp only [Std.Do.PredTrans.apply_Pure_pure] at hhead
      dsimp only [StepPost, Stuck] at hhead
      generalize hstep : (Machine.step (idView ctx hM) state).run.run = stepResult at hhead
      cases stepResult with
      | none => simp at hhead
      | some nextState =>
          have hnext : (nextP nextState).down := by simpa using hhead
          obtain ⟨fuel, scope, hrun⟩ := ih nextState hnext
          refine ⟨fuel + 1, scope, ?_⟩
          simp only [Machine.nsteps]
          rw [OptionT.run_bind]
          change (Machine.step (idView ctx hM) state).run =
            (some nextState : Id (Option (Machine.Config ctx.primCtx))) at hstep
          rw [hstep]
          exact hrun
  | @split ι state splitP cases cover branches ih =>
      intro hP
      have hcover := cover hP
      simp at hcover
      obtain ⟨i, hi⟩ := hcover
      exact ih i hi
  | @subst state state' substP invariant eqState hpre next ih =>
      intro hP
      have heq := eqState hP
      simp at heq
      subst state'
      exact ih (hpre hP)

theorem ofNsteps {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {hM : ctx.M = Id} {fuel : Nat} {value : Val ctx.primCtx}
    {scope : Env ctx.primCtx} {base : List (Frame ctx.primCtx)}
    (h : Id.run (Machine.nsteps (idView ctx hM) fuel state).run =
      some ⟨.ret value, scope, base⟩) :
    Exact.EvaluatesFrom ctx state value base hM := by
  induction fuel generalizing state with
  | zero =>
      change (some state : Option (Machine.Config ctx.primCtx)) =
        some ⟨.ret value, scope, base⟩ at h
      have hstate : state = ⟨.ret value, scope, base⟩ := Option.some.inj h
      subst state
      exact done
  | succ fuel ih =>
      simp only [Machine.nsteps] at h
      rw [OptionT.run_bind] at h
      cases hstep : (Machine.step (idView ctx hM) state).run with
      | none =>
          rw [hstep] at h
          contradiction
      | some next =>
          rw [hstep] at h
          have hnext : Id.run (Machine.nsteps (idView ctx hM) fuel next).run =
              some ⟨.ret value, scope, base⟩ := by exact h
          apply pureStep (ctx := ctx) (hM := hM) (next := next)
          · change (Machine.step (idView ctx hM) state).run =
              (some next : Id (Option (Machine.Config ctx.primCtx)))
            exact hstep
          exact ih hnext

/-- Turn one successful bounded `Id` execution into a finite exact derivation. The fuel is only
used to construct the proof and does not appear in the resulting judgment. -/
theorem ofEvalConfigFuel {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {hM : ctx.M = Id} {fuel : Nat} {value : Val ctx.primCtx}
    (hrun : Id.run (Machine.evalConfigFuel (idView ctx hM) fuel state).run = some value) :
    Exact.EvaluatesFrom ctx state value [] hM := by
  induction fuel generalizing state with
  | zero =>
      cases hresult : Machine.result? state with
      | none =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          change (none : Option (Val ctx.primCtx)) = some value at hrun
          contradiction
      | some result =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          change (some result : Option (Val ctx.primCtx)) = some value at hrun
          have hvalue : result = value := Option.some.inj hrun
          subst value
          cases state with
          | mk control scope stack =>
              cases control <;> cases stack <;>
                simp [Machine.result?] at hresult
              subst result
              exact done
  | succ fuel ih =>
      cases hresult : Machine.result? state with
      | some result =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          change (some result : Option (Val ctx.primCtx)) = some value at hrun
          have hvalue : result = value := Option.some.inj hrun
          subst value
          cases state with
          | mk control scope stack =>
              cases control <;> cases stack <;>
                simp [Machine.result?] at hresult
              subst result
              exact done
      | none =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          rw [OptionT.run_bind] at hrun
          cases hstep : (Machine.step (idView ctx hM) state).run with
          | none => rw [hstep] at hrun; contradiction
          | some next =>
              rw [hstep] at hrun
              simp only [Option.elimM] at hrun
              apply pureStep (ctx := ctx) (hM := hM) (next := next)
              · change (Machine.step (idView ctx hM) state).run =
                  (some next : Id (Option (Machine.Config ctx.primCtx)))
                exact hstep
              · exact ih hrun

/-- A nonterminal exact derivation has a successful first transition in an `Id` context. -/
theorem existsPureStep {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)} {hM : ctx.M = Id}
    (hnotDone : ∀ scope, state ≠ ⟨.ret value, scope, base⟩)
    (h : Exact.EvaluatesFrom ctx state value base hM) :
    ∃ next, Machine.step (idView ctx hM) state =
      Machine.ofOption (idView ctx hM) (some next) := by
  obtain ⟨fuel, scope, hrun⟩ := toNsteps h trivial
  cases fuel with
  | zero =>
      change (some state : Option (Machine.Config ctx.primCtx)) =
        some ⟨.ret value, scope, base⟩ at hrun
      exact (hnotDone scope (Option.some.inj hrun)).elim
  | succ fuel =>
      simp only [Machine.nsteps] at hrun
      rw [OptionT.run_bind] at hrun
      cases hstep : (Machine.step (idView ctx hM) state).run with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          refine ⟨next, ?_⟩
          change (Machine.step (idView ctx hM) state).run =
            (some next : Id (Option (Machine.Config ctx.primCtx)))
          exact hstep

/-- Remove one statically known pure transition from an exact derivation. -/
theorem afterPureStep {ctx : Ctx} {state next : Machine.Config ctx.primCtx}
    {value : Val ctx.primCtx} {base : List (Frame ctx.primCtx)} {hM : ctx.M = Id}
    (hnotDone : ∀ scope, state ≠ ⟨.ret value, scope, base⟩)
    (hstep : Machine.step (idView ctx hM) state =
      Machine.ofOption (idView ctx hM) (some next))
    (h : Exact.EvaluatesFrom ctx state value base hM) :
    Exact.EvaluatesFrom ctx next value base hM := by
  obtain ⟨fuel, scope, hrun⟩ := toNsteps h trivial
  cases fuel with
  | zero =>
      change (some state : Option (Machine.Config ctx.primCtx)) =
        some ⟨.ret value, scope, base⟩ at hrun
      have hstate : state = ⟨.ret value, scope, base⟩ := Option.some.inj hrun
      exact (hnotDone scope hstate).elim
  | succ fuel =>
      simp only [Machine.nsteps] at hrun
      rw [OptionT.run_bind] at hrun
      have hstepRun : (Machine.step (idView ctx hM) state).run =
          (some next : Id (Option (Machine.Config ctx.primCtx))) := by
        rw [hstep]
        rfl
      rw [hstepRun] at hrun
      exact ofNsteps hrun

theorem bind {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {value final : Val ctx.primCtx} {base finalBase : List (Frame ctx.primCtx)}
    {hM : ctx.M = Id}
    (h : Exact.EvaluatesFrom ctx state value base hM)
    (hcont : ∀ scope,
      Exact.EvaluatesFrom ctx ⟨.ret value, scope, base⟩ final finalBase hM) :
    Exact.EvaluatesFrom ctx state final finalBase hM := by
  apply EvalTriple.EvaluatesFrom.bind h
  intro actual scope
  apply Steps.subst (ctx := idView ctx hM) (state' := ⟨.ret value, scope, base⟩)
  · exact Std.Do.SPred.pure_mono fun hactual => by cases hactual; rfl
  · exact Std.Do.SPred.pure_mono fun _ => trivial
  exact hcont scope

/-- Remove a known finite Id-machine prefix from an exact derivation. -/
theorem afterNsteps {ctx : Ctx} {state next : Machine.Config ctx.primCtx}
    {value : Val ctx.primCtx} {hM : ctx.M = Id}
    {steps : Nat}
    (hprefix : Id.run (Machine.nsteps (idView ctx hM) steps state).run = some next)
    (h : Exact.EvaluatesFrom ctx state value [] hM) :
    Exact.EvaluatesFrom ctx next value [] hM := by
  obtain ⟨fuel, scope, hrun⟩ := toNsteps h trivial
  by_cases hle : steps ≤ fuel
  · obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Machine.nsteps_add, OptionT.run_bind] at hrun
    have hprefix' : (Machine.nsteps (idView ctx hM) steps state).run =
        (some next : Id (Option (Machine.Config ctx.primCtx))) := by exact hprefix
    rw [hprefix'] at hrun
    exact ofNsteps hrun
  · have hlt : fuel < steps := by omega
    let rest := steps - fuel - 1
    have hsteps : steps = fuel + (rest + 1) := by omega
    rw [hsteps, Machine.nsteps_add, OptionT.run_bind] at hprefix
    have hrun' : (Machine.nsteps (idView ctx hM) fuel state).run =
        (some ⟨.ret value, scope, []⟩ : Id (Option (Machine.Config ctx.primCtx))) := by
      exact hrun
    rw [hrun'] at hprefix
    have hnone := Machine.nsteps_ret_empty_succ_none (ctx := ctx) (hM := hM)
      rest value scope
    have htail : Id.run (Machine.nsteps (idView ctx hM) (rest + 1)
        ⟨.ret value, scope, []⟩).run = some next := by exact hprefix
    rw [hnone] at htail
    contradiction

/-- An exact derivation cannot continue past an empty-stack return with a different result. -/
theorem retEmptyEq {ctx : Ctx} {result value : Val ctx.primCtx}
    {env : Env ctx.primCtx} {hM : ctx.M = Id}
    (h : Exact.EvaluatesFrom ctx ⟨.ret result, env, []⟩ value [] hM) : value = result := by
  obtain ⟨fuel, scope, hrun⟩ := toNsteps h trivial
  cases fuel with
  | zero =>
      change some (⟨.ret result, env, []⟩ : Machine.Config ctx.primCtx) =
        some ⟨.ret value, scope, []⟩ at hrun
      exact (Action.ret.inj (Machine.Config.mk.inj (Option.some.inj hrun)).1).symm
  | succ fuel =>
      have hnone := Machine.nsteps_ret_empty_succ_none (ctx := ctx) (hM := hM)
        fuel result env
      rw [hnone] at hrun
      contradiction

/-- Invert a successful exact run above a nonempty suffix of operator frames. -/
theorem existsOfAppendOpBodies {ctx : Ctx} {state : Machine.Config ctx.primCtx}
    {base : List (Frame ctx.primCtx)} {final : Val ctx.primCtx} {hM : ctx.M = Id}
    (hbase : Frame.OpBodies base) (hne : base ≠ [])
    (h : Exact.EvaluatesFrom ctx (Machine.appendStack state base) final [] hM) :
    ∃ value, Exact.EvaluatesFrom ctx state value [] hM := by
  obtain ⟨fuel, finalEnv, hrun⟩ := toNsteps h trivial
  obtain ⟨value, steps, env, hvalue⟩ :=
    Machine.exists_nsteps_of_append_opBodies (ctx := ctx) (hM := hM)
      hbase hne hrun
  exact ⟨value, ofNsteps hvalue⟩

end EvaluatesFrom

namespace EvaluatesTo

/-- Promote an empty-stack exact derivation for a surface term to the continuation-parametric
surface judgment. -/
theorem ofEvaluatesFrom {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} {hM : ctx.M = Id}
    (h : Exact.EvaluatesFrom ctx (Machine.start env term) value [] hM) :
    Exact.EvaluatesTo ctx env term value hM := by
  obtain ⟨fuel, scope, hrun⟩ := EvaluatesFrom.toNsteps h trivial
  intro base
  apply EvaluatesFrom.ofNsteps
  have hweaken := Machine.nsteps_appendStack (ctx := ctx) (hM := hM) base hrun
  simpa [Machine.start, Machine.appendStack] using hweaken

/-- Lift a successful bounded surface execution to the continuation-parametric exact judgment. -/
theorem ofEvalFuel {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} {hM : ctx.M = Id} {fuel : Nat}
    (hrun : Id.run (Machine.evalFuel (idView ctx hM) fuel env term).run = some value) :
    Exact.EvaluatesTo ctx env term value hM :=
  ofEvaluatesFrom (EvaluatesFrom.ofEvalConfigFuel hrun)

private def runId {ctx : Ctx} (hM : ctx.M = Id) {α : Type}
    (x : Machine.Effect (idView ctx hM) α) : Option α :=
  Id.run x.run

theorem steps_to_fuel {ctx : Ctx} {hM : ctx.M = Id}
    {state : Machine.Config ctx.primCtx} {P : Assertion (idView ctx hM)}
    {expected : Val ctx.primCtx}
    (h : Steps (idView ctx hM) (post ctx hM expected).2
      (ReturnsTo (idView ctx hM) [] (post ctx hM expected)) state P)
    (hP : P.down) :
    ∃ fuel, runId hM (Machine.evalConfigFuel (idView ctx hM) fuel state) = some expected := by
  revert hP
  induction h using Steps.rec (ctx := idView ctx hM) with
  | done hdone =>
      intro hP
      cases hdone with
      | @intro value scope terminalP hpost =>
          have heq := hpost hP
          change value = expected at heq
          subst expected
          exact ⟨0, by rfl⟩
  | @step state stepP next head tail ih =>
      intro hP
      unfold Std.Do.Triple at head
      dsimp only [Ctx.instWPMonadMPostShape, Ctx.instMonadM,
        Std.Do.WP.wp, Std.Do.Id.instWP, Std.Do.SPred.entails_nil] at head
      have hhead := head hP
      simp only [Std.Do.PredTrans.apply_Pure_pure] at hhead
      dsimp only [StepPost, Stuck] at hhead
      generalize hstep : (Machine.step (idView ctx hM) state).run.run = stepResult at hhead
      cases stepResult with
      | none =>
          simp at hhead
      | some nextState =>
          have hnext : (next nextState).down := by simpa using hhead
          obtain ⟨fuel, hrun⟩ := ih nextState hnext
          have hresult : Machine.result? state = none := by
            cases state with
            | mk control env stack =>
                cases control <;> cases stack <;>
                  simp [Machine.result?, Machine.step, OptionT.fail] at hstep ⊢
          exact ⟨fuel + 1, by
            simp only [Machine.evalConfigFuel, hresult]
            unfold runId at hrun ⊢
            have hstepId : (Machine.step (idView ctx hM) state).run =
                (some nextState : Id (Option (Machine.Config ctx.primCtx))) := hstep
            rw [OptionT.run_bind]
            rw [hstepId]
            exact hrun⟩
  | @split ι state splitP cases cover branches ih =>
      intro hP
      have hcover := cover hP
      simp at hcover
      obtain ⟨i, hi⟩ := hcover
      exact ih i hi
  | @subst state state' substP invariant eq_state hpre next ih =>
      intro hP
      have heq := eq_state hP
      simp at heq
      subst heq
      exact ih (hpre hP)

private theorem evalConfigFuel_of_result {ctx : Ctx} {hM : ctx.M = Id}
    (fuel : Nat) (state : Machine.Config ctx.primCtx) (value : Val ctx.primCtx)
    (hresult : Machine.result? state = some value) :
    runId hM (Machine.evalConfigFuel (idView ctx hM) fuel state) = some value := by
  cases fuel <;> simp only [Machine.evalConfigFuel, hresult] <;>
    change (some value : Option (Val ctx.primCtx)) = some value <;> rfl

private theorem evalConfigFuel_zero_of_none {ctx : Ctx} {hM : ctx.M = Id}
    (state : Machine.Config ctx.primCtx) (hresult : Machine.result? state = none) :
    runId hM (Machine.evalConfigFuel (idView ctx hM) 0 state) = none := by
  simp only [Machine.evalConfigFuel, hresult]
  rfl

private theorem evalConfigFuel_succ_of_none {ctx : Ctx} {hM : ctx.M = Id}
    (fuel : Nat) (state : Machine.Config ctx.primCtx)
    (hresult : Machine.result? state = none) :
    runId hM (Machine.evalConfigFuel (idView ctx hM) (fuel + 1) state) =
      match runId hM (Machine.step (idView ctx hM) state) with
      | none => none
      | some next => runId hM (Machine.evalConfigFuel (idView ctx hM) fuel next) := by
  simp only [Machine.evalConfigFuel, hresult]
  unfold runId
  change (Machine.step (idView ctx hM) state >>= fun next =>
    Machine.evalConfigFuel (idView ctx hM) fuel next).run = _
  rw [OptionT.run_bind]
  cases (Machine.step (idView ctx hM) state).run <;> rfl

theorem evalConfigFuel_unique {ctx : Ctx} {hM : ctx.M = Id}
    {state : Machine.Config ctx.primCtx} {fuel₁ fuel₂ : Nat}
    {value₁ value₂ : Val ctx.primCtx}
    (h₁ : runId hM (Machine.evalConfigFuel (idView ctx hM) fuel₁ state) = some value₁)
    (h₂ : runId hM (Machine.evalConfigFuel (idView ctx hM) fuel₂ state) = some value₂) :
    value₁ = value₂ := by
  induction fuel₁ generalizing fuel₂ state with
  | zero =>
      cases hresult : Machine.result? state with
      | none =>
          rw [evalConfigFuel_zero_of_none state hresult] at h₁
          contradiction
      | some value =>
          rw [evalConfigFuel_of_result 0 state value hresult] at h₁
          rw [evalConfigFuel_of_result fuel₂ state value hresult] at h₂
          exact Option.some.inj (h₁.symm.trans h₂)
  | succ fuel₁ ih =>
      cases hresult : Machine.result? state with
      | some value =>
          rw [evalConfigFuel_of_result (fuel₁ + 1) state value hresult] at h₁
          rw [evalConfigFuel_of_result fuel₂ state value hresult] at h₂
          exact Option.some.inj (h₁.symm.trans h₂)
      | none =>
          rw [evalConfigFuel_succ_of_none fuel₁ state hresult] at h₁
          cases hstep : runId hM (Machine.step (idView ctx hM) state) with
          | none => simp [hstep] at h₁
          | some nextState =>
              have h₁' :
                  runId hM (Machine.evalConfigFuel (idView ctx hM) fuel₁ nextState) =
                    some value₁ := by
                simpa [hstep] using h₁
              cases fuel₂ with
              | zero =>
                  rw [evalConfigFuel_zero_of_none state hresult] at h₂
                  contradiction
              | succ fuel₂ =>
                  rw [evalConfigFuel_succ_of_none fuel₂ state hresult] at h₂
                  have h₂' :
                      runId hM (Machine.evalConfigFuel (idView ctx hM) fuel₂ nextState) =
                        some value₂ := by
                    simpa [hstep] using h₂
                  exact ih h₁' h₂'

theorem unique {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value₁ value₂ : Val ctx.primCtx} {hM : ctx.M = Id}
    (h₁ : Exact.EvaluatesTo ctx env term value₁ hM)
    (h₂ : Exact.EvaluatesTo ctx env term value₂ hM) : value₁ = value₂ := by
  obtain ⟨fuel₁, hrun₁⟩ := steps_to_fuel (h₁ []) trivial
  obtain ⟨fuel₂, hrun₂⟩ := steps_to_fuel (h₂ []) trivial
  exact evalConfigFuel_unique hrun₁ hrun₂

theorem iff_eq_of {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {canonical expected : Val ctx.primCtx} {hM : ctx.M = Id}
    (h : Exact.EvaluatesTo ctx env term canonical hM) :
    Exact.EvaluatesTo ctx env term expected hM ↔ canonical = expected := by
  constructor
  · intro hExpected
    exact unique h hExpected
  · intro heq
    subst expected
    exact h

theorem to_top {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {value : Val ctx.primCtx} {hM : ctx.M = Id}
    (h : Exact.EvaluatesTo ctx env term value hM) :
    EvalTriple.EvaluatesTo (idView ctx hM) env term (pre ctx hM) (post ctx hM value) := by
  change EvalTriple.EvaluatesFrom (idView ctx hM) (Machine.start env term) []
    (pre ctx hM) (post ctx hM value)
  simpa [Machine.start] using h []

@[eval_semantic, zspec] theorem prim {ctx : Ctx} {env : Env ctx.primCtx} (ty : Ty)
    (value : Ty.type ctx.primCtx ty) {hM : ctx.M = Id} :
    Exact.EvaluatesTo ctx env (.prim ty value) (.mk ty value) hM := by
  intro base
  apply Exact.EvaluatesFrom.pureStep (next := ⟨.ret (.mk ty value), env, base⟩)
  · rfl
  exact Exact.EvaluatesFrom.done

@[eval_semantic, zspec] theorem var_local {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {value : Val ctx.primCtx} (hlocal : Scope.get? env name = some value)
    {hM : ctx.M = Id} : Exact.EvaluatesTo ctx env (.var name) value hM := by
  intro base
  apply Exact.EvaluatesFrom.pureStep (next := ⟨.ret value, env, base⟩)
  · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
      Machine.ofOption, idView, idOpCtx, hlocal]
  exact Exact.EvaluatesFrom.done

@[eval_semantic, zspec] theorem var_block {ctx : Ctx} {env : Env ctx.primCtx} {name : String}
    {block : Block ctx.primCtx} (hlocal : Scope.get? env name = none)
    (hblock : ctx.blockCtx.get? name = some block) {hM : ctx.M = Id} :
    Exact.EvaluatesTo ctx env (.var name)
      (.blockRef name (block.params.map Prod.snd) block.outTy) hM := by
  intro base
  apply Exact.EvaluatesFrom.pureStep
    (next := ⟨.ret (.blockRef name (block.params.map Prod.snd) block.outTy), env, base⟩)
  · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate,
      Machine.ofOption, idView, idOpCtx, hlocal, hblock]
  exact Exact.EvaluatesFrom.done

theorem of_eq {ctx : Ctx} {env : Env ctx.primCtx} {term : Term ctx.primCtx}
    {canonical expected : Val ctx.primCtx} {hM : ctx.M = Id}
    (h : Exact.EvaluatesTo ctx env term canonical hM) (heq : canonical = expected) :
    Exact.EvaluatesTo ctx env term expected hM := by
  subst expected
  exact h

end EvaluatesTo

/-- User-facing total evaluator for exact `Id` semantics. Machine stuckness is not an exception in
this interface: successful exact evaluation returns `some value`, and absence of an exact result
returns `none`. -/
def eval? (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (hM : ctx.M = Id := by first | assumption | rfl) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  EvalTriple.total? fun value => Exact.EvaluatesTo ctx env term value hM

def evalList? (ctx : Ctx) (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx))
    (hM : ctx.M = Id := by first | assumption | rfl) :
    Std.Do.PredTrans .pure (Option (List (Val ctx.primCtx))) :=
  EvalTriple.total? fun values => Exact.EvaluatesList ctx env terms values hM

def apply? (ctx : Ctx) (fn : Val ctx.primCtx) (args : List (Val ctx.primCtx))
    (hM : ctx.M = Id := by first | assumption | rfl) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  EvalTriple.total? fun value => Exact.EvaluatesApply ctx fn args value hM

def callValues? (ctx : Ctx) (name : String) (args : List (Val ctx.primCtx))
    (hM : ctx.M = Id := by first | assumption | rfl) :
    Std.Do.PredTrans .pure (Option (Val ctx.primCtx)) :=
  EvalTriple.total? fun value => Exact.EvaluatesCallValues ctx name args value hM

theorem eval?_triple_of_evaluatesTo {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Exact.EvaluatesTo ctx env term value hM)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (eval? ctx env term hM) (Q.1 (some value)) Q := by
  change (Q.1 (some value)).down → _
  intro hQ
  dsimp [eval?, total?]
  constructor
  · intro actual hactual
    have hsame : actual = value := EvaluatesTo.unique hactual h
    subst actual
    exact hQ
  · intro hnone
    exact (hnone value h).elim

theorem eval?_some_of_wp {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id}
    {success : Val ctx.primCtx → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (eval? ctx env term hM)).apply (somePost success)).down) :
    ∃ value, Exact.EvaluatesTo ctx env term value hM ∧ (success value).down := by
  exact EvalTriple.total?_some_of_wp (R := fun value =>
    Exact.EvaluatesTo ctx env term value hM) (success := success) h

theorem evalList?_some_of_wp {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {success : List (Val ctx.primCtx) → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (evalList? ctx env terms hM)).apply (somePost success)).down) :
    ∃ values, Exact.EvaluatesList ctx env terms values hM ∧ (success values).down := by
  exact EvalTriple.total?_some_of_wp (R := fun values =>
    Exact.EvaluatesList ctx env terms values hM) (success := success) h

theorem apply?_some_of_wp {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id}
    {success : Val ctx.primCtx → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (apply? ctx fn args hM)).apply (somePost success)).down) :
    ∃ value, Exact.EvaluatesApply ctx fn args value hM ∧ (success value).down := by
  exact EvalTriple.total?_some_of_wp (R := fun value =>
    Exact.EvaluatesApply ctx fn args value hM) (success := success) h

theorem callValues?_some_of_wp {ctx : Ctx} {name : String}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id}
    {success : Val ctx.primCtx → Std.Do.Assertion .pure}
    (h : ((Std.Do.wp (callValues? ctx name args hM)).apply (somePost success)).down) :
    ∃ value, Exact.EvaluatesCallValues ctx name args value hM ∧ (success value).down := by
  exact EvalTriple.total?_some_of_wp (R := fun value =>
    Exact.EvaluatesCallValues ctx name args value hM) (success := success) h

theorem evaluatesTo_of_eval?_triple {ctx : Ctx} {env : Env ctx.primCtx}
    {term : Term ctx.primCtx} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Std.Do.Triple (eval? ctx env term hM) (Std.Do.SPred.pure True)
      (someEqPost value)) :
    Exact.EvaluatesTo ctx env term value hM := by
  have hwp := (Std.Do.Triple.iff.mp h) trivial
  obtain ⟨actual, hactual, heq⟩ := eval?_some_of_wp hwp
  subst actual
  exact hactual

theorem evaluatesList_of_evalList?_triple {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {values : List (Val ctx.primCtx)}
    (h : Std.Do.Triple (evalList? ctx env terms hM) (Std.Do.SPred.pure True)
      (someEqPost values)) :
    Exact.EvaluatesList ctx env terms values hM := by
  have hwp := (Std.Do.Triple.iff.mp h) trivial
  obtain ⟨actual, hactual, heq⟩ := evalList?_some_of_wp hwp
  subst actual
  exact hactual

theorem EvaluatesList.unique {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {values₁ values₂ : List (Val ctx.primCtx)}
    {hM : ctx.M = Id}
    (h₁ : Exact.EvaluatesList ctx env terms values₁ hM)
    (h₂ : Exact.EvaluatesList ctx env terms values₂ hM) : values₁ = values₂ := by
  induction h₁ generalizing values₂ with
  | nil =>
      cases h₂
      rfl
  | cons hterm₁ hrest₁ ih =>
      cases h₂ with
      | cons hterm₂ hrest₂ =>
          have hvalue := EvaluatesTo.unique hterm₁ hterm₂
          have hvalues := ih hrest₂
          subst hvalue
          subst hvalues
          rfl

theorem EvaluatesApply.unique {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {value₁ value₂ : Val ctx.primCtx}
    {hM : ctx.M = Id}
    (h₁ : Exact.EvaluatesApply ctx fn args value₁ hM)
    (h₂ : Exact.EvaluatesApply ctx fn args value₂ hM) : value₁ = value₂ := by
  obtain ⟨fuel₁, hrun₁⟩ := EvaluatesTo.steps_to_fuel (h₁ [] []) trivial
  obtain ⟨fuel₂, hrun₂⟩ := EvaluatesTo.steps_to_fuel (h₂ [] []) trivial
  exact EvaluatesTo.evalConfigFuel_unique hrun₁ hrun₂

theorem evalList?_triple_of_evaluatesList {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {hM : ctx.M = Id}
    {values : List (Val ctx.primCtx)}
    (h : Exact.EvaluatesList ctx env terms values hM)
    (Q : Std.Do.PostCond (Option (List (Val ctx.primCtx))) .pure) :
    Std.Do.Triple (evalList? ctx env terms hM) (Q.1 (some values)) Q := by
  change (Q.1 (some values)).down → _
  intro hQ
  dsimp [evalList?, total?]
  constructor
  · intro actual hactual
    have hsame : actual = values := EvaluatesList.unique hactual h
    subst actual
    exact hQ
  · intro hnone
    exact (hnone values h).elim

theorem apply?_triple_of_evaluatesApply {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id}
    {value : Val ctx.primCtx}
    (h : Exact.EvaluatesApply ctx fn args value hM)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (apply? ctx fn args hM) (Q.1 (some value)) Q := by
  change (Q.1 (some value)).down → _
  intro hQ
  dsimp [apply?, total?]
  constructor
  · intro actual hactual
    have hsame : actual = value := EvaluatesApply.unique hactual h
    subst actual
    exact hQ
  · intro hnone
    exact (hnone value h).elim

theorem evaluatesApply_of_apply?_triple {ctx : Ctx} {fn : Val ctx.primCtx}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Std.Do.Triple (apply? ctx fn args hM) (Std.Do.SPred.pure True)
      (someEqPost value)) :
    Exact.EvaluatesApply ctx fn args value hM := by
  have hwp := (Std.Do.Triple.iff.mp h) trivial
  obtain ⟨actual, hactual, heq⟩ := apply?_some_of_wp hwp
  subst actual
  exact hactual

theorem evaluatesCallValues_of_callValues?_triple {ctx : Ctx} {name : String}
    {args : List (Val ctx.primCtx)} {hM : ctx.M = Id} {value : Val ctx.primCtx}
    (h : Std.Do.Triple (callValues? ctx name args hM) (Std.Do.SPred.pure True)
      (someEqPost value)) :
    Exact.EvaluatesCallValues ctx name args value hM := by
  have hwp := (Std.Do.Triple.iff.mp h) trivial
  obtain ⟨actual, hactual, heq⟩ := callValues?_some_of_wp hwp
  subst actual
  exact hactual

end Exact

end EvalTriple

def Term.Terminates (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (hM : ctx.M = Id := by first | assumption | rfl) : Prop :=
  ∃ value, EvalTriple.Exact.EvaluatesTo ctx env term value hM

/- Two terms are equal at a type when their exact-result Hoare judgments agree under every
environment matching the scope in which they are stated. -/
structure Term.eq (ctx : Ctx) (varCtx : VarCtx) (ty : Ty)
    (t₁ t₂ : Term ctx.primCtx) (hM : ctx.M = Id := by first | assumption | rfl) : Prop where
  hasType₁ : hasType ctx varCtx t₁ ty
  hasType₂ : hasType ctx varCtx t₂ ty
  eq : ∀ env : Env ctx.primCtx, env.Models varCtx → ∀ value,
    EvalTriple.Exact.EvaluatesTo ctx env t₁ value hM ↔
      EvalTriple.Exact.EvaluatesTo ctx env t₂ value hM

def Pr.interp (ctx : Ctx) :
    (ctxTy : Scope Ty) → (ctxTerm : Scope (Term ctx.primCtx)) → Pr (Term ctx.primCtx) →
      (hM : ctx.M = Id := by first | assumption | rfl) → Prop
| ctxTy, ctxTerm, .eq varCtx ty x y, hM =>
  Term.eq ctx (VarCtx.subst ctxTy varCtx) (Ty.subst ctxTy ty)
    (Term.subst ctxTerm x) (Term.subst ctxTerm y) hM
| ctxTy, ctxTerm, .hasType varCtx term ty, _ =>
  Term.hasType ctx (VarCtx.subst ctxTy varCtx) (Term.subst ctxTerm term) (Ty.subst ctxTy ty)
| ctxTy, ctxTerm, .and p q, hM =>
  Pr.interp ctx ctxTy ctxTerm p hM ∧ Pr.interp ctx ctxTy ctxTerm q hM
| ctxTy, ctxTerm, .or p q, hM =>
  Pr.interp ctx ctxTy ctxTerm p hM ∨ Pr.interp ctx ctxTy ctxTerm q hM
| ctxTy, ctxTerm, .implies p q, hM =>
  Pr.interp ctx ctxTy ctxTerm p hM → Pr.interp ctx ctxTy ctxTerm q hM
| ctxTy, ctxTerm, .forallTy name p, hM =>
  ∀ α : Ty, Pr.interp ctx (ctxTy ++ [(name, α)]) ctxTerm p hM
| ctxTy, ctxTerm, .forallTerm name p, hM =>
  ∀ term : Term ctx.primCtx, Pr.interp ctx ctxTy (ctxTerm ++ [(name, term)]) p hM

inductive Pr.Provable (ctx : Ctx)
    (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (proposition : Pr (Term ctx.primCtx))
    (hM : ctx.M = Id := by first | assumption | rfl) : Prop where
| ofProof (proof : Pr.interp ctx ctxTy ctxTerm proposition hM)

namespace EvalTriple

/-- Canonical Id context for the exact singleton adapter. -/
abbrev idCtx (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx Id)
    (blockCtx : BlockCtx primCtx := .empty) : Ctx where
  primCtx := primCtx
  M := Id
  monad := inferInstance
  opCtx := opCtx
  blockCtx := blockCtx
  postShape := .pure
  wpMonad := inferInstance

abbrev IdEvaluatesTo (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx Id)
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (term : Term primCtx)
    (value : Val primCtx) : Prop :=
  EvaluatesTo (idCtx primCtx opCtx blockCtx) env term (Singleton.idPre True)
    (Singleton.idPost (· = value))

namespace State

abbrev EvaluatesFrom (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (machine : Machine.Config primCtx) (initial : σ)
    (value : Val primCtx) (final : σ) (base : List (Frame primCtx)) : Prop :=
  EvalTriple.EvaluatesFrom (Machine.stateCtx primCtx opCtx blockCtx) machine base
    (Singleton.statePre initial) (Singleton.statePost fun result state =>
      result = value ∧ state = final)

abbrev EvaluatesTo (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (term : Term primCtx)
    (initial : σ) (value : Val primCtx) (final : σ) : Prop :=
  EvalTriple.EvaluatesTo (Machine.stateCtx primCtx opCtx blockCtx) env term
    (Singleton.statePre initial) (Singleton.statePost fun result state =>
      result = value ∧ state = final)

/-- Continuation-parametric exact state evaluation for surface terms. This is the state analogue of
`Exact.EvaluatesTo`: the same term result can be resumed through any pending stack suffix. -/
abbrev EvaluatesToK (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (term : Term primCtx)
    (initial : σ) (value : Val primCtx) (final : σ) : Prop :=
  ∀ base : List (Frame primCtx),
    State.EvaluatesFrom primCtx opCtx blockCtx ⟨.eval term, env, base⟩
      initial value final base

abbrev EvaluatesCall (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (name : String) (args : List (Term primCtx))
    (initial : σ) (value : Val primCtx) (final : σ) : Prop :=
  EvalTriple.EvaluatesCall (Machine.stateCtx primCtx opCtx blockCtx) name args
    (Singleton.statePre initial) (Singleton.statePost fun result state =>
      result = value ∧ state = final)

abbrev EvaluatesApply (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (fn : Val primCtx) (vargs : List (Val primCtx))
    (initial : σ) (value : Val primCtx) (final : σ) : Prop :=
  EvalTriple.EvaluatesApply (Machine.stateCtx primCtx opCtx blockCtx) fn vargs
    (Singleton.statePre initial) (Singleton.statePost fun result state =>
      result = value ∧ state = final)

abbrev EvaluatesCallValues (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (name : String) (vargs : List (Val primCtx))
    (initial : σ) (value : Val primCtx) (final : σ) : Prop :=
  EvalTriple.EvaluatesCallValues (Machine.stateCtx primCtx opCtx blockCtx) name vargs
    (Singleton.statePre initial) (Singleton.statePost fun result state =>
      result = value ∧ state = final)

/-- User-facing total evaluator for `StateM` semantics. The state shape is the public ambient state;
machine stuckness is represented by the normal return value `none`. -/
def eval? (primCtx : PrimitiveCtx) (opCtx : OpCtx primCtx (StateM σ))
    (blockCtx : BlockCtx primCtx) (env : Env primCtx) (term : Term primCtx) :
    Std.Do.PredTrans (.arg σ .pure) (Option (Val primCtx)) where
  trans Q := fun initial => ULift.up
    ((∀ value final, State.EvaluatesToK primCtx opCtx blockCtx env term initial value final →
        (Q.1 (some value) final).down) ∧
      ((∀ value final,
          ¬ State.EvaluatesToK primCtx opCtx blockCtx env term initial value final) →
        (Q.1 none initial).down))
  conjunctiveRaw := by
    intro Q₁ Q₂ initial
    dsimp [Std.Do.PredTrans.apply, Std.Do.SPred.bientails, Std.Do.SPred.and]
    constructor
    · intro h
      exact ⟨⟨fun value final hvalue => (h.1 value final hvalue).1,
          fun hnone => (h.2 hnone).1⟩,
        ⟨fun value final hvalue => (h.1 value final hvalue).2,
          fun hnone => (h.2 hnone).2⟩⟩
    · intro h
      exact ⟨fun value final hvalue =>
          ⟨h.1.1 value final hvalue, h.2.1 value final hvalue⟩,
        fun hnone => ⟨h.1.2 hnone, h.2.2 hnone⟩⟩

namespace EvaluatesFrom

private theorem exactStep {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {machine next : Machine.Config primCtx} {initial middle : σ}
    (hstep : (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run
      initial = (some next, middle)) :
    Std.Do.Triple
      (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run
      (Singleton.statePre initial)
      (StepPost (Machine.stateCtx primCtx opCtx blockCtx)
        (fun actual => At (Machine.stateCtx primCtx opCtx blockCtx) next actual
          (Singleton.statePre middle)) Std.Do.ExceptConds.false) := by
  have hstep' : Id.run (StateT.run
      (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run initial) =
      (some next, middle) := hstep
  simp [Std.Do.Triple.iff, Std.Do.wp, StepPost, At, Stuck, hstep']

theorem done {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {value : Val primCtx} {scope : Env primCtx}
    {state : σ} {base : List (Frame primCtx)} :
    State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret value, scope, base⟩ state value state base :=
  EvalTriple.EvaluatesFrom.done (by simp [Singleton.statePost])

theorem step {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {machine next : Machine.Config primCtx}
    {initial middle final : σ} {value : Val primCtx} {base : List (Frame primCtx)}
    (hstep : (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run initial =
      (some next, middle))
    (hnext : State.EvaluatesFrom primCtx opCtx blockCtx
      next middle value final base) :
    State.EvaluatesFrom primCtx opCtx blockCtx machine initial value final base :=
  EvalTriple.EvaluatesFrom.step (exactStep hstep) hnext

theorem bind {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {machine : Machine.Config primCtx}
    {initial middle final : σ} {value finalValue : Val primCtx}
    {base finalBase : List (Frame primCtx)}
    (h : State.EvaluatesFrom primCtx opCtx blockCtx machine initial value middle base)
    (hcont : ∀ scope, State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret value, scope, base⟩ middle finalValue final finalBase) :
    State.EvaluatesFrom primCtx opCtx blockCtx
      machine initial finalValue final finalBase := by
  apply EvalTriple.EvaluatesFrom.bind h
  intro actual scope
  apply Steps.subst (state' := ⟨.ret value, scope, base⟩)
  · intro state hstate
    cases hstate.1
    rfl
  · intro state hstate
    exact hstate.2
  exact hcont scope

theorem call_then {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {name : String} {vargs : List (Val primCtx)}
    {argTys : List Ty} {outTy : Ty} {env : Env primCtx}
    {stack finalBase : List (Frame primCtx)} {initial callFinal final : σ}
    {value finalValue : Val primCtx}
    (hcall : State.EvaluatesCallValues primCtx opCtx blockCtx
      name vargs initial value callFinal)
    (hcont : ∀ scope, State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret value, scope, stack⟩ callFinal finalValue final finalBase) :
    State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.apply (.blockRef name argTys outTy) vargs, env, stack⟩
      initial finalValue final finalBase :=
  bind (EvalTriple.EvaluatesApply.blockRef hcall env stack) hcont

theorem return_to_call {primCtx : PrimitiveCtx} {opCtx : OpCtx primCtx (StateM σ)}
    {blockCtx : BlockCtx primCtx} {name : String} {callerEnv scope : Env primCtx}
    {stack : List (Frame primCtx)} {state : σ} {value : Val primCtx} :
    State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret value, scope, .call name callerEnv :: stack⟩ state value state stack :=
  EvalTriple.EvaluatesFrom.callReturn (by simp [Singleton.statePost])

theorem return_through_done_call {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {callerEnv scope opEnv : Env primCtx}
    {stack : List (Frame primCtx)} {state : σ} {value : Val primCtx} :
    State.EvaluatesFrom primCtx opCtx blockCtx
      ⟨.ret value, scope,
        .opBody (fun | some value => .done value | none => .fail) [] opEnv ::
          .call name callerEnv :: stack⟩ state value state stack := by
  apply step (middle := state)
  · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp]
    rfl
  exact return_to_call

private theorem steps_toNsteps {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {machine : Machine.Config primCtx} {initial final : σ}
    {value : Val primCtx} {base : List (Frame primCtx)}
    {P : Assertion (Machine.stateCtx primCtx opCtx blockCtx)}
    (h : Steps (Machine.stateCtx primCtx opCtx blockCtx)
      (Singleton.statePost fun result state => result = value ∧ state = final).2
      (ReturnsTo (Machine.stateCtx primCtx opCtx blockCtx) base
        (Singleton.statePost fun result state => result = value ∧ state = final))
      machine P)
    (hP : (P initial).down) :
    ∃ fuel scope,
      (Machine.nsteps (Machine.stateCtx primCtx opCtx blockCtx) fuel machine).run initial =
        (some ⟨.ret value, scope, base⟩, final) := by
  revert hP
  induction h using @Steps.rec (Machine.stateCtx primCtx opCtx blockCtx)
      (Singleton.statePost fun result state => result = value ∧ state = final).2
      (ReturnsTo (Machine.stateCtx primCtx opCtx blockCtx) base
        (Singleton.statePost fun result state => result = value ∧ state = final)) generalizing initial with
  | done hdone =>
      intro hpre
      cases hdone with
      | @intro returned scope terminalP hpost =>
          have hq : returned = value ∧ initial = final :=
            hpost initial hpre
          rcases hq with ⟨rfl, rfl⟩
          exact ⟨0, scope, rfl⟩
  | @step state stepP next head tail ih =>
      intro hpre
      have hhead := (Std.Do.Triple.iff.mp head) initial hpre
      simp only [Std.Do.wp, Std.Do.PredTrans.apply_pushArg,
        Std.Do.PredTrans.apply_Pure_pure] at hhead
      cases hstep : (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) state).run initial with
      | mk next? middle =>
          simp only [StateT.run] at hhead
          rw [hstep] at hhead
          cases next? with
          | none => simp [Id.run, StepPost, Stuck] at hhead
          | some nextState =>
              have hnext : (next nextState middle).down := by
                simpa [Id.run, StepPost] using hhead
              obtain ⟨fuel, scope, hrun⟩ := ih nextState hnext
              refine ⟨fuel + 1, scope, ?_⟩
              change Id.run (((Machine.step (Machine.stateCtx primCtx opCtx blockCtx) state >>=
                Machine.nsteps (Machine.stateCtx primCtx opCtx blockCtx) fuel).run initial)) = _
              rw [Machine.optionT_state_bind_run]
              rw [hstep]
              exact hrun
  | @split ι state splitP cases cover branches ih =>
      intro hpre
      have hcover := cover initial hpre
      simp at hcover
      obtain ⟨i, hi⟩ := hcover
      exact ih i hi
  | @subst state state' substP invariant eq_state hpre' next ih =>
      intro hpre
      have heq := eq_state initial hpre
      simp at heq
      subst state'
      exact ih (hpre' initial hpre)

theorem toNsteps {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {machine : Machine.Config primCtx} {initial final : σ}
    {value : Val primCtx} {base : List (Frame primCtx)}
    (h : State.EvaluatesFrom primCtx opCtx blockCtx machine initial value final base) :
    ∃ fuel scope,
      (Machine.nsteps (Machine.stateCtx primCtx opCtx blockCtx) fuel machine).run initial =
        (some ⟨.ret value, scope, base⟩, final) := by
  change Steps (Machine.stateCtx primCtx opCtx blockCtx)
      (Singleton.statePost fun result state => result = value ∧ state = final).2
      (ReturnsTo (Machine.stateCtx primCtx opCtx blockCtx) base
        (Singleton.statePost fun result state => result = value ∧ state = final))
      machine (Singleton.statePre initial) at h
  exact steps_toNsteps h rfl

/-- Construct a logical derivation from one successful bounded execution. The bound is executable
evidence only and does not occur in the resulting judgment. -/
theorem of_evalConfigFuel {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fuel : Nat} {machine : Machine.Config primCtx} {initial final : σ}
    {value : Val primCtx}
    (hrun : (Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx)
      fuel machine).run initial = (some value, final)) :
    State.EvaluatesFrom primCtx opCtx blockCtx machine initial value final [] := by
  induction fuel generalizing machine initial with
  | zero =>
      cases hresult : Machine.result? machine with
      | none =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          change Id.run ((pure none : StateM σ (Option (Val primCtx))) initial) =
            (some value, final) at hrun
          rw [Machine.stateM_pure_run] at hrun
          simp at hrun
      | some result =>
          cases machine with
          | mk control scope stack =>
              cases control <;> cases stack <;>
                simp [Machine.result?] at hresult
              subst result
              simp [Machine.evalConfigFuel, Machine.result?] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              exact done
  | succ fuel ih =>
      cases hresult : Machine.result? machine with
      | some result =>
          cases machine with
          | mk control scope stack =>
              cases control <;> cases stack <;>
                simp [Machine.result?] at hresult
              subst result
              simp [Machine.evalConfigFuel, Machine.result?] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              exact done
      | none =>
          simp only [Machine.evalConfigFuel, hresult] at hrun
          change Id.run (((Machine.step
            (Machine.stateCtx primCtx opCtx blockCtx) machine >>=
              Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx) fuel).run
                initial)) = (some value, final) at hrun
          rw [Machine.optionT_state_bind_run] at hrun
          cases hstep : (Machine.step
              (Machine.stateCtx primCtx opCtx blockCtx) machine).run initial with
          | mk next? middle =>
              change Id.run ((Machine.step
                (Machine.stateCtx primCtx opCtx blockCtx) machine).run initial) =
                  (next?, middle) at hstep
              rw [hstep] at hrun
              cases next? with
              | none =>
                  change (none, middle) = (some value, final) at hrun
                  simp at hrun
              | some next =>
                  change (Machine.evalConfigFuel
                    (Machine.stateCtx primCtx opCtx blockCtx) fuel next).run middle =
                      (some value, final) at hrun
                  exact step hstep (ih hrun)

end EvaluatesFrom

private theorem evalConfigFuel_run_of_result {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (fuel : Nat) (machine : Machine.Config primCtx) (initial : σ) (value : Val primCtx)
    (hresult : Machine.result? machine = some value) :
    (Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx) fuel machine).run initial =
      (some value, initial) := by
  cases fuel <;> simp only [Machine.evalConfigFuel, hresult] <;> rfl

private theorem evalConfigFuel_run_zero_of_none {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    (machine : Machine.Config primCtx) (initial : σ)
    (hresult : Machine.result? machine = none) :
    (Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx) 0 machine).run initial =
      (none, initial) := by
  simp only [Machine.evalConfigFuel, hresult]
  rfl

private theorem evalConfigFuel_run_unique {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {machine : Machine.Config primCtx} {initial final₁ final₂ : σ}
    {fuel₁ fuel₂ : Nat} {value₁ value₂ : Val primCtx}
    (h₁ : (Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx)
      fuel₁ machine).run initial = (some value₁, final₁))
    (h₂ : (Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx)
      fuel₂ machine).run initial = (some value₂, final₂)) :
    value₁ = value₂ ∧ final₁ = final₂ := by
  induction fuel₁ generalizing fuel₂ machine initial with
  | zero =>
      cases hresult : Machine.result? machine with
      | none =>
          rw [evalConfigFuel_run_zero_of_none machine initial hresult] at h₁
          have hfalse := congrArg Prod.fst h₁
          simp at hfalse
      | some result =>
          rw [evalConfigFuel_run_of_result 0 machine initial result hresult] at h₁
          rw [evalConfigFuel_run_of_result fuel₂ machine initial result hresult] at h₂
          obtain ⟨rfl, rfl⟩ := h₁
          obtain ⟨rfl, rfl⟩ := h₂
          exact ⟨rfl, rfl⟩
  | succ fuel₁ ih =>
      cases hresult : Machine.result? machine with
      | some result =>
          rw [evalConfigFuel_run_of_result (fuel₁ + 1) machine initial result hresult] at h₁
          rw [evalConfigFuel_run_of_result fuel₂ machine initial result hresult] at h₂
          obtain ⟨rfl, rfl⟩ := h₁
          obtain ⟨rfl, rfl⟩ := h₂
          exact ⟨rfl, rfl⟩
      | none =>
          simp only [Machine.evalConfigFuel, hresult] at h₁
          change Id.run (((Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine >>=
            Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx) fuel₁).run
              initial)) = (some value₁, final₁) at h₁
          rw [Machine.optionT_state_bind_run] at h₁
          cases hstep : (Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run
              initial with
          | mk next? middle =>
              change Id.run ((Machine.step (Machine.stateCtx primCtx opCtx blockCtx) machine).run
                initial) = (next?, middle) at hstep
              rw [hstep] at h₁
              cases next? with
              | none =>
                  change (none, middle) = (some value₁, final₁) at h₁
                  have hfalse := congrArg Prod.fst h₁
                  simp at hfalse
              | some nextState =>
                  cases fuel₂ with
                  | zero =>
                      rw [evalConfigFuel_run_zero_of_none machine initial hresult] at h₂
                      have hfalse := congrArg Prod.fst h₂
                      simp at hfalse
                  | succ fuel₂ =>
                      simp only [Machine.evalConfigFuel, hresult] at h₂
                      change Id.run (((Machine.step
                        (Machine.stateCtx primCtx opCtx blockCtx) machine >>=
                          Machine.evalConfigFuel (Machine.stateCtx primCtx opCtx blockCtx)
                            fuel₂).run initial)) = (some value₂, final₂) at h₂
                      rw [Machine.optionT_state_bind_run] at h₂
                      rw [hstep] at h₂
                      exact ih h₁ h₂

namespace EvaluatesTo

theorem of_evaluatesFrom {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesFrom primCtx opCtx blockCtx
      (Machine.start env term) initial value final []) :
    State.EvaluatesTo primCtx opCtx blockCtx env term initial value final :=
  h

theorem unique {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final₁ final₂ : σ}
    {value₁ value₂ : Val primCtx}
    (h₁ : State.EvaluatesTo primCtx opCtx blockCtx env term initial value₁ final₁)
    (h₂ : State.EvaluatesTo primCtx opCtx blockCtx env term initial value₂ final₂) :
    value₁ = value₂ ∧ final₁ = final₂ := by
  obtain ⟨fuel₁, scope₁, hsteps₁⟩ := State.EvaluatesFrom.toNsteps h₁
  obtain ⟨fuel₂, scope₂, hsteps₂⟩ := State.EvaluatesFrom.toNsteps h₂
  have hrun₁ := Machine.evalConfigFuel_run_of_nsteps_result primCtx opCtx blockCtx
    fuel₁ (Machine.start env term) initial final₁ value₁ scope₁ hsteps₁
  have hrun₂ := Machine.evalConfigFuel_run_of_nsteps_result primCtx opCtx blockCtx
    fuel₂ (Machine.start env term) initial final₂ value₂ scope₂ hsteps₂
  exact evalConfigFuel_run_unique hrun₁ hrun₂

end EvaluatesTo

namespace EvaluatesToK

theorem to_evaluatesTo {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesToK primCtx opCtx blockCtx env term initial value final) :
    State.EvaluatesTo primCtx opCtx blockCtx env term initial value final := by
  exact h []

theorem unique {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final₁ final₂ : σ}
    {value₁ value₂ : Val primCtx}
    (h₁ : State.EvaluatesToK primCtx opCtx blockCtx env term initial value₁ final₁)
    (h₂ : State.EvaluatesToK primCtx opCtx blockCtx env term initial value₂ final₂) :
    value₁ = value₂ ∧ final₁ = final₂ :=
  State.EvaluatesTo.unique h₁.to_evaluatesTo h₂.to_evaluatesTo

end EvaluatesToK

namespace EvaluatesApply

theorem unique {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {fn : Val primCtx} {args : List (Val primCtx)} {initial final₁ final₂ : σ}
    {value₁ value₂ : Val primCtx}
    (h₁ : State.EvaluatesApply primCtx opCtx blockCtx fn args initial value₁ final₁)
    (h₂ : State.EvaluatesApply primCtx opCtx blockCtx fn args initial value₂ final₂) :
    value₁ = value₂ ∧ final₁ = final₂ := by
  obtain ⟨fuel₁, scope₁, hsteps₁⟩ := State.EvaluatesFrom.toNsteps (h₁ [] [])
  obtain ⟨fuel₂, scope₂, hsteps₂⟩ := State.EvaluatesFrom.toNsteps (h₂ [] [])
  have hrun₁ := Machine.evalConfigFuel_run_of_nsteps_result primCtx opCtx blockCtx
    fuel₁ ⟨.apply fn args, [], []⟩ initial final₁ value₁ scope₁ hsteps₁
  have hrun₂ := Machine.evalConfigFuel_run_of_nsteps_result primCtx opCtx blockCtx
    fuel₂ ⟨.apply fn args, [], []⟩ initial final₂ value₂ scope₂ hsteps₂
  exact evalConfigFuel_run_unique hrun₁ hrun₂

end EvaluatesApply

namespace EvaluatesCallValues

theorem unique {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {name : String} {args : List (Val primCtx)} {initial final₁ final₂ : σ}
    {value₁ value₂ : Val primCtx}
    (h₁ : State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value₁ final₁)
    (h₂ : State.EvaluatesCallValues primCtx opCtx blockCtx name args initial value₂ final₂) :
    value₁ = value₂ ∧ final₁ = final₂ :=
  State.EvaluatesApply.unique
    (EvalTriple.EvaluatesApply.blockRef
      (argTys := args.map Val.ty) (outTy := value₁.ty) h₁)
    (EvalTriple.EvaluatesApply.blockRef
      (argTys := args.map Val.ty) (outTy := value₁.ty) h₂)

end EvaluatesCallValues

theorem eval?_triple_of_evaluatesTo {primCtx : PrimitiveCtx}
    {opCtx : OpCtx primCtx (StateM σ)} {blockCtx : BlockCtx primCtx}
    {env : Env primCtx} {term : Term primCtx} {initial final : σ}
    {value : Val primCtx}
    (h : State.EvaluatesToK primCtx opCtx blockCtx env term initial value final)
    (Q : Std.Do.PostCond (Option (Val primCtx)) (.arg σ .pure)) :
    Std.Do.Triple (eval? primCtx opCtx blockCtx env term)
      (fun state => Std.Do.SPred.pure
        (state = initial ∧ (Q.1 (some value) final).down)) Q := by
  rw [Std.Do.Triple.iff, Std.Do.SPred.entails_1]
  intro state hpre
  change state = initial ∧ (Q.1 (some value) final).down at hpre
  rcases hpre with ⟨hstate, hQ⟩
  subst state
  change ((∀ actual actualFinal,
      State.EvaluatesToK primCtx opCtx blockCtx env term initial actual actualFinal →
        (Q.1 (some actual) actualFinal).down) ∧
    ((∀ actual actualFinal,
      ¬ State.EvaluatesToK primCtx opCtx blockCtx env term initial actual actualFinal) →
        (Q.1 none initial).down))
  constructor
  · intro actual actualFinal hactual
    obtain ⟨hvalue, hfinal⟩ := EvaluatesToK.unique hactual h
    subst actual
    subst actualFinal
    exact hQ
  · intro hnone
    exact (hnone value final h).elim

end State

end EvalTriple

protected abbrev EvaluatesFrom (ctx : Ctx) (state : Machine.Config ctx.primCtx)
    (base : List (Frame ctx.primCtx)) (P : EvalTriple.Assertion ctx)
    (Q : EvalTriple.PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvalTriple.EvaluatesFrom ctx state base P Q

protected abbrev EvaluatesTo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx)
    (P : EvalTriple.Assertion ctx) (Q : EvalTriple.PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvalTriple.EvaluatesTo ctx env term P Q

protected abbrev EvaluatesApply (ctx : Ctx) (fn : Val ctx.primCtx)
    (vargs : List (Val ctx.primCtx)) (P : EvalTriple.Assertion ctx)
    (Q : EvalTriple.PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvalTriple.EvaluatesApply ctx fn vargs P Q

protected abbrev EvaluatesCall (ctx : Ctx) (name : String)
    (args : List (Term ctx.primCtx)) (P : EvalTriple.Assertion ctx)
    (Q : EvalTriple.PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvalTriple.EvaluatesCall ctx name args P Q

protected abbrev EvaluatesCallValues (ctx : Ctx) (name : String)
    (vargs : List (Val ctx.primCtx)) (P : EvalTriple.Assertion ctx)
    (Q : EvalTriple.PostCond ctx (Val ctx.primCtx)) : Prop :=
  EvalTriple.EvaluatesCallValues ctx name vargs P Q

namespace EvaluatesFrom

export EvalTriple.EvaluatesFrom
  (done consequence bind step pureStep callReturn)

end EvaluatesFrom

namespace EvaluatesTo

export EvalTriple.EvaluatesTo (consequence)

end EvaluatesTo

namespace EvaluatesApply

export EvalTriple.EvaluatesApply (consequence blockRef)

end EvaluatesApply

namespace EvaluatesCall

export EvalTriple.EvaluatesCall (consequence)

end EvaluatesCall

namespace EvaluatesCallValues

export EvalTriple.EvaluatesCallValues (of_body consequence)

end EvaluatesCallValues

end Zag
