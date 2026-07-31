import Lang.AutoCorres.NonDetMonadEx
import Lang.SSA

/-!
# Cross-state correspondence

Corresponds to [`tools/autocorres/CorresXF.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/CorresXF.thy).
-/

namespace Zag.Lang.AutoCorres

universe u v w x y z

/--
Upstream `corresXF`, with its argument direction unchanged: `A` is the
abstract target and `C` is the concrete source.
-/
def CorresXF {CS : Type u} {AS : Type v} {CR : Type w} {AR : Type x}
    {CE : Type y} {AE : Type z}
    (stateMap : CS → AS)
    (normalMap : CR → CS → AR)
    (exceptionMap : CE → CS → AE)
    (precondition : CS → Prop)
    (A : Nondet AS (Except AE AR))
    (C : Nondet CS (Except CE CR)) : Prop :=
  ∀ state, precondition state ∧ ¬ (A (stateMap state)).failed →
    (∀ result post, (result, post) ∈ (C state).results →
      ((match result with
        | Except.error exception => Except.error (exceptionMap exception post)
        | Except.ok value => Except.ok (normalMap value post)), stateMap post) ∈
        (A (stateMap state)).results) ∧
    ¬ (C state).failed

namespace CorresXF

/-- Identity correspondence, for any precondition. -/
theorem refl {σ : Type u} {ε : Type v} {α : Type w}
    (precondition : σ → Prop) (m : Nondet σ (Except ε α)) :
    CorresXF id (fun value _ => value) (fun exception _ => exception)
      precondition m m := by
  intro state hypothesis
  refine ⟨?_, hypothesis.2⟩
  intro result post member
  cases result <;> exact member

/-- Compose adjacent correspondences and their state, result, and exception maps. -/
theorem merge
    {CS : Type u} {BS : Type v} {AS : Type w}
    {CR : Type x} {BR : Type y} {AR : Type z}
    {CE : Type x} {BE : Type y} {AE : Type z}
    {stateMap₁ : CS → BS} {normalMap₁ : CR → CS → BR}
    {exceptionMap₁ : CE → CS → BE} {precondition₁ : CS → Prop}
    {stateMap₂ : BS → AS} {normalMap₂ : BR → BS → AR}
    {exceptionMap₂ : BE → BS → AE} {precondition₂ : BS → Prop}
    {A : Nondet AS (Except AE AR)} {B : Nondet BS (Except BE BR)}
    {C : Nondet CS (Except CE CR)}
    (hCB : CorresXF stateMap₁ normalMap₁ exceptionMap₁ precondition₁ B C)
    (hBA : CorresXF stateMap₂ normalMap₂ exceptionMap₂ precondition₂ A B) :
    CorresXF (stateMap₂ ∘ stateMap₁)
      (fun value state => normalMap₂ (normalMap₁ value state) (stateMap₁ state))
      (fun exception state =>
        exceptionMap₂ (exceptionMap₁ exception state) (stateMap₁ state))
      (fun state => precondition₁ state ∧ precondition₂ (stateMap₁ state)) A C := by
  intro state hypothesis
  have middle := hBA (stateMap₁ state) ⟨hypothesis.1.2, hypothesis.2⟩
  have source := hCB state ⟨hypothesis.1.1, middle.2⟩
  refine ⟨?_, source.2⟩
  intro result post member
  have middleMember := source.1 result post member
  cases result with
  | error exception =>
      simpa [Function.comp_def] using
        middle.1 (Except.error (exceptionMap₁ exception post)) (stateMap₁ post)
          middleMember
  | ok value =>
      simpa [Function.comp_def] using
        middle.1 (Except.ok (normalMap₁ value post)) (stateMap₁ post) middleMember

/-- Conventional transitive form of `merge`, with target link first. -/
theorem trans
    {CS : Type u} {BS : Type v} {AS : Type w}
    {CR : Type x} {BR : Type y} {AR : Type z}
    {CE : Type x} {BE : Type y} {AE : Type z}
    {stateMap₁ : CS → BS} {normalMap₁ : CR → CS → BR}
    {exceptionMap₁ : CE → CS → BE} {precondition₁ : CS → Prop}
    {stateMap₂ : BS → AS} {normalMap₂ : BR → BS → AR}
    {exceptionMap₂ : BE → BS → AE} {precondition₂ : BS → Prop}
    {A : Nondet AS (Except AE AR)} {B : Nondet BS (Except BE BR)}
    {C : Nondet CS (Except CE CR)}
    (hBA : CorresXF stateMap₂ normalMap₂ exceptionMap₂ precondition₂ A B)
    (hCB : CorresXF stateMap₁ normalMap₁ exceptionMap₁ precondition₁ B C) :
    CorresXF (stateMap₂ ∘ stateMap₁)
      (fun value state => normalMap₂ (normalMap₁ value state) (stateMap₁ state))
      (fun exception state =>
        exceptionMap₂ (exceptionMap₁ exception state) (stateMap₁ state))
      (fun state => precondition₁ state ∧ precondition₂ (stateMap₁ state)) A C :=
  merge hCB hBA

end CorresXF

/-! ## Closed SSA bridge -/

/-
The AutoCorres-specific SSA bridge. It emits one closed call into `PrimFuncCtx`;
future structural lowering may split a shallow program into multiple monadic
functions, but this bridge does not claim node-by-node lowering.
-/
namespace SSABridge

/-- A primitive context factory using AutoCorres nondeterministic state semantics. -/
abbrev primitiveCtx (State : Type) (primitives : List Primitive) : PrimitiveCtx where
  prims := primitives
  M := Nondet State
  monad := inferInstance

/-- The fixed primitive name used for a bridge result. -/
abbrev outcomeName : String := "AutoCorres.Outcome"

/-- The fixed SSA type of a bridge result. -/
abbrev outcomeTy : Ty := .prim outcomeName

/-- The sole primitive in a closed bridge context. -/
abbrev outcomePrimitive (Outcome : Type) [Repr Outcome] : Primitive :=
  .of outcomeName Outcome

/--
The closed bridge context. `State` and `Outcome` are restricted to `Type 0`
because Zag's `PrimitiveCtx` stores primitive types and its monad at `Type`.
-/
abbrev primCtx (State Outcome : Type) [Repr Outcome] : PrimitiveCtx :=
  primitiveCtx State [outcomePrimitive Outcome]

@[simp] theorem outcomeTy_type (State Outcome : Type) [Repr Outcome] :
    Ty.type (primCtx State Outcome) outcomeTy = Outcome := by
  simp [Ty.type, PrimitiveCtx.get?]

/-- Preserve every result and failure while making successful outcomes present. -/
def suspend (program : Nondet State Outcome) : Nondet State (Option Outcome) :=
  bind program (fun outcome => pure (some outcome))

@[simp] theorem mem_suspend_some {program : Nondet State Outcome}
    {state post : State} {outcome : Outcome} :
    (some outcome, post) ∈ (suspend program state).results ↔
      (outcome, post) ∈ (program state).results := by
  simp [suspend]

@[simp] theorem not_mem_suspend_none {program : Nondet State Outcome}
    {state post : State} :
    ¬ (none, post) ∈ (suspend program state).results := by
  simp [suspend]

@[simp] theorem failed_suspend {program : Nondet State Outcome} {state : State} :
    (suspend program state).failed ↔ (program state).failed := by
  constructor
  · rintro (failed | ⟨outcome, post, _member, failed⟩)
    · exact failed
    · simp [pure] at failed
  · exact Or.inl

private theorem cast_suspended_cancel (typeEq : Source = Target)
    (program : Nondet State (Option Target)) :
    cast (congrArg (fun type => Option (Nondet State (Option type))) typeEq)
      (some (cast
        (congrArg (fun type => Nondet State (Option type)) typeEq.symm) program)) =
      some program := by
  cases typeEq
  rfl

/-- The name of the closed program primitive function. -/
def runName : String := "run"

/-- A nullary monadic primitive whose interpretation is exactly `suspend program`. -/
def run (program : Nondet State Outcome) [Repr Outcome] :
    PrimFunc (primCtx State Outcome) where
  args := []
  out := outcomeName
  monadic := true
  hprim := by simp
  interp := fun _ => some (Val.mk (.m outcomeTy)
    (Ty.ofM (primCtx State Outcome) outcomeTy
      (cast (by simp only [outcomeTy_type]) (suspend program))))

/-- The context generated for one closed AutoCorres program. -/
abbrev generatedCtx (program : Nondet State Outcome) [Repr Outcome] : Ctx where
  primCtx := primCtx State Outcome
  primFuncCtx := [(runName, run program)]
  opCtx := []

/-- The closed SSA expression invoking the generated `run` primitive. -/
def generatedExpr (program : Nondet State Outcome) [Repr Outcome] :
    Zag.Lang.SSA.SSAExpr (generatedCtx program).primCtx :=
  .ret (.call (.primFunc runName) [])

/-- Evaluation of the generated closed call is exactly the suspended program. -/
theorem eval_generated (program : Nondet State Outcome) [Repr Outcome] :
    cast (by simp only [outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? (generatedCtx program) [] outcomeTy
        (generatedExpr program)) = some (suspend program) := by
  simp [Zag.Lang.SSA.SSAExpr.evalM?, Zag.Lang.SSA.SSAExpr.eval,
    Zag.Lang.SSA.SSAExpr.toTerm?, Zag.Lang.SSA.SSAExpr.valueToTerm?,
    Zag.Lang.SSA.SSAExpr.valuesToTerms?, Zag.Lang.SSA.SSAValue.primFunc,
    generatedExpr, generatedCtx, runName, run, Term.eval, Term.evalGo,
    Term.evalList, PrimFuncCtx.get?, PrimFunc.apply, PrimFunc.outTy, Val.as?]
  exact cast_suspended_cancel (outcomeTy_type State Outcome) (suspend program)

/-- A shallow program packaged with its canonical closed SSA context and call. -/
structure ClosedProgram (State Outcome : Type) [Repr Outcome] where
  program : Nondet State Outcome

abbrev ClosedProgram.ctx [Repr Outcome] (closed : ClosedProgram State Outcome) : Ctx :=
  generatedCtx closed.program

abbrev ClosedProgram.expr [Repr Outcome] (closed : ClosedProgram State Outcome) :
    Zag.Lang.SSA.SSAExpr closed.ctx.primCtx :=
  generatedExpr closed.program

/-- The packaged expression retains the exact closed-call evaluation theorem. -/
theorem ClosedProgram.eval_exact [Repr Outcome]
    (closed : ClosedProgram State Outcome) :
    cast (by simp only [outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? closed.ctx [] outcomeTy closed.expr) =
        some (suspend closed.program) :=
  eval_generated closed.program

/--
An exact semantic refinement between two closed SSA bridge endpoints. The SSA
expressions remain closed primitive calls; `corres` relates their packaged
shallow programs without asserting a structural lowering.
-/
structure Refinement
    {CS CE CR AS AE AR : Type}
    [Repr (Except CE CR)] [Repr (Except AE AR)]
    (source : ClosedProgram CS (Except CE CR))
    (target : ClosedProgram AS (Except AE AR)) where
  stateMap : CS → AS
  normalMap : CR → CS → AR
  exceptionMap : CE → CS → AE
  precondition : CS → Prop
  corres : Zag.Lang.AutoCorres.CorresXF stateMap normalMap exceptionMap
    precondition target.program source.program

namespace Refinement

/-- Package an exact shallow correspondence as a closed SSA endpoint refinement. -/
def ofCorresXF
    {CS CE CR AS AE AR : Type}
    [Repr (Except CE CR)] [Repr (Except AE AR)]
    {source : ClosedProgram CS (Except CE CR)}
    {target : ClosedProgram AS (Except AE AR)}
    (stateMap : CS → AS) (normalMap : CR → CS → AR)
    (exceptionMap : CE → CS → AE) (precondition : CS → Prop)
    (corres : Zag.Lang.AutoCorres.CorresXF stateMap normalMap exceptionMap
      precondition target.program source.program) :
    Refinement source target :=
  ⟨stateMap, normalMap, exceptionMap, precondition, corres⟩

/-- The source SSA endpoint evaluates exactly to its suspended shallow program. -/
theorem source_eval_exact
    {CS CE CR AS AE AR : Type}
    [Repr (Except CE CR)] [Repr (Except AE AR)]
    {source : ClosedProgram CS (Except CE CR)}
    {target : ClosedProgram AS (Except AE AR)}
    (_refinement : Refinement source target) :
    cast (by simp only [outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? source.ctx [] outcomeTy source.expr) =
        some (suspend source.program) :=
  source.eval_exact

/-- The target SSA endpoint evaluates exactly to its suspended shallow program. -/
theorem target_eval_exact
    {CS CE CR AS AE AR : Type}
    [Repr (Except CE CR)] [Repr (Except AE AR)]
    {source : ClosedProgram CS (Except CE CR)}
    {target : ClosedProgram AS (Except AE AR)}
    (_refinement : Refinement source target) :
    cast (by simp only [outcomeTy_type])
      (Zag.Lang.SSA.SSAExpr.evalM? target.ctx [] outcomeTy target.expr) =
        some (suspend target.program) :=
  target.eval_exact

end Refinement

end SSABridge

end Zag.Lang.AutoCorres
