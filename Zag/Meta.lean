import Lean.Elab.Tactic
import Zag.Meta.Language

namespace Zag

structure Refinement (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    {E : Type} [Language ctx.primCtx E] (goal : Pr E) where
  goals : List (Pr E)
  prove : (∀ subgoal, subgoal ∈ goals → Language.Provable ctx ctxTy ctxTerm subgoal) →
    Language.Provable ctx ctxTy ctxTerm goal

abbrev Tactic (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E] :=
  (goal : Pr E) → Refinement ctx ctxTy ctxTerm goal

abbrev Tactic? (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E] :=
  (goal : Pr E) → Option (Refinement ctx ctxTy ctxTerm goal)

namespace Refinement

variable {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E]

def lift {goal : Pr E} (proof : Language.Provable ctx ctxTy ctxTerm goal) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := []
  prove := fun _ => proof

def stuck (goal : Pr E) : Refinement ctx ctxTy ctxTerm goal where
  goals := [goal]
  prove := fun proveSubgoals => proveSubgoals goal (by simp)

theorem toProvable {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal)
    (closed : refinement.goals = []) : Language.Provable ctx ctxTy ctxTerm goal := by
  apply refinement.prove
  intro subgoal hsubgoal
  rw [closed] at hsubgoal
  cases hsubgoal

inductive InterpretsGoals (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx)) :
    List (Pr (Term ctx.primCtx)) → Prop where
  | nil : InterpretsGoals ctx ctxTy ctxTerm []
  | cons {goal : Pr (Term ctx.primCtx)} {rest : List (Pr (Term ctx.primCtx))} :
      Pr.interp ctx ctxTy ctxTerm goal → InterpretsGoals ctx ctxTy ctxTerm rest →
      InterpretsGoals ctx ctxTy ctxTerm (goal :: rest)

theorem InterpretsGoals.get {goals : List (Pr (Term ctx.primCtx))}
    (interps : InterpretsGoals ctx ctxTy ctxTerm goals) {goal : Pr (Term ctx.primCtx)}
    (hgoal : goal ∈ goals) : Pr.interp ctx ctxTy ctxTerm goal := by
  induction interps with
  | nil => simp at hgoal
  | cons head _ ih =>
      simp only [List.mem_cons] at hgoal
      cases hgoal with
      | inl h => exact h ▸ head
      | inr h => exact ih h

theorem sound {goal : Pr (Term ctx.primCtx)}
    (refinement : Refinement ctx ctxTy ctxTerm goal)
    (subgoals : InterpretsGoals ctx ctxTy ctxTerm refinement.goals) :
    Pr.interp ctx ctxTy ctxTerm goal := by
  have proof := refinement.prove fun subgoal hsubgoal => by
    simp only [Language.Provable_term]
    exact .ofProof (subgoals.get hsubgoal)
  simp only [Language.Provable_term] at proof
  cases proof with
  | ofProof result => exact result

def refine {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal)
    (next : ∀ subgoal, subgoal ∈ refinement.goals → Refinement ctx ctxTy ctxTerm subgoal) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := refinement.goals.attach.flatMap fun subgoal =>
    (next subgoal.val subgoal.property).goals
  prove := by
    intro proveGenerated
    apply refinement.prove
    intro subgoal hsubgoal
    apply (next subgoal hsubgoal).prove
    intro generated hgenerated
    apply proveGenerated
    exact List.mem_flatMap.mpr ⟨⟨subgoal, hsubgoal⟩, by simp, hgenerated⟩

def andThen {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal)
    (next : Tactic ctx ctxTy ctxTerm E) : Refinement ctx ctxTy ctxTerm goal :=
  refinement.refine fun subgoal _ => next subgoal

/- The refinement loses no provability: a provable goal only ever generates provable subgoals.
  In sequent-calculus terms this is *invertibility* of the rule, and it is the converse of the
  soundness carried by the `prove` field.

  This is NOT completeness, and must not be read as such: `stuck` satisfies it (see
  `stuck_invertible`), so the identity tactic is invertible. It says the refinement never
  turns a provable goal into an unprovable one -- not that it makes any progress.
  For "provable goals actually get closed", see `Tactic.CompleteOn`. -/
def invertible {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal) : Prop :=
  Language.Provable ctx ctxTy ctxTerm goal →
    ∀ subgoal, subgoal ∈ refinement.goals → Language.Provable ctx ctxTy ctxTerm subgoal

theorem lift_invertible {goal : Pr E} (proof : Language.Provable ctx ctxTy ctxTerm goal) :
    invertible (lift proof) := by
  intro _ subgoal hsubgoal
  simp [lift] at hsubgoal

theorem stuck_invertible (goal : Pr E) :
    invertible (stuck (ctx := ctx) (ctxTy := ctxTy) (ctxTerm := ctxTerm) goal) := by
  intro hgoal subgoal hsubgoal
  simp [stuck] at hsubgoal
  exact hsubgoal ▸ hgoal

theorem refine_invertible {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal)
    (next : ∀ subgoal, subgoal ∈ refinement.goals → Refinement ctx ctxTy ctxTerm subgoal)
    (hrefinement : invertible refinement)
    (hnext : ∀ subgoal hsubgoal, invertible (next subgoal hsubgoal)) :
    invertible (refinement.refine next) := by
  intro hgoal generated hgenerated
  rcases List.mem_flatMap.mp hgenerated with ⟨attached, _hattached, hgeneratedNext⟩
  rcases attached with ⟨subgoal, hsubgoal⟩
  exact hnext subgoal hsubgoal (hrefinement hgoal subgoal hsubgoal) generated hgeneratedNext

end Refinement

open Lean Elab Tactic Meta

structure RefinementNormalizeAttribute where
  attr : AttributeImpl
  ext : PersistentEnvExtension Name Name (Array Name)
deriving Inhabited

initialize refinementNormalizeAttr : RefinementNormalizeAttribute ← do
  let ext ← registerPersistentEnvExtension {
    name := `refinementNormalizeExtension
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := fun entries name => entries.push name
    exportEntriesFn := fun entries => entries
  }
  let attr : AttributeImpl := {
    name := `refinement_normalize
    descr := "register a semantic rewrite used to normalize reflected refinement subgoals"
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `refinement_normalize kind
      modifyEnv fun env => ext.addEntry env decl
  }
  registerBuiltinAttribute attr
  pure { attr, ext }

def RefinementNormalizeAttribute.getEntries (attr : RefinementNormalizeAttribute)
    (env : Environment) : Array Name :=
  let state := attr.ext.toEnvExtension.getState env
  state.importedEntries.flatMap id ++ state.state

private partial def expandRefinementGoals (goal : MVarId) : TacticM (List MVarId) := do
  let target ← instantiateMVars (← goal.getType)
  let args := target.getAppArgs
  let goals ← withTransparency .all do whnf args.back!
  let target := mkAppN target.getAppFn (args.pop.push goals)
  let goal ← withTransparency .all do goal.change target
  try
    let generated ← goal.apply (mkConst ``Refinement.InterpretsGoals.cons)
    match generated with
    | [head, tail] => return head :: (← expandRefinementGoals tail)
      | _ => throwError "unexpected Refinement.InterpretsGoals.cons goals"
  catch _ =>
    let generated ← goal.apply (mkConst ``Refinement.InterpretsGoals.nil)
    unless generated.isEmpty do
      throwError "unexpected Refinement.InterpretsGoals.nil goals"
    return []

elab "refinement_goals" : tactic => do
  let goals ← expandRefinementGoals (← getMainGoal)
  replaceMainGoal goals

elab "normalize_refinement_goal" : tactic => do
  let original ← (← getMainGoal).withContext do
    pure (← getLCtx).getFVarIds
  evalTactic (← `(tactic| try simp_all; intros))
  let rewrites ← refinementNormalizeAttr.getEntries (← getEnv) |>.mapM fun name =>
    let ident := mkIdent name
    `(Lean.Parser.Tactic.rwRule| $ident:ident)
  for rewrite in rewrites do
    evalTactic (← `(tactic| try rw [$rewrite] at *))
  evalTactic (← `(tactic| try simp_all))
  let goal ← getMainGoal
  let introduced ← goal.withContext do
    pure <| (← getLCtx).getFVarIds.filter fun fvar => !original.contains fvar
  let (_, goal) ← goal.revert introduced
  replaceMainGoal [goal]
  evalTactic (← `(tactic| try simp_all))

syntax (name := applyRefinement) "applyRefinement " term : tactic
syntax (name := applyRefinementReducing) "applyRefinement " term " reducing_by " tactic : tactic

macro_rules
| `(tactic| applyRefinement $refinement) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply Refinement.sound ($refinement) <;>
      refinement_goals <;>
      normalize_refinement_goal)
| `(tactic| applyRefinement $refinement reducing_by $reducer:tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply Refinement.sound ($refinement) <;>
      $reducer:tactic <;>
      refinement_goals <;>
      normalize_refinement_goal)

syntax (name := applyTactic) "applyTactic " term : tactic
syntax (name := applyTacticReducing) "applyTactic " term " reducing_by " tactic : tactic

macro_rules
| `(tactic| applyTactic $tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply Refinement.sound (($tactic) _) <;>
      refinement_goals <;>
      normalize_refinement_goal)
| `(tactic| applyTactic $tactic reducing_by $reducer:tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply Refinement.sound (($tactic) _) <;>
      $reducer:tactic <;>
      refinement_goals <;>
      normalize_refinement_goal)

def Refinement.raise {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    {E : Type} [Language.Reflects ctx.primCtx E] {goal : Pr E} {termGoal : Pr (Term ctx.primCtx)}
    (hlower : goal.toTerm? = some termGoal)
    (refinement : Refinement ctx ctxTy ctxTerm termGoal) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := refinement.goals.map Pr.ofTerm
  prove := by
    intro proveSubgoals
    refine ⟨termGoal, hlower, ?_⟩
    simp only [← Language.Provable_term]
    apply refinement.prove
    intro subgoal hsubgoal
    have hraised := proveSubgoals (Pr.ofTerm (E := E) subgoal)
      (List.mem_map.mpr ⟨subgoal, hsubgoal, rfl⟩)
    rcases hraised with ⟨raised, hraised, proof⟩
    rw [Pr.toTerm?_ofTerm] at hraised
    cases Option.some.inj hraised
    simpa only [Language.Provable_term] using proof

def Tactic.raise {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    {E : Type} [Language.Reflects ctx.primCtx E]
    (tactic : Tactic ctx ctxTy ctxTerm (Term ctx.primCtx)) : Tactic ctx ctxTy ctxTerm E :=
  fun goal =>
    match h : goal.toTerm? with
    | none => Refinement.stuck goal
    | some termGoal => Refinement.raise h (tactic termGoal)

namespace Tactic

variable {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E]

def stuck : Tactic ctx ctxTy ctxTerm E := Refinement.stuck

def andThen (first second : Tactic ctx ctxTy ctxTerm E) : Tactic ctx ctxTy ctxTerm E :=
  fun goal => (first goal).andThen second

def iterate (fuel : Nat) (step : Tactic ctx ctxTy ctxTerm E) : Tactic ctx ctxTy ctxTerm E
| goal =>
    match fuel with
    | 0 => step goal
    | n + 1 => (step goal).refine fun subgoal _ => iterate n step subgoal

def invertible (tactic : Tactic ctx ctxTy ctxTerm E) : Prop :=
  ∀ goal, Refinement.invertible (tactic goal)

theorem iterate_invertible {step : Tactic ctx ctxTy ctxTerm E} (hstep : invertible step) :
    ∀ fuel, invertible (iterate fuel step)
| 0 => hstep
| n + 1 => fun goal =>
    Refinement.refine_invertible _ _ (hstep goal)
      (fun subgoal _ => iterate_invertible hstep n subgoal)

/- Completeness proper, relative to a `domain` of goals the tactic claims to decide:
  every provable goal in the domain is closed outright (no residual subgoals).

  Unlike `invertible` this is not satisfied by `stuck`, and it is the property that makes
  `tactic` a decision procedure on `domain` -- see `decides`. -/
def CompleteOn (tactic : Tactic ctx ctxTy ctxTerm E) (domain : Pr E → Prop) : Prop :=
  ∀ goal, domain goal → Language.Provable ctx ctxTy ctxTerm goal → (tactic goal).goals = []

/- On its domain, a complete tactic decides provability: the goal is provable exactly when
  the tactic closes it. The `←` direction is soundness (`Refinement.toProvable`), which every
  `Refinement` carries by construction; `CompleteOn` supplies `→`. -/
theorem decides {tactic : Tactic ctx ctxTy ctxTerm E} {domain : Pr E → Prop}
    (hcomplete : CompleteOn tactic domain) (goal : Pr E) (hdomain : domain goal) :
    Language.Provable ctx ctxTy ctxTerm goal ↔ (tactic goal).goals = [] :=
  ⟨hcomplete goal hdomain, fun hclosed => (tactic goal).toProvable hclosed⟩

end Tactic

namespace Tactic?

variable {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E]

def orElse (first second : Tactic? ctx ctxTy ctxTerm E) : Tactic? ctx ctxTy ctxTerm E :=
  fun goal => (first goal).orElse (fun _ => second goal)

def firstOf : List (Tactic? ctx ctxTy ctxTerm E) → Tactic? ctx ctxTy ctxTerm E
| [] => fun _ => none
| tactic :: rest => orElse tactic (firstOf rest)

def toTactic (tactic : Tactic? ctx ctxTy ctxTerm E) : Tactic ctx ctxTy ctxTerm E :=
  fun goal => (tactic goal).getD (Refinement.stuck goal)

def assumption [DecidableEq E] : (facts : List (Pr E)) →
    (∀ fact, fact ∈ facts → Language.Provable ctx ctxTy ctxTerm fact) → Tactic? ctx ctxTy ctxTerm E
| [], _ => fun _ => none
| fact :: rest, hfacts => fun goal =>
    if h : fact = goal then some (Refinement.lift (h ▸ hfacts fact (by simp)))
    else assumption rest (fun f hf => hfacts f (by simp [hf])) goal

def raise {E : Type} [Language.Reflects ctx.primCtx E]
    (tactic : Tactic? ctx ctxTy ctxTerm (Term ctx.primCtx)) : Tactic? ctx ctxTy ctxTerm E :=
  fun goal =>
    match h : goal.toTerm? with
    | none => none
    | some termGoal => (tactic termGoal).map (Refinement.raise h)

end Tactic?

namespace Pr

namespace Refinement

private def structuralGoals {ctx : Ctx} : Pr (Term ctx.primCtx) → List (Pr (Term ctx.primCtx))
| .and p q => structuralGoals p ++ structuralGoals q
| .forallTy name p => (structuralGoals p).map (Pr.forallTy name)
| p@(.forallTerm _ _) => [p]
| p => [p]

private theorem structuralInterprets {ctx : Ctx}
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)} (goal : Pr (Term ctx.primCtx)) :
    (∀ subgoal, subgoal ∈ structuralGoals goal →
      Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.interp ctx ctxTy ctxTerm goal := by
  induction goal generalizing ctxTy ctxTerm with
  | eq varCtx ty lhs rhs =>
      intro proveSubgoals
      cases proveSubgoals (.eq varCtx ty lhs rhs) (by simp [structuralGoals]) with
      | ofProof proof => exact proof
  | hasType varCtx term ty =>
      intro proveSubgoals
      cases proveSubgoals (.hasType varCtx term ty) (by simp [structuralGoals]) with
      | ofProof proof => exact proof
  | and p q ihp ihq =>
      intro proveSubgoals
      exact And.intro
        (ihp (by
          intro subgoal hsubgoal
          exact proveSubgoals subgoal (by simp [structuralGoals, hsubgoal])))
        (ihq (by
          intro subgoal hsubgoal
          exact proveSubgoals subgoal (by simp [structuralGoals, hsubgoal])))
  | or p q =>
      intro proveSubgoals
      cases proveSubgoals (.or p q) (by simp [structuralGoals]) with
      | ofProof proof => exact proof
  | implies p q =>
      intro proveSubgoals
      cases proveSubgoals (.implies p q) (by simp [structuralGoals]) with
      | ofProof proof => exact proof
  | forallTy name p ih =>
      intro proveSubgoals α
      apply ih
      intro subgoal hsubgoal
      have hforall : Pr.Provable ctx ctxTy ctxTerm (.forallTy name subgoal) :=
        proveSubgoals (.forallTy name subgoal) (by
          change .forallTy name subgoal ∈ (structuralGoals p).map (Pr.forallTy name)
          exact List.mem_map.mpr ⟨subgoal, hsubgoal, rfl⟩)
      cases hforall with
      | ofProof proof => exact Pr.Provable.ofProof (proof α)
  | forallTerm name p _ =>
      intro proveSubgoals
      cases proveSubgoals (.forallTerm name p) (by simp [structuralGoals]) with
      | ofProof proof => exact proof
def structural {ctx : Ctx}
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)} (goal : Pr (Term ctx.primCtx)) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := structuralGoals goal
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    exact Pr.Provable.ofProof (structuralInterprets goal proveSubgoals)

end Refinement

end Pr

end Zag
