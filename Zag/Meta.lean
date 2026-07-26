import Zag.Meta.Language

namespace Zag

structure Refinement (ctx : Ctx) (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    {E : Type} [Language ctx.primCtx E] (goal : Pr E) where
  goals : List (Pr E)
  prove : (∀ subgoal, subgoal ∈ goals → Language.Provable ctx ctxTy ctxTerm subgoal) →
    Language.Provable ctx ctxTy ctxTerm goal

abbrev Tactic (ctx : Ctx) (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E] :=
  (goal : Pr E) → Refinement ctx ctxTy ctxTerm goal

abbrev Tactic? (ctx : Ctx) (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E] :=
  (goal : Pr E) → Option (Refinement ctx ctxTy ctxTerm goal)

namespace Refinement

variable {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
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

def complete {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal) : Prop :=
  Language.Provable ctx ctxTy ctxTerm goal →
    ∀ subgoal, subgoal ∈ refinement.goals → Language.Provable ctx ctxTy ctxTerm subgoal

theorem lift_complete {goal : Pr E} (proof : Language.Provable ctx ctxTy ctxTerm goal) :
    complete (lift proof) := by
  intro _ subgoal hsubgoal
  simp [lift] at hsubgoal

theorem stuck_complete (goal : Pr E) :
    complete (stuck (ctx := ctx) (ctxTy := ctxTy) (ctxTerm := ctxTerm) goal) := by
  intro hgoal subgoal hsubgoal
  simp [stuck] at hsubgoal
  exact hsubgoal ▸ hgoal

theorem refine_complete {goal : Pr E} (refinement : Refinement ctx ctxTy ctxTerm goal)
    (next : ∀ subgoal, subgoal ∈ refinement.goals → Refinement ctx ctxTy ctxTerm subgoal)
    (hrefinement : complete refinement)
    (hnext : ∀ subgoal hsubgoal, complete (next subgoal hsubgoal)) :
    complete (refinement.refine next) := by
  intro hgoal generated hgenerated
  rcases List.mem_flatMap.mp hgenerated with ⟨attached, _hattached, hgeneratedNext⟩
  rcases attached with ⟨subgoal, hsubgoal⟩
  exact hnext subgoal hsubgoal (hrefinement hgoal subgoal hsubgoal) generated hgeneratedNext

end Refinement

def Refinement.raise {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
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

def Tactic.raise {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
    {E : Type} [Language.Reflects ctx.primCtx E]
    (tactic : Tactic ctx ctxTy ctxTerm (Term ctx.primCtx)) : Tactic ctx ctxTy ctxTerm E :=
  fun goal =>
    match h : goal.toTerm? with
    | none => Refinement.stuck goal
    | some termGoal => Refinement.raise h (tactic termGoal)

namespace Tactic

variable {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E]

def stuck : Tactic ctx ctxTy ctxTerm E := Refinement.stuck

def andThen (first second : Tactic ctx ctxTy ctxTerm E) : Tactic ctx ctxTy ctxTerm E :=
  fun goal => (first goal).andThen second

def iterate (fuel : Nat) (step : Tactic ctx ctxTy ctxTerm E) : Tactic ctx ctxTy ctxTerm E
| goal =>
    match fuel with
    | 0 => step goal
    | n + 1 => (step goal).refine fun subgoal _ => iterate n step subgoal

def complete (tactic : Tactic ctx ctxTy ctxTerm E) : Prop :=
  ∀ goal, Refinement.complete (tactic goal)

theorem iterate_complete {step : Tactic ctx ctxTy ctxTerm E} (hstep : complete step) :
    ∀ fuel, complete (iterate fuel step)
| 0 => hstep
| n + 1 => fun goal =>
    Refinement.refine_complete _ _ (hstep goal) (fun subgoal _ => iterate_complete hstep n subgoal)

end Tactic

namespace Tactic?

variable {ctx : Ctx} {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
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
| .forallTy p => (structuralGoals p).map Pr.forallTy
| .forallTerm p => (structuralGoals p).map Pr.forallTerm
| p => [p]

private theorem structuralInterprets {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr (Term ctx.primCtx)) :
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
  | forallTy p ih =>
      intro proveSubgoals α
      apply ih
      intro subgoal hsubgoal
      have hforall : Pr.Provable ctx ctxTy ctxTerm (.forallTy subgoal) :=
        proveSubgoals (.forallTy subgoal) (by
          change .forallTy subgoal ∈ (structuralGoals p).map Pr.forallTy
          exact List.mem_map.mpr ⟨subgoal, hsubgoal, rfl⟩)
      cases hforall with
      | ofProof proof => exact Pr.Provable.ofProof (proof α)
  | forallTerm p ih =>
      intro proveSubgoals x
      apply ih
      intro subgoal hsubgoal
      have hforall : Pr.Provable ctx ctxTy ctxTerm (.forallTerm subgoal) :=
        proveSubgoals (.forallTerm subgoal) (by
          change .forallTerm subgoal ∈ (structuralGoals p).map Pr.forallTerm
          exact List.mem_map.mpr ⟨subgoal, hsubgoal, rfl⟩)
      cases hforall with
      | ofProof proof => exact Pr.Provable.ofProof (proof x)
def structural {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr (Term ctx.primCtx)) :
    Refinement ctx ctxTy ctxTerm goal where
  goals := structuralGoals goal
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    exact Pr.Provable.ofProof (structuralInterprets goal proveSubgoals)

end Refinement

end Pr

end Zag
