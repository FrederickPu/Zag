import Zag.Theory

namespace Zag

namespace Pr

structure MetaProgram (ctx : Ctx)
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (goal : Pr ctx.primCtx) where
  goals : List (Pr ctx.primCtx)
  prove : (∀ subgoal, subgoal ∈ goals →
    Pr.Provable ctx ctxTy ctxTerm subgoal) →
      Pr.Provable ctx ctxTy ctxTerm goal

namespace MetaProgram

def lift {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (proof : Pr.Provable ctx ctxTy ctxTerm goal) :
    MetaProgram ctx ctxTy ctxTerm goal where
  goals := []
  prove := by
    intro _
    exact proof

theorem toProvable {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (program : MetaProgram ctx ctxTy ctxTerm goal)
    (closed : program.goals = []) :
    Pr.Provable ctx ctxTy ctxTerm goal := by
  apply program.prove
  intro subgoal hsubgoal
  rw [closed] at hsubgoal
  cases hsubgoal

def refine {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (program : MetaProgram ctx ctxTy ctxTerm goal)
    (next : ∀ subgoal, subgoal ∈ program.goals →
      MetaProgram ctx ctxTy ctxTerm subgoal) :
    MetaProgram ctx ctxTy ctxTerm goal where
  goals := program.goals.attach.flatMap fun subgoal =>
    (next subgoal.val subgoal.property).goals
  prove := by
    intro proveGenerated
    apply program.prove
    intro subgoal hsubgoal
    apply (next subgoal hsubgoal).prove
    intro generated hgenerated
    apply proveGenerated
    exact List.mem_flatMap.mpr
      ⟨⟨subgoal, hsubgoal⟩, by simp, hgenerated⟩

def iterate {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)}
    (fuel : Nat)
    (step : (goal : Pr ctx.primCtx) → MetaProgram ctx ctxTy ctxTerm goal) :
    (goal : Pr ctx.primCtx) → MetaProgram ctx ctxTy ctxTerm goal
| goal =>
    match fuel with
    | 0 => step goal
    | n + 1 => (step goal).refine fun subgoal _ => iterate n step subgoal

def complete {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (program : MetaProgram ctx ctxTy ctxTerm goal) : Prop :=
  Pr.Provable ctx ctxTy ctxTerm goal →
    ∀ subgoal, subgoal ∈ program.goals →
      Pr.Provable ctx ctxTy ctxTerm subgoal

theorem lift_complete {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (proof : Pr.Provable ctx ctxTy ctxTerm goal) :
    complete (lift proof) := by
  intro _ subgoal hsubgoal
  simp [lift] at hsubgoal

theorem refine_complete {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} {goal : Pr ctx.primCtx}
    (program : MetaProgram ctx ctxTy ctxTerm goal)
    (next : ∀ subgoal, subgoal ∈ program.goals →
      MetaProgram ctx ctxTy ctxTerm subgoal)
    (hprogram : complete program)
    (hnext : ∀ subgoal hsubgoal, complete (next subgoal hsubgoal)) :
    complete (program.refine next) := by
  intro hgoal generated hgenerated
  rcases List.mem_flatMap.mp hgenerated with ⟨attached, _hattached, hgeneratedNext⟩
  rcases attached with ⟨subgoal, hsubgoal⟩
  have hsubgoalProv := hprogram hgoal subgoal hsubgoal
  exact hnext subgoal hsubgoal hsubgoalProv generated hgeneratedNext

private def structuralGoals {ctx : Ctx} : Pr ctx.primCtx → List (Pr ctx.primCtx)
| .and p q => structuralGoals p ++ structuralGoals q
| .forallTy p => (structuralGoals p).map Pr.forallTy
| .forallTerm p => (structuralGoals p).map Pr.forallTerm
| p => [p]

private theorem structuralInterprets {ctx : Ctx}
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr ctx.primCtx) :
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
    {ctxTy : List Ty} {ctxTerm : List (Term ctx.primCtx)} (goal : Pr ctx.primCtx) :
    MetaProgram ctx ctxTy ctxTerm goal where
  goals := structuralGoals goal
  prove := by
    intro proveSubgoals
    exact Pr.Provable.ofProof (structuralInterprets goal proveSubgoals)

end MetaProgram

end Pr

end Zag
