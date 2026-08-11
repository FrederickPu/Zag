import Meta.UnifyTypeCompleteness

namespace Zag

namespace Pr

namespace TypeUnification

/-- Every provable `hasType` goal is closed outright by `unifyType`. -/
theorem unifyType_completeOn_hasType {ctx : Ctx} [Peano.Model ctx]
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup) :
    Tactic.CompleteOn
      (ctx := ctx) (ctxTy := []) (ctxTerm := [])
      unifyType
      (fun goal => ∃ varCtx term ty, goal = .hasType varCtx term ty) := by
  intro goal hdomain hprov
  rcases hdomain with ⟨varCtx, term, ty, rfl⟩
  simp only [unifyType, unifyTypeGoals]
  simp only [Language.Provable_term] at hprov
  have hty : Term.hasType ctx varCtx term ty := by
    cases hprov with
    | ofProof p =>
        simpa [Pr.interp, Term.subst, Ty.subst_nil, list_map_subst_nil] using p
  exact unifyTypeHasTypeGoals_eq_nil_of_hasType hnames hty

/-- Invertibility of `unifyType` for closed proof states follows from completeness on
  `hasType` goals and the identity behaviour on every other connective. -/
theorem unifyType_invertible {ctx : Ctx} [Peano.Model ctx] {goal : Pr (Term ctx.primCtx)}
    (hnames : (ctx.primFuncCtx.map Prod.fst).Nodup) :
    Refinement.invertible (unifyType (ctx := ctx) (ctxTy := []) (ctxTerm := []) goal) := by
  intro hgoal subgoal hsubgoal
  simp only [Language.Provable_term] at hgoal ⊢
  cases goal with
  | hasType varCtx term ty =>
      have hnil := unifyType_completeOn_hasType (ctx := ctx) hnames
        (.hasType varCtx term ty) ⟨varCtx, term, ty, rfl⟩ (by
          simpa only [Language.Provable_term] using hgoal)
      simp [unifyType, unifyTypeGoals] at hsubgoal hnil
      simp [hnil] at hsubgoal
  | eq varCtx ty lhs rhs =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | and p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | or p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | implies p q =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | forallTy p =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal
  | forallTerm p =>
      simp [unifyType, unifyTypeGoals] at hsubgoal; subst hsubgoal; exact hgoal

end TypeUnification

end Pr

end Zag
