import Zag.Meta.Language
import Zag.Meta.Refinement

namespace Zag

abbrev PrRefinement (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    {E : Type} [Language ctx.primCtx E] (goal : Pr E)
    (hM : ctx.M = Id := by first | assumption | rfl) :=
  Refinement (fun p => Language.Provable ctx ctxTy ctxTerm p hM) goal

abbrev PrTactic (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E]
    (hM : ctx.M = Id := by first | assumption | rfl) :=
  Tactic (fun p : Pr E => Language.Provable ctx ctxTy ctxTerm p hM)

abbrev PrTactic? (ctx : Ctx) (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx))
    (E : Type) [Language ctx.primCtx E]
    (hM : ctx.M = Id := by first | assumption | rfl) :=
  Tactic? (fun p : Pr E => Language.Provable ctx ctxTy ctxTerm p hM)

namespace PrRefinement

variable {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E] {hM : ctx.M = Id}

theorem sound {goal : Pr (Term ctx.primCtx)}
    (refinement : PrRefinement ctx ctxTy ctxTerm goal)
    (subgoals : Refinement.InterpretsGoals
      (Language.Provable ctx ctxTy ctxTerm) refinement.goals) :
    Pr.interp ctx ctxTy ctxTerm goal := by
  have proof := refinement.prove fun subgoal hsubgoal => by
    exact subgoals.get hsubgoal
  simp only [Language.Provable_term] at proof
  cases proof with
  | ofProof result => exact result

end PrRefinement

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
      apply PrRefinement.sound ($refinement) <;>
      refinement_goals <;>
      rw [Zag.Language.Provable_term] <;>
      refine Pr.Provable.ofProof ?_ <;>
      normalize_refinement_goal)
| `(tactic| applyRefinement $refinement reducing_by $reducer:tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply PrRefinement.sound ($refinement) <;>
      $reducer:tactic <;>
      refinement_goals <;>
      rw [Zag.Language.Provable_term] <;>
      refine Pr.Provable.ofProof ?_ <;>
      normalize_refinement_goal)

syntax (name := applyTactic) "applyTactic " term : tactic
syntax (name := applyTacticReducing) "applyTactic " term " reducing_by " tactic : tactic

macro_rules
| `(tactic| applyTactic $tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply PrRefinement.sound (($tactic) _) <;>
      refinement_goals <;>
      rw [Zag.Language.Provable_term] <;>
      refine Pr.Provable.ofProof ?_ <;>
      normalize_refinement_goal)
| `(tactic| applyTactic $tactic reducing_by $reducer:tactic) =>
    `(tactic|
      refine Pr.Provable.ofProof ?_ <;>
      apply PrRefinement.sound (($tactic) _) <;>
      $reducer:tactic <;>
      refinement_goals <;>
      rw [Zag.Language.Provable_term] <;>
      refine Pr.Provable.ofProof ?_ <;>
      normalize_refinement_goal)

def PrRefinement.raise {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    {E : Type} [Language.Reflects ctx.primCtx E] {goal : Pr E} {termGoal : Pr (Term ctx.primCtx)}
    {hM : ctx.M = Id}
    (hlower : goal.toTerm? = some termGoal)
    (refinement : PrRefinement ctx ctxTy ctxTerm termGoal) :
    PrRefinement ctx ctxTy ctxTerm goal where
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

def PrTactic.raise {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
    {E : Type} [Language.Reflects ctx.primCtx E] {hM : ctx.M = Id}
    (tactic : PrTactic ctx ctxTy ctxTerm (Term ctx.primCtx)) : PrTactic ctx ctxTy ctxTerm E :=
  fun goal =>
    match h : goal.toTerm? with
    | none => Refinement.stuck goal
    | some termGoal => PrRefinement.raise h (tactic termGoal)

namespace PrTactic?

variable {ctx : Ctx} {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)}
  {E : Type} [Language ctx.primCtx E] {hM : ctx.M = Id}

def assumption [DecidableEq E] : (facts : List (Pr E)) →
    (∀ fact, fact ∈ facts → Language.Provable ctx ctxTy ctxTerm fact) →
      PrTactic? ctx ctxTy ctxTerm E
| [], _ => fun _ => none
| fact :: rest, hfacts => fun goal =>
    if h : fact = goal then some (Refinement.lift (h ▸ hfacts fact (by simp)))
    else assumption rest (fun f hf => hfacts f (by simp [hf])) goal

def raise {E : Type} [Language.Reflects ctx.primCtx E]
    (tactic : PrTactic? ctx ctxTy ctxTerm (Term ctx.primCtx)) : PrTactic? ctx ctxTy ctxTerm E :=
  fun goal =>
    match h : goal.toTerm? with
    | none => none
    | some termGoal => (tactic termGoal).map (PrRefinement.raise h)

end PrTactic?

namespace Pr

namespace Refinement

private def structuralGoals {ctx : Ctx} : Pr (Term ctx.primCtx) → List (Pr (Term ctx.primCtx))
| .and p q => structuralGoals p ++ structuralGoals q
| .forallTy name p => (structuralGoals p).map (Pr.forallTy name)
| p@(.forallTerm _ _) => [p]
| p => [p]

private theorem structuralInterprets {ctx : Ctx}
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)} {hM : ctx.M = Id}
    (goal : Pr (Term ctx.primCtx)) :
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
    {ctxTy : Scope Ty} {ctxTerm : Scope (Term ctx.primCtx)} {hM : ctx.M = Id}
    (goal : Pr (Term ctx.primCtx)) :
    PrRefinement ctx ctxTy ctxTerm goal where
  goals := structuralGoals goal
  prove := by
    intro proveSubgoals
    simp only [Language.Provable_term] at proveSubgoals ⊢
    exact Pr.Provable.ofProof (structuralInterprets goal proveSubgoals)

end Refinement

end Pr

end Zag
