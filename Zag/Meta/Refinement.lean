import Lean.Elab.Tactic
import Zag.Refinement

namespace Zag

open Lean Elab Tactic Meta

private partial def expandRefinementGoals (goal : MVarId) : TacticM (List MVarId) := do
  let target ← instantiateMVars (← goal.getType)
  let args := target.getAppArgs
  let goals ← withTransparency .all do whnf args.back!
  let target := mkAppN target.getAppFn (args.pop.push goals)
  let goal ← withTransparency .all do goal.change target
  try
    let cons ← mkConstWithFreshMVarLevels ``Refinement.InterpretsGoals.cons
    let generated ← goal.apply cons
    match generated with
    | [head, tail] => return head :: (← expandRefinementGoals tail)
    | _ => throwError "unexpected Refinement.InterpretsGoals.cons goals"
  catch _ =>
    let nil ← mkConstWithFreshMVarLevels ``Refinement.InterpretsGoals.nil
    let generated ← goal.apply nil
    unless generated.isEmpty do
      throwError "unexpected Refinement.InterpretsGoals.nil goals"
    return []

elab "refinement_goals" : tactic => do
  let goals ← expandRefinementGoals (← getMainGoal)
  replaceMainGoal goals

syntax (name := nameRefinementGoals) "name_refinement_goals" " [" ident,* "]" : tactic

elab_rules : tactic
| `(tactic| name_refinement_goals [$names,*]) => do
    let goals ← getGoals
    let names := names.getElems
    unless goals.length = names.size do
      throwError "refinement produced {goals.length} goals, expected {names.size}"
    for (goal, name) in goals.zip names.toList do
      goal.setTag name.getId.eraseMacroScopes

elab "prefix_refinement_goals " name:ident : tactic => do
  let tagPrefix := name.getId.eraseMacroScopes
  for goal in ← getGoals do
    goal.setTag (Lean.Meta.appendTag tagPrefix (← goal.getTag))

syntax (name := applyRefinementRule) "apply_refinement " term : tactic
syntax (name := applyNamedRefinementRule)
  "apply_refinement " term " naming" " [" ident,* "]" : tactic

macro_rules
| `(tactic| apply_refinement $refinement) =>
    `(tactic|
      (apply Refinement.sound ($refinement)
       refinement_goals))
| `(tactic| apply_refinement $refinement naming [$names,*]) =>
    `(tactic|
      (apply Refinement.sound ($refinement)
       refinement_goals
       name_refinement_goals [$names,*]))

end Zag
