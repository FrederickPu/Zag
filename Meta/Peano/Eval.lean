import Meta.Eval
import Lib.Peano.Eval

/-!
# Peano control-flow evaluation tactics

The generic evaluator only knows how to invoke a semantic finalizer at a named operator. This
module supplies the Peano `while` finalizer and translates its native theorem premises into the
public invariant obligations.
-/

namespace Zag

open Lean Elab Tactic Meta
open Lean.Meta.Sym

/-- Apply and normalize the Peano while semantic rule, leaving arithmetic obligations visible. -/
syntax (name := applyPeanoWhileWPRefinementTactic)
  "apply_peano_while_wp" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

/-- Compatibility alias that also attempts to close the normalized arithmetic obligations. -/
syntax (name := whileInductionTactic) "while_induction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

/-- Compatibility alias leaving the normalized arithmetic obligations visible. -/
syntax (name := whileInductionQTactic) "while_induction?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

macro_rules
| `(tactic| while_induction $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) =>
    `(tactic|
      (while_induction? $[$bound?]? [$lemmas,*] $I stopping_at $N
         $[returning $result?]?
       auto_eval_refinement_goals [$lemmas,*]))
| `(tactic| while_induction? $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) =>
    `(tactic|
      apply_peano_while_wp $[$bound?]? [$lemmas,*] $I stopping_at $N
        $[returning $result?]?)

elab_rules : tactic
| `(tactic| apply_peano_while_wp $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) => do
    let fuel := match bound? with
      | some bound => bound.getNat
      | none => evalStepBound
    let goals ← getGoals
    let some root := goals.head? | return
    let target ← root.withContext do instantiateMVars (← root.getType)
    unless target.getAppFn.isConstOf ``EvaluatesCall do
      throwError "apply_peano_while_wp expected an EvaluatesCall goal"
    let args := target.getAppArgs
    unless args.size >= 4 do throwError "malformed EvaluatesCall goal"
    let ctx := args[args.size - 4]!
    let primCtx ← root.withContext do mkAppM ``Ctx.primCtx #[ctx]
    let valType ← root.withContext do mkAppM ``Val #[primCtx]
    let valuesType ← root.withContext do mkAppM ``List #[valType]
    let invariantType ← root.withContext do
      let tail ← mkArrow valuesType (mkSort .zero)
      mkArrow (mkConst ``Nat) tail
    let invariant ← root.withContext do Term.elabTerm I (some invariantType)
    let stoppingAt ← root.withContext do Term.elabTerm N (some (mkConst ``Nat))
    let loopResult ← root.withContext do match result? with
      | some result => Term.elabTerm result (some valType)
      | none => mkFreshExprMVar valType
    let invariant ← instantiateMVars invariant
    let stoppingAt ← instantiateMVars stoppingAt
    let loopResult ← instantiateMVars loopResult
    let invariantType ← inferType invariant
    let finalizer : EvalSemanticFinalizer := ⟨mkStrLit "while", fun goal => goal.withContext do
        let target ← instantiateMVarsS (← goal.getType)
        let targetArgs := target.getAppArgs
        unless targetArgs.size >= 4 do return none
        unless ← withTransparency .all <| isDefEq targetArgs[targetArgs.size - 1]! loopResult do
          return none
        let rule ← mkConstWithFreshMVarLevels ``Peano.while_evaluatesTo
        let subgoals ← goal.apply rule { newGoals := .all }
        let mut propositions := []
        let mut parameters := []
        for subgoal in subgoals do
          let type ← instantiateMVarsS (← subgoal.getType)
          if ← isProp type then
            propositions := propositions ++ [subgoal]
          else if ← withTransparency .all <| isDefEq type invariantType then
            subgoal.assign invariant
          else if ← withTransparency .all <| isDefEq type (mkConst ``Nat) then
            subgoal.assign stoppingAt
          else
            parameters := parameters ++ [subgoal]
        -- Keep the theorem's native proof spine while presenting the established public order.
        let [hop, operands, headTy, init, typed, preserved, exits] := propositions
          | return none
        return some {
          prerequisites := [hop, operands, headTy]
          roots := [
            .goal `typed typed,
            .residual `init init,
            .forallAnd `step.condition `step.preservation preserved,
            .goal `termination exits]
          parameters
        }⟩
    let generated ← SymM.run <| evalWPVCGen [root] (some finalizer) fuel
    setGoals generated
    evalTactic (← `(tactic| normalize_eval_refinement_goals [$lemmas,*]))
    let normalized ← getGoals
    setGoals (normalized ++ goals.tail)

end Zag
