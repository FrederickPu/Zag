import Meta.Eval
import Lib.Peano.Eval

/-!
# Peano control-flow evaluation tactics

The generic evaluator only knows how to walk a machine and invoke a finalizer at a named operator.
This module supplies the Peano `while` finalizer and translates its typed semantic refinement into
the public invariant obligations.
-/

namespace Zag

/-- Apply and normalize the Peano while WP rule, leaving arithmetic obligations visible. -/
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
| `(tactic| apply_peano_while_wp $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) => do
    let loopResult ← match result? with
      | some result => pure result
      | none => `(term| ?loopResult)
    `(tactic|
      (evaluates_call $[$bound?]? [$lemmas,*] finalizing_at_op "while" with
        (apply_eval_wp_refinement $[$bound?]? [$lemmas,*]
            (Zag.Peano.whileInduction rfl
              (by evaluates_to_all $[$bound?]? [$lemmas,*]) rfl)
            selecting
              ({ invariant := $I, stoppingAt := $N, result := $loopResult } :
                Zag.Peano.WhileInductionParams _)
            naming [typed, init, step.condition, step.preservation, termination]
         process_eval_wp_goals $[$bound?]? [$lemmas,*])))

end Zag
