import Meta.Eval.Core
import Zag.Meta.Refinement

/-!
# Evaluation call composition

Call specifications and refinement lifting layered over the small-step machine walker.
-/

namespace Zag

syntax (name := evaluatesCallTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallFinalizingTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" " finalizing_at_op " term " with " tactic : tactic

/-- Discharge a stopped call using a known specification, then keep walking. -/
syntax (name := useCallTactic) "use_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

syntax (name := evaluatesCallQTactic) "evaluates_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := useCallQTactic) "use_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

/-- Apply a semantic refinement to the current term and walk its continuation. -/
syntax (name := applyEvalRefinementTactic) "apply_eval_refinement" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " naming" " [" ident,* "]"
  " with " tactic : tactic

macro_rules
| `(tactic| use_call $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      (apply Zag.EvaluatesFrom.call_then
       case hblock => rfl
       case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
       case hcall => apply $spec
       intro scope
       evaluates_from $[$bound?]? [$lemmas,*]))
| `(tactic| use_call? $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      (apply Zag.EvaluatesFrom.call_then
       case hblock => rfl
       case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
       case hcall => apply $spec
       intro scope
       evaluates_from $[$bound?]? [$lemmas,*] discharging
         (try simp only [eval_finish])))
| `(tactic| apply_eval_refinement $[$bound?]? [$lemmas,*] $refinement
      naming [$names,*] with $premises) =>
    `(tactic|
      (apply_refinement
         (PropRefinement.evalThen $refinement (by
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*] discharging
           (try simp only [eval_finish])))
         naming [$names,*]
       $premises))
| `(tactic| evaluates_call $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [eval_step, $lemmas,*]
        evaluates_from $[$bound?]? [$lemmas,*])
| `(tactic| evaluates_call $[$bound?]? [$lemmas,*]
      finalizing_at_op $op with $finalizer) =>
    `(tactic|
      (focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [eval_step, $lemmas,*]
        evaluates_from $[$bound?]? [$lemmas,*]
          finalizing_at_op $op with $finalizer))
| `(tactic| evaluates_call? $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [eval_step, $lemmas,*]
        evaluates_from $[$bound?]? [$lemmas,*] stopping_at_apply discharging
          (try simp only [eval_finish]))

end Zag
