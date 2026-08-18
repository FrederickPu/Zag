import Meta.Eval
import Lib.Peano.Eval

/-!
# Peano control-flow evaluation tactics

The generic evaluator only knows how to walk a machine and invoke a finalizer at a named operator.
This module supplies the Peano `while` finalizer and translates its typed semantic refinement into
the public invariant obligations.
-/

namespace Zag

/-- Prove a Peano `while` call from an indexed invariant and its stopping iteration. -/
syntax (name := whileInductionTactic) "while_induction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

/-- Run the same Peano while refinement while leaving its semantic obligations visible. -/
syntax (name := whileInductionQTactic) "while_induction?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

macro_rules
| `(tactic| while_induction $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) => do
    let loopResult ← match result? with
      | some result => pure result
      | none => `(term| ?loopResult)
    `(tactic|
      (while_induction? $[$bound?]? [$lemmas,*] $I stopping_at $N returning $loopResult
       all_goals
         (try set_option linter.unusedSimpArgs false in simp +arith [$lemmas,*])
       all_goals
         (try simp only [List.cons.injEq, and_true, eval_finish])
       all_goals (try omega)))
| `(tactic| while_induction? $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) => do
    let loopResult ← match result? with
      | some result => pure result
      | none => `(term| ?loopResult)
    `(tactic|
      (evaluates_call $[$bound?]? [$lemmas,*] finalizing_at_op "while" with
        (apply_eval_refinement $[$bound?]? [$lemmas,*]
            (Zag.Peano.whileInduction (I := $I) (N := $N) (loopResult := $loopResult) rfl
              (by evaluates_to_all $[$bound?]? [$lemmas,*]) rfl
              (by
                intros
                subst_vars
                try set_option linter.unusedSimpArgs false in simp +arith [$lemmas,*]))
            naming [init, step.condition, step.preservation, termination] with
          (case' condition =>
             intro iter args hlt hinv
             try subst hinv
             evaluates_call? $[$bound?]? [$lemmas,*]
             prefix_refinement_goals step
           case' preservation =>
             intro iter args hlt hinv hnext
             try subst hinv
             evaluates_call? $[$bound?]? [$lemmas,*]
             use_apply? $[$bound?]? [$lemmas,*] hnext
             prefix_refinement_goals step
           case' termination =>
             intro args hinv
             try subst hinv
             refine ⟨?condFalse, ?head⟩
             case' condFalse => evaluates_call? $[$bound?]? [$lemmas,*]
             prefix_refinement_goals termination))
       all_goals
         (try simp only [List.nil_append, List.set_cons_zero, List.set_cons_succ,
           List.cons.injEq, and_true, List.head?_cons, Option.some.injEq, decide_eq_true_eq,
           eval_finish])))

end Zag
