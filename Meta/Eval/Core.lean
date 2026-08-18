import Zag.EvalState
import Zag.Loop

/-!
# Small-step evaluator core

This module owns only machine walking, fuel, operator finalizers, and evaluation of argument
lists. Composition with call and application specifications lives in `Meta.Eval.Refinement`.
-/

namespace Zag

open Lean Elab Tactic

/-- Upper bound used when a caller does not give one. Reaching it means the machine did not halt,
  which for these programs indicates a genuine loop rather than a bound that is too small. -/
def evalStepBound : Nat := 10000

/-- Run the small-step machine until it stops, discharging `EvaluatesTo`.

  The lemmas to pass are the program's own operator context and block list. Symbolic leaves are
  supported, but symbolic control flow stops for a specification or case split. -/
syntax (name := evaluatesTactic) "evaluates" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesToAllTactic) "evaluates_to_all" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- The optional `discharging` clause controls the final `value = expected` obligation.
  `stopping_at_apply` stops when a CPS proof reaches an operator continuation. -/
syntax (name := evaluatesFromTactic) "evaluates_from" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" (" stopping_at_apply")?
  (" discharging " tactic)? : tactic

syntax (name := evaluatesFromFinalizingTactic) "evaluates_from" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" (" stopping_at_apply")?
  (" discharging " tactic)? " finalizing_at_op " term " with " tactic : tactic

/-- Run `tac`, reporting whether it succeeded and rolling the state back if it did not. -/
private def tryStep (tac : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic tac
    return true
  catch _ =>
    restoreState saved
    return false

/-- A hook invoked when machine walking reaches a selected operator. -/
structure EvalFinalizer where
  probe : TSyntax `tactic
  run : TSyntax `tactic

/-- Walk an `EvaluatesFrom` goal one `step` at a time until it is discharged or nothing applies. -/
partial def evaluatesFromCore (bound : Nat)
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (close : TSyntax `tactic) (finalizer? : Option EvalFinalizer := none)
    (stopAtApply : Bool := false) :
    TacticM Unit := do
  let fold ← `(tactic| try simp only [eval_fold])
  let rec go (remaining : Nat) : TacticM Unit := do
    if (← getGoals).isEmpty then return
    if ← tryStep (← `(tactic| exact Zag.EvaluatesFrom.done)) then return
    if ← tryStep (← `(tactic| refine Zag.EvaluatesFrom.done_of ?_)) then
      evalTactic close
      return
    if ← tryStep (← `(tactic| refine Zag.EvaluatesFrom.atCall ?_)) then
      evalTactic fold
      return
    if let some finalizer := finalizer? then
      let saved ← saveState
      if ← tryStep finalizer.probe then
        restoreState saved
        evalTactic finalizer.run
        return
    if stopAtApply then
      if ← tryStep (← `(tactic| refine Zag.EvaluatesFrom.atApply ?_)) then
        evalTactic fold
        return
    match remaining with
    | 0 => evalTactic fold
    | n + 1 =>
        let stepTac ← `(tactic|
          refine Zag.EvaluatesFrom.step
            (by set_option linter.unusedSimpArgs false in
                  simp +arith [eval_step, $lemmas,*] <;> rfl) ?_)
        if ← tryStep stepTac then go n else evalTactic fold
  go bound

/-- The bound a caller wrote, or `evalStepBound`. -/
private def boundOf (bound? : Option (TSyntax `num)) : Nat :=
  match bound? with
  | some n => n.getNat
  | none => evalStepBound

elab_rules : tactic
| `(tactic| evaluates_from $[$bound?]? [$lemmas,*] $[stopping_at_apply%$stopApply?]?
      $[discharging $close?]?) => do
    let close ← match close? with
      | some c => pure c
      | none =>
          `(tactic| try set_option linter.unusedSimpArgs false in simp +arith [$lemmas,*])
    evaluatesFromCore (boundOf bound?) lemmas.getElems close
      (stopAtApply := stopApply?.isSome)
| `(tactic| evaluates_from $[$bound?]? [$lemmas,*] $[stopping_at_apply%$stopApply?]?
      $[discharging $close?]? finalizing_at_op $op with $finalizer) => do
    let close ← match close? with
      | some c => pure c
      | none =>
          `(tactic| try set_option linter.unusedSimpArgs false in simp +arith [$lemmas,*])
    let probe ← `(tactic| refine Zag.EvaluatesFrom.atOp (name := $op) ?_)
    evaluatesFromCore (boundOf bound?) lemmas.getElems close
      (finalizer? := some { probe, run := finalizer })
      (stopAtApply := stopApply?.isSome)

macro_rules
| `(tactic| evaluates $[$bound?]? [$lemmas,*]) => do
    let fuel := Lean.Syntax.mkNumLit (toString (boundOf bound?))
    `(tactic|
      (focus
         rw [Zag.EvaluatesTo.iff_run]
         refine ⟨$fuel, ?_⟩
       all_goals
         set_option linter.unusedSimpArgs false in
           simp +arith [eval_step, Zag.EvalState.run,
             Zag.EvalState.start, Zag.EvalState.result?, $lemmas,*] <;>
           try rfl))
| `(tactic| evaluates_to_all $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      first
      | exact Zag.EvaluatesToAll.nil
      | constructor
        · evaluates $[$bound?]? [$lemmas,*]
        · evaluates_to_all $[$bound?]? [$lemmas,*])

end Zag
