import Zag.EvalState
import Zag.Loop
import Zag.Meta.Refinement

/-!
# Small-step evaluation tactics

`evaluates` runs a closed `EvaluatesTo` goal. `evaluates_call` proves block specifications stated
as `EvaluatesCall`; recursive proofs splice an induction hypothesis with
`EvaluatesFrom.call_then` when the machine reaches the recursive call. Operator-specific control
flow is supplied through the generic finalizer hook rather than built into this module.

## On fuel

The step count is found by running the machine, not supplied. `evaluates_from` walks until the
goal is discharged or no rule applies, so a caller never has to know how many steps a block
takes. A numeral may still be given as an *upper bound*, which only matters for a program that
would otherwise walk forever.

This is why the count is no longer mandatory: it used to be the depth to which a recursive macro
unrolled, so it had to be an overestimate, and the tactic paid for every unused step at
elaboration time. The walk below is an ordinary loop, so an unused bound costs nothing.
-/

namespace Zag

open Lean Elab Tactic

/-- Upper bound used when a caller does not give one. Reaching it means the machine did not halt,
  which for these programs indicates a genuine loop rather than a bound that is too small. -/
def evalStepBound : Nat := 10000

/-- Run the small-step machine until it stops, discharging `EvaluatesTo`.

  The lemmas to pass are the program's own: its operator context (`natOpCtx`, `heapOpCtx`, ..) and
  its block list. Everything context-independent is already tagged `@[eval_step]`.

  Symbolic *leaves* are fine -- `add [nat x, nat 1]` runs to `Val.nat (x + 1)`. Symbolic
  *control flow* is not: a branch on an unknown condition, or a recursive call with an unknown
  bound, stops and needs a case split or an induction hypothesis. -/
syntax (name := evaluatesTactic) "evaluates" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallFinalizingTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" " finalizing_at_op " term " with " tactic : tactic

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

/-- Discharge the call that normalisation stopped at, using a known specification, then keep
  normalising. This is deliberately *separate* from `evaluates_call`: walking the machine and
  knowing which fact closes a call are different jobs. -/
syntax (name := useCallTactic) "use_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

/-- Discharge an application stopped by `stopping_at_apply`, then continue normalising. -/
syntax (name := useApplyTactic) "use_apply" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term (" discharging " tactic)? : tactic

/-- The non-closing form of `use_apply`, for adapters that must expose generated obligations. -/
syntax (name := useApplyQTactic) "use_apply?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

/-- Apply a semantic refinement to the value produced by the current term, then evaluate the
  surrounding continuation. Operator-specific finalizers supply only the refinement itself and
  tactics for its named premises. -/
syntax (name := applyEvalRefinementTactic) "apply_eval_refinement" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " naming" " [" ident,* "]"
  " with " tactic : tactic

/-- Prove a self-recursive block's specification by induction on `target`, closing the recursive
  call with the induction hypothesis automatically.

  The loop invariant is the `EvaluatesCall` statement being proved -- it is what the hypothesis
  gets instantiated with -- so nothing has to be supplied separately. What is left over is only
  the arithmetic: `x + 1 + y = x + (y + 1)` and its base case. No `EvaluatesFrom` goal, and so no
  machine state, is ever surfaced.

  Arithmetic the lemma list does not cover is left as an ordinary goal, so the caller can finish
  it in place. The typed `PropRefinement.natInduction` rule supplies the base and step premises;
  this adapter only introduces their binders under names taken from the caller.

  `generalizing` takes the arguments that change across iterations, exactly as `induction` does. -/
syntax (name := tailInductionTactic) "tail_induction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace ident
  (" generalizing" (ppSpace colGt ident)+)? : tactic

/-! ### seeing the obligations

`tail_induction?`, `evaluates_call?` and `use_call?` walk the machine exactly as their plain
counterparts do, then stop at the arithmetic instead of discharging it. Primitive libraries use
`@[eval_finish]` to remove their own value wrappers. -/
syntax (name := tailInductionQTactic) "tail_induction?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace ident
  (" generalizing" (ppSpace colGt ident)+)? : tactic

syntax (name := evaluatesCallQTactic) "evaluates_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := useCallQTactic) "use_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

open Lean Elab Tactic in
/-- Run `tac`, reporting whether it succeeded and rolling the state back if it did not. -/
private def tryStep (tac : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic tac
    return true
  catch _ =>
    restoreState saved
    return false

open Lean Elab Tactic in
/-- Walk an `EvaluatesFrom` goal one `step` at a time until it is discharged or nothing applies.

  Each iteration tries, in order: the goal is already `done`; the machine has returned and only
  `value = expected` is left (handed to `close`); the machine is parked at a call, which is where
  a specification has to be supplied by the caller; otherwise take one machine step and continue.
  Anything left over is put back into source notation by `eval_fold`. -/
structure EvalFinalizer where
  probe : TSyntax `tactic
  run : TSyntax `tactic

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

open Lean in
/-- The bound a caller wrote, or `evalStepBound`. -/
private def boundOf (bound? : Option (TSyntax `num)) : Nat :=
  match bound? with
  | some n => n.getNat
  | none => evalStepBound

open Lean Elab Tactic in
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
      refine ⟨$fuel, ?_⟩ <;>
      set_option linter.unusedSimpArgs false in
        simp +arith [eval_step, Zag.EvalState.run,
          Zag.EvalState.start, Zag.EvalState.result?, $lemmas,*] <;>
        try rfl)
| `(tactic| evaluates_to_all $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      first
      | exact Zag.EvaluatesToAll.nil
      | constructor
        · evaluates $[$bound?]? [$lemmas,*]
        · evaluates_to_all $[$bound?]? [$lemmas,*])
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
| `(tactic| use_apply $[$bound?]? [$lemmas,*] $spec $[discharging $discharge?]?) => do
    let discharge ← match discharge? with
      | some tactic => pure tactic
      | none => `(tactic| skip)
    `(tactic|
      (refine Zag.EvaluatesFrom.apply_then ?_ (by
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*])
       apply $spec
       all_goals (try set_option linter.unusedSimpArgs false in simp +arith [$lemmas,*])
       all_goals (try simp only [List.cons.injEq, and_true, eval_finish])
       all_goals (try omega)
       $discharge))
| `(tactic| use_apply? $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      (refine Zag.EvaluatesFrom.apply_then ?_ (by
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*] discharging
           (try simp only [eval_finish]))
       apply $spec))
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
        evaluates_from $[$bound?]? [$lemmas,*] discharging
          (try simp only [eval_finish]))
| `(tactic| tail_induction $[$bound?]? [$lemmas,*] $target:ident) =>
    `(tactic|
      (apply_refinement (PropRefinement.natInduction $target)
       · evaluates_call $[$bound?]? [$lemmas,*]
       ·
         intro $target ih
         evaluates_call $[$bound?]? [$lemmas,*]
         use_call $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction $[$bound?]? [$lemmas,*] $target:ident generalizing $vars*) =>
    `(tactic|
      (revert $vars*
       apply_refinement (PropRefinement.natInduction $target)
       ·
         intro $vars*
         evaluates_call $[$bound?]? [$lemmas,*]
       ·
         intro $target ih $vars*
         evaluates_call $[$bound?]? [$lemmas,*]
         use_call $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction? $[$bound?]? [$lemmas,*] $target:ident) =>
    `(tactic|
      (apply_refinement (PropRefinement.natInduction $target)
       · evaluates_call? $[$bound?]? [$lemmas,*]
       ·
         intro $target ih
         evaluates_call $[$bound?]? [$lemmas,*]
         use_call? $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction? $[$bound?]? [$lemmas,*] $target:ident generalizing $vars*) =>
    `(tactic|
      (revert $vars*
       apply_refinement (PropRefinement.natInduction $target)
       ·
         intro $vars*
         evaluates_call? $[$bound?]? [$lemmas,*]
       ·
         intro $target ih $vars*
         evaluates_call $[$bound?]? [$lemmas,*]
         use_call? $[$bound?]? [$lemmas,*] ih))
end Zag
