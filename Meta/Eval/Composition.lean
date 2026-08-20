import Meta.Eval.Core
import Zag.Meta.Refinement

/-!
# Evaluation call composition

Call specifications and refinement lifting layered over the small-step machine walker.
-/

namespace Zag

open Lean Elab Tactic Meta

syntax (name := evaluatesCallTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallFinalizingTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" " finalizing_at_op " term " with " tactic : tactic

/-- Discharge a stopped call using a known specification, then keep walking. -/
syntax (name := useCallTactic) "use_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

syntax (name := evaluatesCallQTactic) "evaluates_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Compatibility machine walk used by recursive induction after its measure has been split. -/
syntax (name := evaluatesCallMachineTactic) "evaluates_call_machine" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallMachineQTactic) "evaluates_call_machine?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Prove a normally completing call by splitting its block body into instruction WPs. -/
syntax (name := evaluatesCallWPTactic) "evaluates_call_wp" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := useCallQTactic) "use_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

/-- Apply a semantic refinement to the current term and walk its continuation. -/
syntax (name := applyEvalRefinementTactic) "apply_eval_refinement" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " naming" " [" ident,* "]"
  " with " tactic : tactic

/-- Prove ordinary block instructions in order, stopping when the current term needs a call or
  application specification. -/
syntax (name := evaluatesInstrsTactic) "evaluates_instrs" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
| `(tactic| use_call $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      first
      | (apply Zag.EvaluatesInstrs.cons_call
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (try simp only [Instr.ofTerm]
         apply Zag.EvaluatesTo.call
         case hblock => rfl
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (apply Zag.EvaluatesFrom.call_then
         case hblock => rfl
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*]
         try evaluates_instrs $[$bound?]? [$lemmas,*]))
| `(tactic| use_call? $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      first
      | (apply Zag.EvaluatesInstrs.cons_call
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (try simp only [Instr.ofTerm]
         apply Zag.EvaluatesTo.call
         case hblock => rfl
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (apply Zag.EvaluatesFrom.call_then
         case hblock => rfl
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case hcall =>
           first
           | apply $spec
           | (apply Zag.EvaluatesCall.of_eq
              case hcall => apply $spec
              case hvalue => simp [$lemmas,*])
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*] discharging
           (try simp only [eval_finish])
         try evaluates_instrs $[$bound?]? [$lemmas,*]))
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
    `(tactic| evaluates_call $[$bound?]? [$lemmas,*])
| `(tactic| evaluates_call_machine $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      (focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [eval_step, $lemmas,*]
        evaluates_from $[$bound?]? [$lemmas,*]))
| `(tactic| evaluates_call_machine? $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      (focus
        refine Zag.EvaluatesCall.of_evaluatesFrom ?_
        intro env base
        set_option linter.unusedSimpArgs false in
          simp +arith [eval_step, $lemmas,*]
        evaluates_from $[$bound?]? [$lemmas,*] stopping_at_apply discharging
          (try simp only [eval_finish])))
| `(tactic| evaluates_call_wp $[$bound?]? [$lemmas,*]) =>
    `(tactic|
      (focus
        apply Zag.EvaluatesCall.of_evaluatesInstrs
        case hblock => set_option maxRecDepth 10000 in rfl
        case hargs => set_option maxRecDepth 10000 in rfl
        evaluates_instrs $[$bound?]? [$lemmas,*]))

elab_rules : tactic
| `(tactic| evaluates_call $[$bound?]? [$lemmas,*]) => do
    let goal ← getMainGoal
    let target ← goal.withContext do instantiateMVars (← goal.getType)
    if target.hasFVar || target.hasMVar then
      evalTactic (← `(tactic| evaluates_call_wp $[$bound?]? [$lemmas,*]))
    else
      let fuel ← match bound? with
        | some bound => `(term| $bound)
        | none => `(term| Zag.evalStepBound)
      evalTactic (← `(tactic|
        first
        | (apply Zag.EvaluatesCall.of_runCallBodyMatches (fuel := $fuel) <;> native_decide)
        | evaluates_call_wp $[$bound?]? [$lemmas,*]))

/-- Split one instruction with an internal result metavariable, evaluate it in isolation, and
  recurse only after that result has been fixed. A stopped call/application remains ahead of its
  still-hidden dependent tail in the goal list. -/
private def containsExit (expr : Expr) : Bool :=
  (expr.find? fun subexpr => subexpr.getAppFn.isConstOf ``Term.exit).isSome

private partial def evaluatesInstrsCore (evalCurrentTactic directTactic : TSyntax `tactic) :
    TacticM Unit := do
  let goals ← getGoals
  let some root := goals.head? | return
  let rest := goals.tail
  let target ← root.withContext do instantiateMVars (← root.getType)
  unless target.getAppFn.isConstOf ``EvaluatesInstrs do
    throwError "evaluates_instrs expected an EvaluatesInstrs goal"
  let args := target.getAppArgs
  unless args.size >= 5 do throwError "malformed EvaluatesInstrs goal"
  let fields := args.extract (args.size - 5) args.size
  let ctx := fields[0]!
  let instrs ← root.withContext do withTransparency .reducible <| whnf fields[1]!
  let result ← root.withContext do withTransparency .reducible <| whnf fields[2]!
  let env := fields[3]!
  let value := fields[4]!
  if containsExit instrs || containsExit result then
    throwError "evaluates_instrs does not handle blocks containing non-local exits"
  let evalCurrent (goal : MVarId) : TacticM (List MVarId) := do
    let evalTarget ← goal.withContext do instantiateMVars (← goal.getType)
    let evalArgs := evalTarget.getAppArgs
    unless evalTarget.getAppFn.isConstOf ``EvaluatesTo && evalArgs.size >= 4 do
      throwError "evaluates_instrs generated a malformed EvaluatesTo goal"
    let evalFields := evalArgs.extract (evalArgs.size - 4) evalArgs.size
    let evalCtx := evalFields[0]!
    let evalEnv := evalFields[1]!
    let term ← goal.withContext do
      withTransparency .all do
        whnf evalFields[2]!
    let expected := evalFields[3]!
    let needsSpec := term.getAppFn.isConstOf ``Term.call || term.getAppFn.isConstOf ``Term.app
    if needsSpec then return [goal]
    let saved ← saveState
    let semanticGoals ← goal.withContext do
      let primCtx ← mkAppM ``Ctx.primCtx #[evalCtx]
      let valueType ← mkAppM ``Val #[primCtx]
      let canonical ← mkFreshExprMVar valueType
      let hcanonicalType ← mkAppM ``EvaluatesTo #[evalCtx, evalEnv, term, canonical]
      let hcanonical ← mkFreshExprSyntheticOpaqueMVar hcanonicalType
      let equalityType ← mkEq canonical expected
      let equality ← mkFreshExprSyntheticOpaqueMVar equalityType
      let iffProof := mkAppN (mkConst ``EvaluatesTo.iff_eq_of)
        #[evalCtx, evalEnv, term, canonical, expected, hcanonical]
      let proof ← mkAppM ``Iff.mpr #[iffProof, equality]
      goal.assign proof
      setGoals [hcanonical.mvarId!]
      try
        evalTactic evalCurrentTactic
        if (← getGoals).isEmpty then
          if ← equality.mvarId!.isAssigned then
            pure (some [])
          else
            setGoals [equality.mvarId!]
            evalTactic (← `(tactic| try rfl))
            pure (some (← getGoals))
        else
          let pending ← getGoals
          let mut stoppedAtSpec := true
          for pendingGoal in pending do
            let pendingTarget ← pendingGoal.withContext do
              instantiateMVars (← pendingGoal.getType)
            let head := pendingTarget.getAppFn
            let pendingArgs := pendingTarget.getAppArgs
            let searchTarget :=
              if head.isConstOf ``EvaluatesFrom && pendingArgs.size >= 4 then
                pendingArgs[pendingArgs.size - 3]!
              else if head.isConstOf ``EvaluatesTo && pendingArgs.size >= 4 then
                pendingArgs[pendingArgs.size - 2]!
              else
                pendingTarget
            let containsSpec := (searchTarget.find? fun subexpr =>
              subexpr.getAppFn.isConstOf ``Term.call ||
                subexpr.getAppFn.isConstOf ``Term.app).isSome
            unless containsSpec && (head.isConstOf ``EvaluatesFrom ||
                head.isConstOf ``EvaluatesTo || head.isConstOf ``EvaluatesCall ||
                head.isConstOf ``EvaluatesApply) do
              stoppedAtSpec := false
          if stoppedAtSpec then
            let equalityGoals ← if ← equality.mvarId!.isAssigned then
                pure []
              else
                setGoals [equality.mvarId!]
                evalTactic (← `(tactic| try rfl))
                getGoals
            pure (some (pending ++ equalityGoals))
          else
            pure none
      catch _ => pure none
    if let some generated := semanticGoals then return generated
    restoreState saved
    setGoals [goal]
    evalTactic directTactic
    return ← getGoals
  if instrs.getAppFn.isConstOf ``List.nil then
    let hresultType ← root.withContext do mkAppM ``EvaluatesTo #[ctx, env, result, value]
    let hresult ← root.withContext do mkFreshExprSyntheticOpaqueMVar hresultType
    let proof ← root.withContext do mkAppM ``EvaluatesInstrs.nil #[hresult]
    root.assign proof
    let pending ← evalCurrent hresult.mvarId!
    setGoals (pending ++ rest)
    return
  unless instrs.getAppFn.isConstOf ``List.cons do
    throwError "evaluates_instrs could not expose the instruction list"
  let listArgs := instrs.getAppArgs
  unless listArgs.size >= 2 do throwError "malformed instruction list"
  let instr := listArgs[listArgs.size - 2]!
  let tail := listArgs[listArgs.size - 1]!
  let primCtx ← root.withContext do mkAppM ``Ctx.primCtx #[ctx]
  let valType ← root.withContext do mkAppM ``Val #[primCtx]
  let instrValue ← root.withContext do mkFreshExprMVar valType
  let instrName ← root.withContext do mkAppM ``Instr.name #[instr]
  let instrTerm ← root.withContext do mkAppM ``Instr.value #[instr]
  let hinstrType ← root.withContext do
    mkAppM ``EvaluatesTo #[ctx, env, instrTerm, instrValue]
  let hinstr ← root.withContext do mkFreshExprSyntheticOpaqueMVar hinstrType
  let tailEnv ← root.withContext do
    let binding ← mkAppM ``Prod.mk #[instrName, instrValue]
    let singleton ← mkListLit (← inferType binding) [binding]
    mkAppM ``List.append #[env, singleton]
  let hrestType ← root.withContext do
    mkAppM ``EvaluatesInstrs #[ctx, tail, result, tailEnv, value]
  let hrest ← root.withContext do mkFreshExprSyntheticOpaqueMVar hrestType
  let proof ← root.withContext do mkAppM ``EvaluatesInstrs.cons #[hinstr, hrest]
  root.assign proof
  let pending ← evalCurrent hinstr.mvarId!
  if pending.isEmpty then
    setGoals (hrest.mvarId! :: rest)
    evaluatesInstrsCore evalCurrentTactic directTactic
  else
    setGoals (pending ++ hrest.mvarId! :: rest)

elab_rules : tactic
| `(tactic| evaluates_instrs $bound:num [$lemmas,*]) => do
    let tactic ← `(tactic|
      (simp only [Instr.ofTerm, List.nil_append]
       apply Zag.EvaluatesTo.of_evaluatesFrom;
       evaluates_from $bound [$lemmas,*]))
    let direct ← `(tactic| evaluates $bound [$lemmas,*])
    evaluatesInstrsCore tactic direct
| `(tactic| evaluates_instrs [$lemmas,*]) => do
    let tactic ← `(tactic|
      (simp only [Instr.ofTerm, List.nil_append]
       apply Zag.EvaluatesTo.of_evaluatesFrom;
       evaluates_from [$lemmas,*]))
    let direct ← `(tactic| evaluates [$lemmas,*])
    evaluatesInstrsCore tactic direct

end Zag
