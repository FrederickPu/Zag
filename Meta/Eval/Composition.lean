import Meta.Eval.Core
import Zag.Meta.Refinement

/-!
# Evaluation call composition

Call specifications and refinement lifting layered directly over the canonical machine walker.
-/

namespace Zag

open Lean Elab Tactic Meta
open Lean.Meta.Sym

private theorem exactCallProofIrrel {ctx : Ctx} {name : String}
    {args : List (Term ctx.primCtx)} {argValues : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {block : Block ctx.primCtx}
    {hM hSpec : ctx.M = Id}
    (hcall : EvalTriple.Exact.EvaluatesCallValues ctx name argValues value hSpec)
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : EvalTriple.Exact.EvaluatesList ctx env args argValues hM) :
    EvalTriple.Exact.EvaluatesTo ctx env (.call name args) value hM := by
  have : hSpec = hM := Subsingleton.elim _ _
  cases this
  exact EvalTriple.Exact.EvaluatesTo.call hcall hblock hargs

private theorem exactCallAutoProofIrrel {ctx : Ctx} {name : String}
    {args : List (Term ctx.primCtx)} {argValues : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {hM hSpec : ctx.M = Id}
    (hcall : EvalTriple.Exact.EvaluatesCallValues ctx name argValues value hSpec)
    (hargs : EvalTriple.Exact.EvaluatesList ctx env args argValues hM) :
    EvalTriple.Exact.EvaluatesTo ctx env (.call name args) value hM := by
  obtain ⟨block, _, hblock, _, _⟩ := hcall [] []
  exact exactCallProofIrrel hcall hblock hargs

private theorem exactCallFromAutoProofIrrel {ctx : Ctx} {name : String}
    {args : List (Term ctx.primCtx)} {argValues : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {stack : List (Frame ctx.primCtx)}
    {hM hSpec : ctx.M = Id}
    (hcall : EvalTriple.Exact.EvaluatesCallValues ctx name argValues value hSpec)
    (hargs : EvalTriple.Exact.EvaluatesList ctx env args argValues hM) :
    EvalTriple.Exact.EvaluatesFrom ctx ⟨.eval (.call name args), env, stack⟩ value stack hM :=
  (exactCallAutoProofIrrel hcall hargs) stack

private theorem exactCallBodyProofIrrel {ctx : Ctx} {name : String}
    {vargs : List (Val ctx.primCtx)} {value : Val ctx.primCtx}
    {callerEnv : Env ctx.primCtx} {base : List (Frame ctx.primCtx)}
    {block : Block ctx.primCtx} {state : Machine.Config ctx.primCtx}
    {hM hSpec : ctx.M = Id}
    (hcall : EvalTriple.Exact.EvaluatesCallValues ctx name vargs value hSpec)
    (hblock : ctx.blockCtx.get? name = some block)
    (henter : Machine.enterBlock name block vargs callerEnv base = some state) :
    EvalTriple.Exact.EvaluatesFrom ctx state value base hM := by
  have : hSpec = hM := Subsingleton.elim _ _
  cases this
  obtain ⟨actualBlock, actualState, hactualBlock, hactualEnter, hbody⟩ :=
    hcall callerEnv base
  rw [hblock] at hactualBlock
  cases hactualBlock
  rw [henter] at hactualEnter
  cases hactualEnter
  exact hbody

syntax (name := evaluatesCallTactic) "evaluates_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := zspecCallTactic) "zspec_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

syntax (name := evaluatesCallMachineTactic) "evaluates_call_machine" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesCallMachineQTactic) "evaluates_call_machine?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := zvcgenCallTactic) "zvcgen_call" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := zspecCallQTactic) "zspec_call?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

syntax (name := evaluatesInstrsTactic) "evaluates_instrs" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evaluatesInstrsOnlyTactic) "evaluates_instrs_only" : tactic

syntax (name := zspecCallCoreTactic) "zspec_call_core" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term (" discharging " tactic)? : tactic

syntax (name := zspecCallApplyTactic) "zspec_call_apply" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term (" discharging " tactic)? : tactic

macro_rules
| `(tactic| zspec_call $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic| zspec_call_core $[$bound?]? [$lemmas,*] $spec)
| `(tactic| zspec_call? $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic| zspec_call_core $[$bound?]? [$lemmas,*] $spec discharging
      (try simp only [eval_finish]))
| `(tactic| zspec_call_core $[$bound?]? [$lemmas,*] $spec $[discharging $close?]?) =>
    `(tactic| zspec_call_apply $[$bound?]? [$lemmas,*] $spec $[discharging $close?]?)
| `(tactic| zspec_call_apply $[$bound?]? [$lemmas,*] $spec $[discharging $close?]?) =>
    `(tactic|
      first
      | exact $spec
      | (apply Zag.exactCallFromAutoProofIrrel $spec
         evaluates_to_all $[$bound?]? [$lemmas,*])
      | (apply Zag.exactCallAutoProofIrrel $spec
         evaluates_to_all $[$bound?]? [$lemmas,*])
      | (refine Zag.EvalTriple.Exact.EvaluatesTo.app ?_ ?_ $spec
         · evaluates $[$bound?]? [$lemmas,*]
         · evaluates_to_all $[$bound?]? [$lemmas,*])
      | (refine Zag.EvalTriple.Exact.EvaluatesFrom.apply_then $spec ?_
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*] $[discharging $close?]?)
      | (refine Zag.EvalTriple.Exact.EvaluatesFrom.eval_then
          (hterm := by
            apply Zag.exactCallAutoProofIrrel $spec
            evaluates_to_all $[$bound?]? [$lemmas,*]) ?_
         · intro scope
           exact Zag.EvalTriple.Exact.EvaluatesFrom.callReturn)
      | (refine Zag.EvalTriple.Exact.EvaluatesFrom.eval_then
          (hterm := by
            apply Zag.exactCallAutoProofIrrel $spec
            evaluates_to_all $[$bound?]? [$lemmas,*]) ?_
         · intro scope
           evaluates_from $[$bound?]? [$lemmas,*] $[discharging $close?]?)
      | (refine Zag.EvalTriple.Exact.EvaluatesFrom.eval_then
          (hterm := Zag.EvalTriple.Exact.EvaluatesTo.app
            ?_ ?_ $spec) ?_
         · evaluates $[$bound?]? [$lemmas,*]
         · evaluates_to_all $[$bound?]? [$lemmas,*]
         · intro scope
           evaluates_from $[$bound?]? [$lemmas,*] $[discharging $close?]?)
      | (refine Zag.EvalTriple.Exact.EvaluatesInstrs.cons
          (by
            apply Zag.exactCallAutoProofIrrel $spec
            evaluates_to_all $[$bound?]? [$lemmas,*]) ?_
         · evaluates_instrs $[$bound?]? [$lemmas,*])
      | (refine Zag.EvalTriple.Exact.EvaluatesInstrs.cons
          (Zag.EvalTriple.Exact.EvaluatesTo.app
            ?_ ?_ $spec) ?_
         · evaluates $[$bound?]? [$lemmas,*]
         · evaluates_to_all $[$bound?]? [$lemmas,*]
         · evaluates_instrs $[$bound?]? [$lemmas,*])
      | (refine Zag.EvalTriple.Exact.EvaluatesFrom.eval_then (hterm := $spec) ?_
         intro scope
         evaluates_from $[$bound?]? [$lemmas,*] $[discharging $close?]?)
       | apply Zag.EvaluatesTo.consequence $spec
       | apply Zag.EvaluatesFrom.consequence $spec
       | apply Zag.EvaluatesCall.consequence $spec
       | apply Zag.EvaluatesCallValues.consequence $spec
       | (apply Zag.exactCallBodyProofIrrel $spec <;> simp [$lemmas,*])
       | (refine Zag.EvalTriple.Exact.EvaluatesFrom.eval_then
           (hterm := by
             apply Zag.exactCallAutoProofIrrel $spec
             evaluates_to_all $[$bound?]? [$lemmas,*]) ?_
          · intro scope
            exact Zag.EvalTriple.Exact.EvaluatesFrom.callReturn)
       | (apply Zag.exactCallAutoProofIrrel $spec
          evaluates_to_all $[$bound?]? [$lemmas,*]))
| `(tactic| evaluates_call_machine $[$bound?]? [$lemmas,*]) =>
    `(tactic| evaluates $[$bound?]? [$lemmas,*])
| `(tactic| evaluates_call_machine? $[$bound?]? [$lemmas,*]) =>
    `(tactic| evaluates $[$bound?]? [$lemmas,*])
| `(tactic| zvcgen_call $[$bound?]? [$lemmas,*]) =>
    `(tactic| evaluates_call $[$bound?]? [$lemmas,*])

private def exactEvalTerm? (goal : MVarId) : MetaM (Option Expr) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesTo do return none
  let args := target.getAppArgs
  unless args.size >= 5 do return none
  return some args[args.size - 3]!

private def shouldStopExactEval (goal : MVarId) : MetaM Bool := do
  let some term ← exactEvalTerm? goal | return false
  let term ← goal.withContext do withTransparency .all <| whnf term
  if term.getAppFn.isConstOf ``Term.call || term.getAppFn.isConstOf ``Term.app then
    return true
  unless term.getAppFn.isConstOf ``Term.op do return false
  let args := term.getAppArgs
  if args.size < 2 then return false
  let name ← goal.withContext do withTransparency .all <| whnf args[args.size - 2]!
  return match name with
    | .lit (.strVal name) => name == "while"
    | _ => false

private partial def evaluatesInstrsCore (core : EvalCoreContext) (bound? : Option (TSyntax `num))
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) (tryGeneric := true) : TacticM Unit := do
  let goals ← getGoals
  let some root := goals.head? | return
  let parentTag ← root.getTag
  let target ← root.withContext do instantiateMVars (← root.getType)
  unless target.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesInstrs do
    throwError "evaluates_instrs expected an exact EvaluatesInstrs goal"
  let args := target.getAppArgs
  unless args.size >= 6 do throwError "malformed exact EvaluatesInstrs goal"
  let instrs ← root.withContext do withTransparency .all <| whnf args[args.size - 5]!
  setGoals [root]
  if instrs.getAppFn.isConstOf ``List.nil then
    evalTactic (← `(tactic| apply Zag.EvalTriple.Exact.EvaluatesInstrs.nil))
    let resultGoals ← getGoals
    let some result := resultGoals.head? | setGoals goals.tail; return
    result.setTag parentTag
    if tryGeneric then
      let canonical? ← withAssignableSyntheticOpaque <|
        SymM.run <| decomposeCanonicalEval? result (evalBoundOf bound?) core
      if let some generated := canonical? then
        setGoals (generated ++ goals.tail)
        return
      let saved ← saveState
      try evaluatesCoreWith core (evalBoundOf bound?) lemmas
      catch _ => restoreState saved
      unless (← getGoals).isEmpty do
        restoreState saved
        setGoals [result]
    setGoals ((← getGoals) ++ goals.tail)
    return
  unless instrs.getAppFn.isConstOf ``List.cons do
    throwError "evaluates_instrs could not expose the instruction list"
  let listArgs := instrs.getAppArgs
  let instr := listArgs[listArgs.size - 2]!
  let instrsTail := listArgs[listArgs.size - 1]!
  let ctx := args[args.size - 6]!
  let result := args[args.size - 4]!
  let env := args[args.size - 3]!
  let value := args[args.size - 2]!
  let hM := args[args.size - 1]!
  let instrValue ← root.withContext do
    let primCtx ← mkAppM ``Ctx.primCtx #[ctx]
    mkFreshExprMVar (← mkAppM ``Val #[primCtx])
  let instrTerm ← root.withContext do mkAppM ``Instr.value #[instr]
  let headType ← root.withContext do
    mkAppM ``EvalTriple.Exact.EvaluatesTo #[ctx, env, instrTerm, instrValue, hM]
  let head ← root.withContext do mkFreshExprSyntheticOpaqueMVar headType
  let tailEnv ← root.withContext do
    let instrName ← mkAppM ``Instr.name #[instr]
    let binding ← mkAppM ``Prod.mk #[instrName, instrValue]
    let singleton ← mkListLit (← inferType binding) [binding]
    mkAppM ``List.append #[env, singleton]
  let tailType ← root.withContext do
    mkAppM ``EvalTriple.Exact.EvaluatesInstrs
      #[ctx, instrsTail, result, tailEnv, value, hM]
  let tail ← root.withContext do mkFreshExprSyntheticOpaqueMVar tailType
  root.assign (← root.withContext do
    mkAppM ``EvalTriple.Exact.EvaluatesInstrs.cons #[head, tail])
  let head := head.mvarId!
  let tail := tail.mvarId!
  head.setTag parentTag
  tail.setTag parentTag
  if !tryGeneric || (← shouldStopExactEval head) then
    setGoals ([head, tail] ++ goals.tail)
    return
  setGoals [head]
  let saved ← saveState
  try evaluatesCoreWith core (evalBoundOf bound?) lemmas
  catch _ => restoreState saved
  if (← getGoals).isEmpty then
    setGoals [tail]
    evaluatesInstrsCore core bound? lemmas
    setGoals ((← getGoals) ++ goals.tail)
  else
    restoreState saved
    setGoals ((← getGoals) ++ [tail] ++ goals.tail)

elab_rules : tactic
| `(tactic| evaluates_call $[$bound?]? [$lemmas,*]) => do
    let core ← mkEvalCoreContext lemmas.getElems
    let goal ← getMainGoal
    let saved ← saveState
    let decomposed ← try
      let parentTag ← goal.getTag
      let target ← goal.withContext do instantiateMVars (← goal.getType)
      unless target.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesCallValues do
        throwError "not an exact value-call goal"
      let args := target.getAppArgs
      unless args.size >= 5 do throwError "malformed exact value-call goal"
      let ctx := args[args.size - 5]!
      let name := args[args.size - 4]!
      let vargs := args[args.size - 3]!
      let value := args[args.size - 2]!
      let hM := args[args.size - 1]!
      let blockCtx ← goal.withContext do mkAppM ``Ctx.blockCtx #[ctx]
      let lookup ← goal.withContext do mkAppM ``BlockCtx.get? #[blockCtx, name]
      let reducedLookup ← goal.withContext do withTransparency .all <| whnf lookup
      unless reducedLookup.getAppFn.isConstOf ``Option.some do
        throwError "could not resolve the called block"
      let lookupArgs := reducedLookup.getAppArgs
      let block := lookupArgs[lookupArgs.size - 1]!
      let someBlock ← goal.withContext do mkAppM ``Option.some #[block]
      let hblock ← goal.withContext do
        mkFreshExprSyntheticOpaqueMVar (← mkEq lookup someBlock)
      let vargsLength ← goal.withContext do mkAppM ``List.length #[vargs]
      let params ← goal.withContext do mkAppM ``Block.params #[block]
      let paramsLength ← goal.withContext do mkAppM ``List.length #[params]
      let hargs ← goal.withContext do
        mkFreshExprSyntheticOpaqueMVar (← mkEq vargsLength paramsLength)
      let instrs ← goal.withContext do mkAppM ``Block.instrs #[block]
      let result ← goal.withContext do mkAppM ``Block.result #[block]
      let env ← goal.withContext do mkAppM ``Block.entryEnv #[block, vargs]
      let instrsWhnf ← goal.withContext do withTransparency .all <| whnf instrs
      let resultWhnf ← goal.withContext do withTransparency .all <| whnf result
      -- Empty-bodied self-exits need the call frame; `of_evaluatesInstrs` cannot install it.
      let exitTerm? ← goal.withContext do
        unless instrsWhnf.getAppFn.isConstOf ``List.nil do return none
        unless resultWhnf.getAppFn.isConstOf ``Term.exit do return none
        let exitArgs := resultWhnf.getAppArgs
        unless exitArgs.size >= 2 do return none
        let exitName ← withTransparency .all <| whnf exitArgs[exitArgs.size - 2]!
        unless ← withTransparency .all <| isDefEq exitName name do return none
        return some exitArgs[exitArgs.size - 1]!
      if let some exitTerm := exitTerm? then
        let emptyInstrs ← goal.withContext do
          let primCtx ← mkAppM ``Ctx.primCtx #[ctx]
          let instrTy ← mkAppM ``Instr #[primCtx]
          mkAppOptM ``List.nil #[some instrTy]
        let hinstrs ← goal.withContext do
          mkFreshExprSyntheticOpaqueMVar (← mkEq instrs emptyInstrs)
        let expectedResult ← goal.withContext do mkAppM ``Term.exit #[name, exitTerm]
        let hresult ← goal.withContext do
          mkFreshExprSyntheticOpaqueMVar (← mkEq result expectedResult)
        let hvalueType ← goal.withContext do
          mkAppM ``EvalTriple.Exact.EvaluatesTo #[ctx, env, exitTerm, value, hM]
        let hvalue ← goal.withContext do mkFreshExprSyntheticOpaqueMVar hvalueType
        goal.assign (← goal.withContext do
          mkAppM ``EvalTriple.Exact.EvaluatesCallValues.of_exit
            #[hblock, hargs, hinstrs, hresult, hvalue])
        let proofGoals := [hblock.mvarId!, hargs.mvarId!, hinstrs.mvarId!, hresult.mvarId!,
          hvalue.mvarId!]
        for generated in proofGoals do generated.setTag parentTag
        setGoals proofGoals
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        if let some generated := (← getGoals).head? then
          let generatedType ← generated.withContext do instantiateMVars (← generated.getType)
          if generatedType.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesTo then
            evaluatesCoreWith core (evalBoundOf bound?) lemmas.getElems
        pure true
      else
        let hbodyType ← goal.withContext do
          mkAppM ``EvalTriple.Exact.EvaluatesInstrs #[ctx, instrs, result, env, value, hM]
        let hbody ← goal.withContext do mkFreshExprSyntheticOpaqueMVar hbodyType
        goal.assign (← goal.withContext do
          mkAppM ``EvalTriple.Exact.EvaluatesCallValues.of_evaluatesInstrs
            #[hblock, hargs, hbody])
        let proofGoals := [hblock.mvarId!, hargs.mvarId!, hbody.mvarId!]
        for generated in proofGoals do generated.setTag parentTag
        setGoals proofGoals
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        evalTactic (← `(tactic| first | rfl | simp [$lemmas,*]))
        if let some generated := (← getGoals).head? then
          let generatedType ← generated.withContext do instantiateMVars (← generated.getType)
          if generatedType.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesInstrs then
            evaluatesInstrsCore core bound? lemmas.getElems
        pure true
    catch _ =>
      restoreState saved
      pure false
    unless decomposed do
      evaluatesCoreWith core (evalBoundOf bound?) lemmas.getElems

elab_rules : tactic
| `(tactic| evaluates_instrs $[$bound?]? [$lemmas,*]) =>
    do evaluatesInstrsCore (← mkEvalCoreContext lemmas.getElems) bound? lemmas.getElems
| `(tactic| evaluates_instrs_only) =>
    do evaluatesInstrsCore (← mkEvalCoreContext #[]) none #[] false

end Zag
