import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.Simp.Main
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Apply
import Lean.Meta.Sym.Intro
import Zag.EvalState
import Zag.Loop

/-!
# Small-step evaluator core

This module owns only machine walking, fuel, operator finalizers, and evaluation of argument
lists. Composition with call and application specifications lives in `Meta.Eval.Refinement`.
-/

namespace Zag

open Lean Elab Tactic Meta
open Lean.Meta.Sym

builtin_initialize registerTraceClass `Zag.eval.sym

/-- Upper bound used when a caller does not give one. Reaching it means evaluation did not halt,
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
  op : Expr
  probe : TSyntax `tactic
  run : TSyntax `tactic

/-- The original tactic-driven walker, retained as a compatibility fallback when `Sym.simp` cannot
  normalize a machine step using its more restrictive theorem language. -/
private partial def evaluatesFromCoreLegacy (bound : Nat)
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

/-- Return the explicit tail fields of a constructor or function application. This is the only
  place where evaluator metadata depends on Lean's inclusion of implicit parameters in app args. -/
private def trailingAppArgs? (expr : Expr) (head : Name) (count : Nat) : Option (Array Expr) := do
  guard (expr.getAppFn.isConstOf head)
  let args := expr.getAppArgs
  guard (args.size >= count)
  return args.extract (args.size - count) args.size

private def appArg? (expr : Expr) (head : Name) : Option Expr := do
  return (← trailingAppArgs? expr head 1)[0]!

private def appArgs2? (expr : Expr) (head : Name) : Option (Expr × Expr) := do
  let args ← trailingAppArgs? expr head 2
  return (args[0]!, args[1]!)

private structure EvalStateView where
  primCtx : Expr
  control : Expr
  env : Expr
  stack : Expr

private def EvalStateView.ofExpr? (state : Expr) : Option EvalStateView := do
  let args ← trailingAppArgs? state ``EvalState.mk 4
  return { primCtx := args[0]!, control := args[1]!, env := args[2]!, stack := args[3]! }

/-- Convert an elaborated ordinary simp set into the structural theorem set used by `Sym.simp`.
  It is used only for equality premises exposed by backward transition rules. -/
private def mkEvalSymSimpMethods
    (simpTheorems : SimpTheoremsArray) : MetaM Sym.Simp.Methods := do
  let env ← getEnv
  let mut evalHeuristics : Sym.Simp.Theorems := {}
  let mut evalTheorems : Sym.Simp.Theorems := {}
  for simpSet in simpTheorems do
    for simpTheorem in simpSet.pre.values ++ simpSet.post.values do
      if simpTheorems.isErased simpTheorem.origin then continue
      try
        let thm ← Sym.Simp.mkTheoremFromExpr simpTheorem.proof
        evalTheorems := evalTheorems.insert thm
        -- Generated equations for tagged definitions are theorem declarations too, but their
        -- original declaration kind identifies them. Keep them post-only so authored rules get
        -- the first chance before the generic operator transition procedure.
        if !simpTheorem.rfl then
          let originDecl? := match simpTheorem.origin with
            | .decl declName .. => some declName
            | _ => none
          match originDecl? with
          | some declName =>
            if (declFromEqLikeName env declName).isNone then
              evalHeuristics := evalHeuristics.insert thm
          | none => evalHeuristics := evalHeuristics.insert thm
      catch _ => pure ()
  for declName in #[``Option.bind_none, ``Option.bind_some] do
    evalTheorems := evalTheorems.insert (← Sym.Simp.mkTheoremFromDecl declName)
  return {
    pre := Sym.Simp.simpControl <|>
      evalHeuristics.rewrite Sym.Simp.dischargeSimpSelf
    post := Sym.Simp.evalGround >>
      evalTheorems.rewrite Sym.Simp.dischargeSimpSelf
  }

/-- Elaborate `eval_step` and the caller's lemmas once instead of rebuilding them at each step. -/
private def elabEvalSymSimpMethods
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Sym.Simp.Methods := do
  let simpStx ← `(tactic| simp only [eval_step, $lemmas,*])
  let result ← mkSimpContext simpStx.raw (eraseLocal := false)
  mkEvalSymSimpMethods result.ctx.simpTheorems

/-- Compile registered whole-term semantics once for an evaluator invocation. -/
def mkEvalSemanticRules : MetaM (Array Sym.BackwardRule) := do
  let entries := evalSemanticAttr.getEntries (← getEnv)
  entries.mapM Sym.mkBackwardRuleFromDecl

private structure EvalBackwardRules where
  evalThen : Sym.BackwardRule
  op : Sym.BackwardRule
  eval : Sym.BackwardRule
  apply : Sym.BackwardRule
  ret : Sym.BackwardRule
  exit : Sym.BackwardRule

/-- Compile the fixed relation-level transitions once for an evaluator invocation. -/
private def mkEvalBackwardRules : MetaM EvalBackwardRules := do
  return {
    evalThen := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.eval_then
    op := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.op_step
    eval := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.eval_step
    apply := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.apply_step
    ret := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.ret_step
    exit := ← Sym.mkBackwardRuleFromDecl ``EvaluatesFrom.exit_step
  }

private inductive EvalSymResult where
  | atResult (goal : MVarId) (remaining : Nat)
  | stopped (goal : MVarId)
  | finalizer (goal : MVarId)
  | fallback (goal : MVarId) (remaining : Nat)

private structure EvaluatesFromTarget where
  target : Expr
  ctx : Expr
  state : Expr
  value : Expr
  base : Expr

private def EvaluatesFromTarget.ofExpr? (target : Expr) : Option EvaluatesFromTarget := do
  let args ← trailingAppArgs? target ``EvaluatesFrom 4
  return { target, ctx := args[0]!, state := args[1]!, value := args[2]!, base := args[3]! }

private def EvaluatesFromTarget.ofGoal? (goal : MVarId) : SymM (Option EvaluatesFromTarget) :=
    goal.withContext do
  let target ← instantiateMVarsS (← goal.getType)
  return EvaluatesFromTarget.ofExpr? target

private structure EvaluatesToTarget where
  ctx : Expr
  env : Expr
  term : Expr
  value : Expr

private def EvaluatesToTarget.ofExpr? (target : Expr) : Option EvaluatesToTarget := do
  let args ← trailingAppArgs? target ``EvaluatesTo 4
  return { ctx := args[0]!, env := args[1]!, term := args[2]!, value := args[3]! }

/-- Close a side equality by symbolic normalization, retaining the generated proof. -/
private def solveSemanticEq (goal : MVarId) (methods : Sym.Simp.Methods)
    (simpState : Sym.Simp.State) : SymM (Option Sym.Simp.State) := goal.withContext do
  let target ← instantiateMVarsS (← goal.getType)
  let some (lhs, rhs) := appArgs2? target ``Eq | return none
  if ← Sym.isDefEqS lhs rhs then
    goal.assign (← Sym.mkEqRefl lhs)
    return some simpState
  let (result, simpState) ←
    Sym.Simp.SimpM.run (Sym.Simp.simp lhs) methods {} simpState
  let resultExpr ← withTransparency .all <| whnf (result.getResultExpr lhs)
  unless ← Sym.isDefEqS resultExpr rhs do return none
  let proof ← match result with
    | .rfl .. => Sym.mkEqRefl lhs
    | .step _ proof .. => pure proof
  goal.assign proof
  return some simpState

/-- Apply a backward rule only after all of its hidden instance arguments have been synthesized. -/
def applyEvalBackwardRule? (goal : MVarId) (rule : Sym.BackwardRule) :
    SymM (Option (List MVarId)) := goal.withContext do
  let decl ← goal.getDecl
  let some result ← rule.pattern.unify? decl.type | return none
  for h : i in [:result.args.size] do
    let isInstance := match rule.pattern.varInfos? with
      | some infos => infos.argsInfo[i]!.isInstance
      | none => false
    if isInstance then
      let arg ← instantiateMVarsS result.args[i]
      if let .mvar mvarId := arg then
        let type ← instantiateMVarsS (← mvarId.getType)
        let some inst ← Sym.synthInstance? type | return none
        mvarId.assign inst
  let value := if let .const declName [] := rule.expr then
      mkAppN (mkConst declName result.us) result.args
    else
      mkAppN (rule.expr.instantiateLevelParams rule.pattern.levelParams result.us) result.args
  goal.assign value
  return some <| rule.resultPos.map fun i => result.args[i]!.mvarId!

/-- Apply cached semantic rules recursively, solving operator operands without leaving `SymM`. -/
private partial def solveSemanticEval (goal : MVarId) (rules : Array Sym.BackwardRule)
    (methods : Sym.Simp.Methods) (simpState : Sym.Simp.State)
    (activeTerms : Array Expr := #[]) : SymM (Option Sym.Simp.State) := goal.withContext do
  let target ← instantiateMVarsS (← goal.getType)
  let some evalTarget := EvaluatesToTarget.ofExpr? target | return none
  if activeTerms.any fun term => isSameExpr term evalTarget.term then return none
  for rule in rules do
    let mctxSaved ← getMCtx
    let symSaved ← get
    match ← applyEvalBackwardRule? goal rule with
    | none =>
        setMCtx mctxSaved
        set symSaved
    | some subgoals =>
        let mut state := simpState
        let mut solved := true
        for subgoal in subgoals do
          if ← subgoal.isAssigned then continue
          let subtarget ← instantiateMVarsS (← subgoal.getType)
          if (EvaluatesToTarget.ofExpr? subtarget).isSome then
            match ← solveSemanticEval subgoal rules methods state
                (activeTerms.push evalTarget.term) with
            | some nextState => state := nextState
            | none => solved := false
          else
            match ← solveSemanticEq subgoal methods state with
            | some nextState => state := nextState
            | none => solved := false
          unless solved do break
        if solved then return some state
        setMCtx mctxSaved
        set symSaved
  return none

private structure AppliedTransition where
  goal : MVarId
  target : EvaluatesFromTarget
  simpState : Sym.Simp.State

/-- Backward-apply one machine transition and solve only the equalities it exposes. -/
private def applyMachineTransition? (goal : MVarId) (rule : Sym.BackwardRule)
    (methods : Sym.Simp.Methods) (simpState : Sym.Simp.State) :
    SymM (Option AppliedTransition) := goal.withContext do
  let mctxSaved ← getMCtx
  let symSaved ← get
  let subgoals? ← match ← applyEvalBackwardRule? goal rule with
    | some subgoals => pure (some subgoals)
    | none => goal.withContext do
        try
          let expr ← match rule.expr with
            | .const name _ => mkConstWithFreshMVarLevels name
            | expr => pure expr
          return some (← goal.apply expr { newGoals := .all })
        catch _ => return none
  let some subgoals := subgoals?
    | setMCtx mctxSaved; set symSaved; return none
  let mut state := simpState
  let mut nextGoal? : Option MVarId := none
  let mut solved := true
  for subgoal in subgoals do
    if ← subgoal.isAssigned then continue
    let target ← instantiateMVarsS (← subgoal.getType)
    if (EvaluatesFromTarget.ofExpr? target).isSome then
      if nextGoal?.isSome then
        solved := false
      else
        nextGoal? := some subgoal
    else if (appArgs2? target ``Eq).isSome then
      match ← solveSemanticEq subgoal methods state with
      | some nextState => state := nextState
      | none => solved := false
    unless solved do break
  if solved then
    for subgoal in subgoals do
      if some subgoal == nextGoal? then continue
      unless ← subgoal.isAssigned do solved := false
  if solved then
    if let some nextGoal := nextGoal? then
      if let some target ← EvaluatesFromTarget.ofGoal? nextGoal then
        nextGoal.setTag (← goal.getTag)
        return some { goal := nextGoal, target, simpState := state }
  setMCtx mctxSaved
  set symSaved
  return none

/-- Backward-apply `eval_then`, solve its semantic premise, and introduce its continuation. -/
private def applySemanticTransition? (goal : MVarId) (rule : Sym.BackwardRule)
    (semanticRules : Array Sym.BackwardRule) (methods : Sym.Simp.Methods)
    (simpState : Sym.Simp.State) : SymM (Option AppliedTransition) := goal.withContext do
  let mctxSaved ← getMCtx
  let symSaved ← get
  let some subgoals ← applyEvalBackwardRule? goal rule
    | setMCtx mctxSaved; set symSaved; return none
  let mut state := simpState
  let mut nextGoal? : Option MVarId := none
  let mut solved := true
  for subgoal in subgoals do
    if ← subgoal.isAssigned then continue
    let target ← instantiateMVarsS (← subgoal.getType)
    if (EvaluatesToTarget.ofExpr? target).isSome then
      match ← solveSemanticEval subgoal semanticRules methods state with
      | some nextState => state := nextState
      | none => solved := false
    else if target.isForall then
      match ← Sym.introN subgoal 1 with
      | .goal _ nextGoal => nextGoal? := some nextGoal
      | .failed => solved := false
    unless solved do break
  if solved then
    for subgoal in subgoals do
      unless ← subgoal.isAssigned do solved := false
  if solved then
    if let some nextGoal := nextGoal? then
      if let some target ← EvaluatesFromTarget.ofGoal? nextGoal then
        nextGoal.setTag (← goal.getTag)
        return some { goal := nextGoal, target, simpState := state }
  setMCtx mctxSaved
  set symSaved
  return none

private def isCallControl (control : Expr) : Bool :=
  match appArg? control ``Action.eval with
  | some term => (appArgs2? term ``Term.call).isSome
  | none => false

private def isApplyControl (control : Expr) : Bool :=
  (appArgs2? control ``Action.apply).isSome

private def isSelectedOpControl (control : Expr) (op : Expr) : MetaM Bool :=
    withoutModifyingState do match appArg? control ``Action.eval with
  | some term => match appArgs2? term ``Term.op with
    | some (name, _) => withTransparency .reducible <| isDefEq name op
    | none => pure false
  | none => pure false

/-- Fully concrete machine runs are cheaper as direct execution than as one VC per transition. -/
private def isConcreteMachineGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some evalTarget := EvaluatesFromTarget.ofExpr? target | return false
  let primCtx ← mkAppM ``Ctx.primCtx #[evalTarget.ctx]
  let envType ← mkAppM ``Env #[primCtx]
  let frameType ← mkAppM ``Frame #[primCtx]
  let stackType ← mkAppM ``List #[frameType]
  let fvars := (collectFVars (collectFVars {} evalTarget.state) evalTarget.value).fvarIds
  for fvarId in fvars do
    let type ← inferType (mkFVar fvarId)
    unless (← isDefEq type envType) || (← isDefEq type stackType) do return false
  return true

/-- Generate one successor verification condition per machine or registered semantic transition
  in a single `SymM` session. Each transition is committed immediately, so stopping and fallback
  never replay a successful prefix. Goal-closing and user-provided finalizers remain at the
  `TacticM` boundary. -/
private partial def evaluatesFromVC (goal : MVarId) (bound : Nat)
    (methods : Sym.Simp.Methods) (semanticRules : Array Sym.BackwardRule)
    (backwardRules : EvalBackwardRules) (finalizerOp? : Option Expr) (stopAtApply : Bool) :
    SymM EvalSymResult := do
  let tag ← goal.getTag
  let goal ← preprocessMVar goal
  goal.setTag tag
  let finalizerOp? ← finalizerOp?.mapM fun op => do
    shareCommon (← instantiateMVars op)
  let some evalTarget ← EvaluatesFromTarget.ofGoal? goal
    | return .fallback goal bound
  go goal evalTarget evalTarget.state 0 bound {} finalizerOp?
where
  go (goal : MVarId) (evalTarget : EvaluatesFromTarget) (state : Expr) (steps remaining : Nat)
      (simpState : Sym.Simp.State) (finalizerOp? : Option Expr) :
      SymM EvalSymResult := goal.withContext do
    let some stateView := EvalStateView.ofExpr? state
      | return .fallback goal remaining
    if (appArg? stateView.control ``Action.ret).isSome &&
        isSameExpr stateView.stack evalTarget.base then
      trace[Zag.eval.sym] "result after {steps} steps: {evalTarget.target}"
      return .atResult goal remaining
    if isCallControl stateView.control then
      return .stopped goal
    if let some op := finalizerOp? then
      if ← isSelectedOpControl stateView.control op then
        return .finalizer goal
    if stopAtApply && isApplyControl stateView.control then
      return .stopped goal
    if remaining = 0 then
      return .stopped goal
    if let some term := appArg? stateView.control ``Action.eval then
      if (appArgs2? term ``Term.op).isSome then
        if let some applied ← applySemanticTransition? goal backwardRules.evalThen
            semanticRules methods simpState then
          trace[Zag.eval.sym] "semantic evaluation: {term}"
          return ← go applied.goal applied.target applied.target.state (steps + 1)
            (remaining - 1) applied.simpState finalizerOp?
    let rule? :=
      if let some term := appArg? stateView.control ``Action.eval then
        if (appArgs2? term ``Term.op).isSome then some backwardRules.op
        else some backwardRules.eval
      else if (appArgs2? stateView.control ``Action.apply).isSome then some backwardRules.apply
      else if (appArg? stateView.control ``Action.ret).isSome then some backwardRules.ret
      else if (appArgs2? stateView.control ``Action.exit).isSome then some backwardRules.exit
      else none
    let some rule := rule?
      | trace[Zag.eval.sym] "fallback: no transition rule for {state}"
        return .fallback goal remaining
    let some applied ← applyMachineTransition? goal rule methods simpState
      | trace[Zag.eval.sym] "fallback: transition rule failed for {state}"
        return .fallback goal remaining
    go applied.goal applied.target applied.target.state (steps + 1) (remaining - 1)
      applied.simpState finalizerOp?

/-- Walk an `EvaluatesFrom` goal one `step` at a time until it is discharged or nothing applies. -/
partial def evaluatesFromCore (bound : Nat)
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (close : TSyntax `tactic) (finalizer? : Option EvalFinalizer := none)
    (stopAtApply : Bool := false) :
    TacticM Unit := do
  let goals ← getGoals
  let some root := goals.head? | return
  if ← isConcreteMachineGoal root then
    evaluatesFromCoreLegacy bound lemmas close finalizer? stopAtApply
    return
  let methods ← elabEvalSymSimpMethods lemmas
  let semanticRules ← mkEvalSemanticRules
  let backwardRules ← mkEvalBackwardRules
  let result ← SymM.run <|
    evaluatesFromVC root bound methods semanticRules backwardRules
      (finalizer?.map (·.op)) stopAtApply
  let setMain (goal : MVarId) := setGoals (goal :: goals.tail)
  match result with
  | .atResult goal remaining =>
      setMain goal
      if ← tryStep (← `(tactic| exact Zag.EvaluatesFrom.done)) then return
      if ← tryStep (← `(tactic| refine Zag.EvaluatesFrom.done_of ?_)) then
        evalTactic close
        return
      evaluatesFromCoreLegacy remaining lemmas close finalizer? stopAtApply
  | .stopped goal =>
      setMain goal
      evalTactic (← `(tactic| try simp only [eval_fold]))
  | .finalizer goal =>
      setMain goal
      let some finalizer := finalizer? | unreachable!
      evalTactic finalizer.run
  | .fallback goal remaining =>
      setMain goal
      evaluatesFromCoreLegacy remaining lemmas close finalizer? stopAtApply

/-- The bound a caller wrote, or `evalStepBound`. -/
private def boundOf (bound? : Option (TSyntax `num)) : Nat :=
  match bound? with
  | some n => n.getNat
  | none => evalStepBound

/-- Use registered whole-term semantics before falling back to bounded machine reduction. -/
private def evaluatesCore (bound : Nat)
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let goals ← getGoals
  let some root := goals.head? | return
  let methods ← elabEvalSymSimpMethods lemmas
  let rules ← mkEvalSemanticRules
  if (← SymM.run <| solveSemanticEval root rules methods {}).isSome then
    setGoals goals.tail
    return
  let fuel := Lean.Syntax.mkNumLit (toString bound)
  evalTactic (← `(tactic|
    (focus
       rw [Zag.EvaluatesTo.iff_run]
       refine ⟨$fuel, ?_⟩
     all_goals
       set_option linter.unusedSimpArgs false in
         simp +arith [eval_step, Zag.EvalState.run,
           Zag.EvalState.start, Zag.EvalState.result?, $lemmas,*] <;>
         try rfl)))

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
    let opExpr ← instantiateMVars (← Term.elabTerm op (some (mkConst ``String)))
    let probe ← `(tactic| refine Zag.EvaluatesFrom.atOp (name := $op) ?_)
    evaluatesFromCore (boundOf bound?) lemmas.getElems close
      (finalizer? := some { op := opExpr, probe, run := finalizer })
      (stopAtApply := stopApply?.isSome)
| `(tactic| evaluates $[$bound?]? [$lemmas,*]) =>
    evaluatesCore (boundOf bound?) lemmas.getElems

private def listView (xs : Expr) : MetaM (Option (Expr × Expr)) := do
  let xs ← whnf xs
  if xs.isAppOfArity ``List.nil 1 then
    return none
  unless xs.isAppOfArity ``List.cons 3 do
    throwError "expected a concrete argument list, got {xs}"
  let args := xs.getAppArgs
  return some (args[1]!, args[2]!)

private def listConsView (xs : Expr) : MetaM (Expr × Expr) := do
  let xs ← instantiateMVars xs
  if xs.isMVar then
    let xsType ← inferType xs
    let typeArgs := (← whnf xsType).getAppArgs
    let value ← mkFreshExprMVar typeArgs[0]!
    let values ← mkFreshExprMVar xsType
    xs.mvarId!.assign (← mkAppM ``List.cons #[value, values])
    return (value, values)
  let some view ← listView xs
    | throwError "expected a nonempty value list, got {xs}"
  return view

private def primitiveEvalProof? (ctx env target term : Expr) : MetaM (Option Expr) := do
  let term ← whnf term
  unless term.isAppOfArity ``Term.prim 3 do return none
  let termArgs := term.getAppArgs
  let proof := mkAppN (mkConst ``EvaluatesTo.prim)
    #[ctx, env, termArgs[1]!, termArgs[2]!]
  unless ← isDefEq (← inferType proof) target do return none
  return some proof

private partial def evaluatesToAllCore (bound? : Option (TSyntax `num))
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let goals ← getGoals
  let some root := goals.head? | return
  let target ← root.withContext do instantiateMVars (← root.getType)
  unless target.isAppOfArity ``EvaluatesToAll 4 do
    throwError "expected an EvaluatesToAll goal, got {target}"
  let args := target.getAppArgs
  let terms? ← root.withContext do listView args[2]!
  match terms? with
  | none =>
      setGoals [root]
      evalTactic (← `(tactic| exact Zag.EvaluatesToAll.nil))
      setGoals goals.tail
  | some (term, terms) =>
      let (value, values) ← root.withContext do listConsView args[3]!
      let headType ← root.withContext do mkAppM ``EvaluatesTo #[args[0]!, args[1]!, term, value]
      let head ← root.withContext do mkFreshExprSyntheticOpaqueMVar headType
      let tailType ← root.withContext do mkAppM ``EvaluatesToAll #[args[0]!, args[1]!, terms, values]
      let tail ← root.withContext do mkFreshExprSyntheticOpaqueMVar tailType
      root.assign (← root.withContext do mkAppM ``EvaluatesToAll.cons #[head, tail])
      let primitive? ← root.withContext do
        primitiveEvalProof? args[0]! args[1]! headType term
      let pending ← match primitive? with
        | some proof =>
            head.mvarId!.assign proof
            pure []
        | none =>
            setGoals [head.mvarId!]
            let direct ← `(tactic|
              first
              | exact Zag.EvaluatesTo.var_local (by rfl)
              | exact Zag.EvaluatesTo.var_block (by rfl) (by simp [$lemmas,*])
              | evaluates $[$bound?]? [$lemmas,*])
            evalTactic direct
            getGoals
      if pending.isEmpty then
        setGoals (tail.mvarId! :: goals.tail)
        evaluatesToAllCore bound? lemmas
      else
        setGoals (pending ++ tail.mvarId! :: goals.tail)

elab_rules : tactic
| `(tactic| evaluates_to_all $[$bound?]? [$lemmas,*]) =>
    evaluatesToAllCore bound? lemmas.getElems

end Zag
