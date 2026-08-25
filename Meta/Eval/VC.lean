import Lean.Elab.Tactic
import Lean.Meta.Tactic.Apply
import Std.Tactic.Do
import Zag.VC
import Zag.EvalAttr
import Zag.EvalTriple

/-!
# Zag verification-condition generation

Load `@[zspec]` / `@[eval_semantic]` once, then repeatedly `MVarId.apply` (MetaM)
until stuck. Only tactic elaborators are `TacticM`.
-/

namespace Zag

open Lean Elab Tactic Meta

register_option zvcgen.fuel : Nat := {
  defValue := 256
  descr := "maximum refinement steps for zvcgen"
}
register_option zvcgen.resumeReturn : Bool := { defValue := false, descr := "compat" }
register_option zvcgen.useLocalApply : Bool := { defValue := false, descr := "compat" }
initialize registerTraceClass `Zag.zvcgen

syntax (name := normalizeEvalRefinementGoals) "normalize_eval_refinement_goals"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax (name := autoEvalRefinementGoals) "auto_eval_refinement_goals"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax (name := zvcgen) "zvcgen" (ppSpace num)?
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
syntax (name := zvcgenQ) "zvcgen?" (ppSpace num)?
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
syntax (name := zspec) "zspec" ppSpace term : tactic
syntax (name := zspecWithLemmas) "zspec" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic
syntax (name := zintro) "zintro" (ppSpace colGt binderIdent)+ : tactic

macro_rules (kind := zspec)
| `(tactic| zspec $spec) =>
    `(tactic| first
      | apply Zag.EvaluatesTo.consequence $spec
      | apply Zag.EvaluatesFrom.consequence $spec
      | apply Zag.EvaluatesApply.consequence $spec
      | apply Zag.EvaluatesCall.consequence $spec
      | apply Zag.EvaluatesCallValues.consequence $spec
      | apply Zag.VC.StateTriple.of_result $spec
      | apply Zag.VC.Triple.of_result $spec
      | apply Std.Do.Triple.entails_wp_of_pre $spec
      | apply $spec)
macro_rules (kind := zspecWithLemmas)
| `(tactic| zspec $[$bound?]? [$_lemmas,*] $spec) => `(tactic| zspec $spec)


private partial def exposeZIntroPremise (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← withTransparency .all <| whnf (← instantiateMVars (← goal.getType))
  let .forallE _ domain _ _ := target | return goal
  if ← isProp domain then return goal
  let (_, next) ← goal.intro1
  exposeZIntroPremise next

private def loadSpecs : MetaM (Array Name) := do
  let env ← getEnv
  -- Prefer later `@[zspec]` entries (more specific rules) before earlier ones.
  pure (evalSemanticAttr.getEntries env ++ zspecAttr.getEntries env |>.reverse)

private def judgmentHeadOf (e : Expr) : MetaM Name := do
  let t ← instantiateMVars e
  withTransparency .reducible do
    let (_, _, body) ← forallMetaTelescopeReducing t
    let body ← whnf body.consumeMData
    pure (body.getAppFn.constName?.getD Name.anonymous)

private def keepProps (gs : List MVarId) : MetaM (List MVarId) := do
  let mut out : List MVarId := []
  for g in gs do
    if ← g.isAssigned then continue
    let ty ← g.withContext do instantiateMVars (← g.getType)
    if !(← g.withContext do isProp ty) then continue
    if ty.isAppOfArity ``Eq 3 then
      let args := ty.getAppArgs
      let closed ← g.withContext do
        if ← withTransparency .all <| isDefEq args[1]! args[2]! then
          g.assign (← mkEqRefl (← instantiateMVars args[1]!))
          pure true
        else pure false
      unless closed do out := out ++ [g]
    else if ty.getAppFn.isConstOf ``Std.Do.SPred.entails then
      let saved ← saveState
      try
        let _ ← g.apply (← mkConstWithFreshMVarLevels ``Std.Do.SPred.entails.refl)
          { newGoals := .all }
      catch _ =>
        restoreState saved
        out := out ++ [g]
    else
      out := out ++ [g]
  return out

private def tryApply (goal : MVarId) (c : Expr) (rejectOpenEq : Bool := false) :
    MetaM (Option (List MVarId)) := do
  let saved ← saveState
  try
    let gs ← keepProps (← goal.apply c { newGoals := .all })
    if rejectOpenEq then
      for g in gs do
        let ty ← g.withContext do instantiateMVars (← g.getType)
        if ty.isAppOfArity ``Eq 3 then restoreState saved; return none
    return some gs
  catch _ =>
    restoreState saved
    return none

/-- One MetaM step: matching tagged lemma, else intro / `And.intro`. -/
private def refineOnce (goal : MVarId) (specs : Array Name) :
    MetaM (Option (List MVarId)) := goal.withContext do
  if ← goal.isAssigned then return some []
  let gHead ← judgmentHeadOf (← goal.getType)
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hHead ← judgmentHeadOf ldecl.type
    if hHead == gHead || hHead == Name.anonymous then
      if let some gs ← tryApply goal (mkFVar ldecl.fvarId) then return some gs
  for rejectOpenEq in [true, false] do
    for name in specs do
      -- Open combinators that recreate the same judgment head loop under naive apply.
      let s := name.toString
      if s.endsWith ".bind" || s.endsWith ".split" || s.endsWith ".subst" ||
          s.endsWith ".consequence" then
        continue
      try
        let c ← mkConstWithFreshMVarLevels name
        let cHead ← judgmentHeadOf (← inferType c)
        unless cHead == gHead || cHead == Name.anonymous do continue
        if let some gs ← tryApply goal c rejectOpenEq then return some gs
      catch _ => pure ()
  let ty ← withTransparency .all <|
    whnf (← instantiateMVars (← goal.getType)).consumeMData
  if ty.isForall then
    let (_, g) ← goal.introNP 1
    return some [g]
  if ty.getAppFn.isConstOf ``And then
    if let some gs ← tryApply goal (mkConst ``And.intro) then return some gs
  -- Leaf: only when control is already `ret` at the declared base.
  if gHead == ``EvalTriple.Steps || gHead == ``EvalTriple.EvaluatesFrom ||
      gHead == ``Zag.EvaluatesFrom || gHead == ``EvalTriple.ReturnsTo then
    let args := ty.getAppArgs
    let state? :=
      if gHead == ``EvalTriple.Steps && args.size >= 2 then some args[args.size - 2]!
      else if args.size >= 4 then some args[args.size - 4]!
      else none
    if let some stateE := state? then
      let state ← withTransparency .all <| whnf (← instantiateMVars stateE)
      let control ←
        if state.isAppOf ``Machine.Config.mk && state.getAppNumArgs >= 3 then
          withTransparency .all <| whnf (← instantiateMVars state.getAppArgs[state.getAppNumArgs - 3]!)
        else pure state
      if control.getAppFn.isConstOf ``Action.ret then
        if gHead == ``EvalTriple.Steps then
          if let some gs ← tryApply goal (← mkConstWithFreshMVarLevels ``EvalTriple.Steps.done) then
            return some gs
        if gHead == ``EvalTriple.ReturnsTo then
          if let some gs ← tryApply goal (← mkConstWithFreshMVarLevels ``EvalTriple.ReturnsTo.intro) then
            return some gs
        if gHead == ``EvalTriple.EvaluatesFrom || gHead == ``Zag.EvaluatesFrom then
          if let some gs ← tryApply goal (← mkConstWithFreshMVarLevels ``EvalTriple.EvaluatesFrom.done) then
            return some gs
  return none

partial def zvcgenCore (goals : List MVarId) (specs : Array Name) (fuel : Nat) :
    MetaM (List MVarId) := do
  if fuel = 0 then return goals
  let mut leaves : List MVarId := []
  let mut progress := false
  for goal in goals do
    if ← goal.isAssigned then continue
    match ← refineOnce goal specs with
    | some sub => progress := true; leaves := leaves ++ sub
    | none => leaves := leaves ++ [goal]
  if progress then return ← zvcgenCore leaves specs (fuel - 1)
  return leaves

private def runZvcgen (bound? : Option (TSyntax `num)) : TacticM Unit := do
  let defaultFuel := zvcgen.fuel.get (← getOptions)
  let fuel := match bound? with
    | some n => let k := n.getNat; if k = 0 then min defaultFuel 32 else k
    | none => defaultFuel
  setGoals (← zvcgenCore (← getGoals) (← loadSpecs) fuel)

elab_rules : tactic
| `(tactic| zintro $xs:binderIdent*) => do
    let mut g ← getMainGoal
    for ident in xs do
      g ← exposeZIntroPremise g
      let name ← match ident with
        | `(binderIdent| $n:ident) => pure n.getId
        | `(binderIdent| _) => g.withContext do mkFreshUserName `h
        | _ => throwUnsupportedSyntax
      let (_, g') ← g.intro name
      g := g'
    setGoals [g]
| `(tactic| normalize_eval_refinement_goals [$lemmas,*]) => do
    let mut out : List MVarId := []
    for goal in ← getGoals do
      if ← goal.isAssigned then continue
      setGoals [goal]
      try evalTactic (← `(tactic|
        simp -implicitDefEqProofs only
          [List.nil_append, List.append_nil, List.cons.injEq, and_true, true_and,
           Option.some.injEq, Std.Do.Triple.iff, Std.Do.wp, Std.Do.PredTrans.apply,
           Std.Do.PredTrans.pure, Std.Do.PredTrans.pushArg, EvalTriple.ActionPost,
           EvalTriple.Stuck, EvalTriple.StepPost, EvalTriple.At,
           EvalTriple.Singleton.statePost, EvalTriple.Singleton.statePre,
           EvalTriple.Singleton.idPost, EvalTriple.Singleton.idPre,
           Std.Do.SPred.entails, ULift.down, ULift.up, StateT.mk, StateT.run,
           StateT.bind, StateT.pure, StateT.modifyGet, StateT.run_pure,
           MonadState.modifyGet, MonadStateOf.modifyGet, Id.run, Id.run_pure,
           Bind.bind, Pure.pure, $lemmas,*, eval_step, eval_finish]))
      catch _ => pure ()
      try evalTactic (← `(tactic| first | rfl | trivial | exact .rfl | simp))
      catch _ => pure ()
      for g in ← getGoals do
        unless ← g.isAssigned do out := out ++ [g]
    setGoals out
| `(tactic| auto_eval_refinement_goals [$lemmas,*]) => do
    try evalTactic (← `(tactic| all_goals (try simp +arith [$lemmas,*]))) catch _ => pure ()
    evalTactic (← `(tactic| normalize_eval_refinement_goals [$lemmas,*]))
    try evalTactic (← `(tactic| all_goals (try simp_all +arith [$lemmas,*]))) catch _ => pure ()
    try evalTactic (← `(tactic| all_goals (try (first | rfl | trivial | omega | simp_all))))
    catch _ => pure ()
| `(tactic| zvcgen? $[$bound?]? $[[$lemmas,*]]?) => do
    runZvcgen bound?
    match lemmas with
    | some ls => evalTactic (← `(tactic| normalize_eval_refinement_goals [$ls,*]))
    | none => evalTactic (← `(tactic| normalize_eval_refinement_goals []))
| `(tactic| zvcgen $[$bound?]? $[[$lemmas,*]]?) => do
    runZvcgen bound?
    match lemmas with
    | some ls => evalTactic (← `(tactic| auto_eval_refinement_goals [$ls,*]))
    | none => evalTactic (← `(tactic| auto_eval_refinement_goals []))

end Zag
