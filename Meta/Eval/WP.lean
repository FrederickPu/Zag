import Lean.Elab.Tactic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Subst
import Meta.Eval.Composition

/-!
# Evaluation weakest-precondition composition

Application specifications, parameterized refinement lifting, normalization, and generic
processing of evaluation WP obligations.
-/

namespace Zag

open Lean Elab Tactic Meta
open Lean.Meta.Sym

/-- Discharge an application stopped by `stopping_at_apply`, then continue walking. -/
syntax (name := useApplyTactic) "use_apply" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term (" discharging " tactic)? : tactic

/-- The non-closing application form used by obligation processors. -/
syntax (name := useApplyQTactic) "use_apply?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term : tactic

/-- Select parameters before lifting one WP refinement through the current continuation. -/
syntax (name := applyEvalWPRefinementTactic) "apply_eval_wp_refinement" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " selecting " term
  " naming" " [" ident,* "]" : tactic

/-- Normalize evaluation wrappers without arithmetic search. -/
syntax (name := normalizeEvalRefinementGoals) "normalize_eval_refinement_goals"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Best-effort simplification and arithmetic closure for normalized obligations. -/
syntax (name := autoEvalRefinementGoals) "auto_eval_refinement_goals"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Process freshly generated evaluation WP goals by their proposition and evaluation shape. -/
syntax (name := processEvalWPGoals) "process_eval_wp_goals" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

syntax (name := evalDischargeTactic) "eval_discharge " tactic : tactic

/-- One public verification-condition root produced by a direct semantic finalizer. -/
inductive EvalSemanticRoot where
  | goal (name : Name) (goal : MVarId)
  | residual (name : Name) (goal : MVarId)
  | forallAnd (leftName rightName : Name) (goal : MVarId)

/-- The result of applying a direct semantic finalizer. Prerequisites must close before its named
  roots are exposed; parameters must be inferred by processing those proposition goals. -/
structure AppliedEvalSemanticFinalizer where
  prerequisites : List MVarId
  roots : List EvalSemanticRoot
  parameters : List MVarId := []

/-- A selected whole-term semantic rule used by the direct evaluation proof generator. -/
structure EvalSemanticFinalizer where
  op : Expr
  apply : MVarId → SymM (Option AppliedEvalSemanticFinalizer)

elab_rules : tactic
  | `(tactic| eval_discharge $tac) => do
      unless (← getGoals).isEmpty do
        evalTactic tac

macro_rules
| `(tactic| use_apply $[$bound?]? [$lemmas,*] $spec $[discharging $discharge?]?) => do
    let discharge ← match discharge? with
      | some tactic => pure tactic
      | none => `(tactic| skip)
    `(tactic|
      first
      | (apply Zag.EvaluatesInstrs.cons_app (happly := by apply $spec)
         case hfn =>
           first
           | exact Zag.EvaluatesTo.var_local (by rfl)
           | (evaluates $[$bound?]? [$lemmas,*] <;> simp [$lemmas,*])
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         try evaluates_instrs $[$bound?]? [$lemmas,*]
         all_goals auto_eval_refinement_goals [$lemmas,*]
         eval_discharge $discharge)
      | (try simp only [Instr.ofTerm]
         apply Zag.EvaluatesTo.app
         case hfn =>
           first
           | exact Zag.EvaluatesTo.var_local (by rfl)
           | (evaluates $[$bound?]? [$lemmas,*] <;> simp [$lemmas,*])
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case happly => apply $spec
         try evaluates_instrs $[$bound?]? [$lemmas,*]
         all_goals auto_eval_refinement_goals [$lemmas,*]
         eval_discharge $discharge)
      | (refine Zag.EvaluatesFrom.apply_then ?_ (by
           intro scope
           evaluates_from $[$bound?]? [$lemmas,*])
         apply $spec
         all_goals auto_eval_refinement_goals [$lemmas,*]
         eval_discharge $discharge
         try evaluates_instrs $[$bound?]? [$lemmas,*]))
| `(tactic| use_apply? $[$bound?]? [$lemmas,*] $spec) =>
    `(tactic|
      first
      | (apply Zag.EvaluatesInstrs.cons_app (happly := by apply $spec)
         case hfn =>
           first
           | exact Zag.EvaluatesTo.var_local (by rfl)
           | (evaluates $[$bound?]? [$lemmas,*] <;> simp [$lemmas,*])
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (try simp only [Instr.ofTerm]
         apply Zag.EvaluatesTo.app
         case hfn =>
           first
           | exact Zag.EvaluatesTo.var_local (by rfl)
           | (evaluates $[$bound?]? [$lemmas,*] <;> simp [$lemmas,*])
         case hargs => evaluates_to_all $[$bound?]? [$lemmas,*]
         case happly => apply $spec
         try evaluates_instrs $[$bound?]? [$lemmas,*])
      | (refine Zag.EvaluatesFrom.apply_then ?_ (by
           intro scope
           evaluates_from $[$bound?]? [$lemmas,*] discharging
             (try simp only [eval_finish]))
         apply $spec
         try evaluates_instrs $[$bound?]? [$lemmas,*]))
| `(tactic| apply_eval_wp_refinement $[$bound?]? [$lemmas,*] $refinement
      selecting $params naming [$names,*]) =>
    `(tactic|
      apply_refinement
        (PropRefinement.evalThen (($refinement) $params) (by
          intro scope
          evaluates_from $[$bound?]? [$lemmas,*] discharging
            (try simp only [eval_finish])))
        naming [$names,*])
| `(tactic| auto_eval_refinement_goals [$lemmas,*]) =>
    `(tactic|
      (all_goals
         (try set_option linter.unusedSimpArgs false in simp +arith)
       normalize_eval_refinement_goals [$lemmas,*]
       all_goals (try omega)))

private def natValue? (value : Expr) : MetaM (Option Expr) := do
  let value ← withTransparency .all <| whnf value
  unless value.getAppFn.isConstOf ``Val.mk do return none
  let fields := value.getAppArgs
  let payload := fields[fields.size - 1]!
  unless payload.getAppFn.isConstOf `Zag.Ty.ofNat do return none
  let args := payload.getAppArgs
  return some args[args.size - 1]!

/-- Replace equality of canonical natural values with its ordinary `Nat` equality premise. -/
private def normalizeValNatEq? (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``Eq 3 do return none
  let args := target.getAppArgs
  let some lhs ← natValue? args[1]! | return none
  let some rhs ← natValue? args[2]! | return none
  let premise ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs)
  let natInj ← mkConstWithFreshMVarLevels `Zag.Val.nat_inj
  let (params, _, iffType) ← forallMetaTelescopeReducing (← inferType natInj)
  unless ← withTransparency .all <| isDefEq iffType.getAppArgs[1]! (← premise.mvarId!.getType) do
    return none
  let iff := mkAppN natInj params
  let proof ← mkAppM ``Iff.mpr #[iff, premise]
  unless ← withTransparency .all <| isDefEq (← inferType proof) target do return none
  goal.assign proof
  premise.mvarId!.setTag (← goal.getTag)
  return some premise.mvarId!

/-- Apply the shared representation cleanup to one isolated goal. -/
private def normalizeEvalGoal (goal : MVarId)
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM (List MVarId) := do
  setGoals [goal]
  evalTactic (← `(tactic|
    try simp -implicitDefEqProofs only [List.nil_append, List.set_cons_zero, List.set_cons_succ,
      List.cons.injEq, and_true, List.head?_cons, Option.some.injEq]))
  let mut normalized := []
  for goal in ← getGoals do
    if let some goal ← normalizeValNatEq? goal then
      if lemmas.isEmpty || (← goal.getTag) == `step.preservation then
        normalized := normalized ++ [goal]
      else
        setGoals [goal]
        evalTactic (← `(tactic| try simp -implicitDefEqProofs only [$lemmas,*]))
        normalized := normalized ++ (← getGoals)
    else
      setGoals [goal]
      -- Caller lemmas may be the intended proof of a named preservation equation.
      let preserveEq ← if (← goal.getTag) == `step.preservation then
          goal.withContext do
            return (← instantiateMVars (← goal.getType)).getAppFn.isConstOf ``Eq
        else
          pure false
      if lemmas.isEmpty || preserveEq then
        evalTactic (← `(tactic|
          try simp -implicitDefEqProofs only [Nat.sub_self, Nat.not_lt_zero, not_false_eq_true,
            decide_eq_true_eq, decide_eq_false_iff_not, eval_finish]))
      else
        evalTactic (← `(tactic|
          try simp -implicitDefEqProofs only [Nat.sub_self, Nat.not_lt_zero, not_false_eq_true,
            decide_eq_true_eq, decide_eq_false_iff_not, $lemmas,*, eval_finish]))
      normalized := normalized ++ (← getGoals)
  setGoals normalized
  return ← getGoals

private structure EvalWPRules where
  eqRefl : Sym.BackwardRule
  andIntro : Sym.BackwardRule
  callInstrs : Sym.BackwardRule
  instrsNil : Sym.BackwardRule
  instrsCons : Sym.BackwardRule
  evalsNil : Sym.BackwardRule
  evalsCons : Sym.BackwardRule
  varBlock : Sym.BackwardRule
  app : Sym.BackwardRule
  call : Sym.BackwardRule
  semantic : Array Sym.BackwardRule

private def mkEvalWPRules : MetaM EvalWPRules := do
  return {
    eqRefl := ← Sym.mkBackwardRuleFromDecl ``Eq.refl
    andIntro := ← Sym.mkBackwardRuleFromDecl ``And.intro
    callInstrs := ← Sym.mkBackwardRuleFromDecl ``EvaluatesCall.of_evaluatesInstrs
    instrsNil := ← Sym.mkBackwardRuleFromDecl ``EvaluatesInstrs.nil
    instrsCons := ← Sym.mkBackwardRuleFromDecl ``EvaluatesInstrs.cons
    evalsNil := ← Sym.mkBackwardRuleFromDecl ``EvaluatesToAll.nil
    evalsCons := ← Sym.mkBackwardRuleFromDecl ``EvaluatesToAll.cons
    varBlock := ← Sym.mkBackwardRuleFromDecl ``EvaluatesTo.var_block
    app := ← Sym.mkBackwardRuleFromDecl ``EvaluatesTo.app
    call := ← Sym.mkBackwardRuleFromDecl ``EvaluatesTo.call
    semantic := ← mkEvalSemanticRules
  }

private def isEvaluationHead (head : Expr) : Bool :=
  head.isConstOf ``EvaluatesCall || head.isConstOf ``EvaluatesInstrs ||
    head.isConstOf ``EvaluatesToAll || head.isConstOf ``EvaluatesTo ||
    head.isConstOf ``EvaluatesFrom || head.isConstOf ``EvaluatesApply

private partial def forallResultHead : Expr → Expr
| .forallE _ _ body _ => forallResultHead body
| .mdata _ body => forallResultHead body
| type => type.getAppFn

private def selectedEvalFinalizer? (target : Expr) (finalizer? : Option EvalSemanticFinalizer) :
    MetaM (Option EvalSemanticFinalizer) := withoutModifyingState do
  let some finalizer := finalizer? | return none
  unless target.getAppFn.isConstOf ``EvaluatesTo do return none
  let args := target.getAppArgs
  unless args.size >= 4 do return none
  let term ← withTransparency .all <| whnf args[args.size - 2]!
  unless term.getAppFn.isConstOf ``Term.op do return none
  let termArgs := term.getAppArgs
  unless termArgs.size >= 2 do return none
  let op := termArgs[termArgs.size - 2]!
  if ← withTransparency .reducible <| isDefEq op finalizer.op then
    return some finalizer
  return none

/-- Compile local call/application specifications in the current branch as backward rules. -/
private def mkLocalEvalRules (goal : MVarId) (targetHead : Expr) : SymM (Array Sym.BackwardRule) :=
    goal.withContext do
  let mut rules := #[]
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    let type ← instantiateMVarsS localDecl.type
    if forallResultHead type == targetHead then
      try
        rules := rules.push (← Sym.mkBackwardRuleFromExpr (mkFVar localDecl.fvarId))
      catch _ => pure ()
  return rules

private inductive EvalVCResult where
  | success (goals : List MVarId)
  | blocked (goal : MVarId)

private def substIntroduced (goal : MVarId) (introduced : Array FVarId) : SymM MVarId := do
  let mut goal := goal
  for fvarId in introduced do
    let decl ← goal.getDecl
    unless decl.lctx.contains fvarId do continue
    let saved ← getMCtx
    try
      goal ← Meta.subst goal fvarId
    catch _ =>
      setMCtx saved
  return goal

/-- Expose structural constructors after a call rule infers its block parameter. -/
private def exposeEvalStructure (goal : MVarId) : SymM MVarId := goal.withContext do
  let target ← instantiateMVarsS (← goal.getType)
  let args := target.getAppArgs
  let index? :=
    if target.getAppFn.isConstOf ``EvaluatesInstrs && args.size >= 5 then
      some (args.size - 4)
    else if target.getAppFn.isConstOf ``EvaluatesTo && args.size >= 4 then
      some (args.size - 2)
    else
      none
  let some index := index? | return goal
  let exposed ← withTransparency .all <| whnf args[index]!
  if isSameExpr exposed args[index]! then return goal
  goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! index exposed))

/-- Use Lean's output unification when probing for a canonical evaluation result. -/
private def applyCanonicalRule? (goal : MVarId) (rule : Sym.BackwardRule) :
    SymM (Option (List MVarId)) := goal.withContext do
  try
    let expr ← match rule.expr with
      | .const name _ => mkConstWithFreshMVarLevels name
      | expr => pure expr
    return some (← goal.apply expr { newGoals := .all })
  catch _ =>
    return none

/-- Apply definitional reflexivity with enough transparency to infer dependent rule parameters. -/
private def applyEqRefl? (goal : MVarId) (target : Expr) : SymM Bool := goal.withContext do
  withAssignableSyntheticOpaque do
    unless target.isAppOfArity ``Eq 3 do return false
    let args := target.getAppArgs
    let lhs ← withTransparency .all <| whnf args[1]!
    let rhs ← withTransparency .all <| whnf args[2]!
    unless ← withTransparency .all <| isDefEq lhs rhs do return false
    let lhs ← instantiateMVarsS lhs
    goal.assign (← Sym.mkEqRefl lhs)
    return true

mutual
  /-- Apply cached backward rules in one `SymM` session, returning only ordinary verification
    conditions. No simplifier, arithmetic tactic, or evaluator tactic runs in this pass. -/
  private partial def processEvalVCGoal (goal : MVarId) (rules : EvalWPRules)
      (finalizer? : Option EvalSemanticFinalizer := none)
      (fuel : Nat := 100) (assignEqMVars := true) (useLocalRules := true) :
      SymM EvalVCResult := do
    if fuel = 0 then return .blocked goal
    if ← goal.isAssigned then return .success []
    let rawTarget ← goal.withContext do instantiateMVarsS (← goal.getType)
    let goal ← if rawTarget.isMData then goal.replaceTargetDefEq rawTarget.consumeMData else pure goal
    let rawTarget := rawTarget.consumeMData
    let rawHead := rawTarget.getAppFn
    if !assignEqMVars && rawHead.isConstOf ``Eq then
      return .success [goal]
    let rawLocalRules ← if useLocalRules && isEvaluationHead rawHead then
        mkLocalEvalRules goal rawHead
      else
        pure #[]
    if !rawLocalRules.isEmpty then
      if let some generated ←
          tryEvalVCRules goal rules rawLocalRules finalizer? (fuel - 1) (canonicalProbe := true) then
        return .success generated
    let tag ← goal.getTag
    let goal ← exposeEvalStructure (← preprocessMVar goal)
    goal.setTag tag
    let target ← goal.withContext do instantiateMVarsS (← goal.getType)
    if target.isForall then
      match ← Sym.intros goal with
      | .failed => return .blocked goal
      | .goal introduced next =>
          let next ← substIntroduced next introduced
          next.setTag tag
          processEvalVCGoal next rules finalizer? (fuel - 1) assignEqMVars
    else
      let head := target.getAppFn
      if head.isConstOf ``Eq then
        if assignEqMVars && (← applyEqRefl? goal target) then
          return .success []
      if let some finalizer ← selectedEvalFinalizer? target finalizer? then
        return ← processEvalFinalizer goal rules finalizer finalizer? (fuel - 1)
      let localRules := if head == rawHead then rawLocalRules else #[]
      let candidates :=
        if head.isConstOf ``Eq then
          if assignEqMVars then #[rules.eqRefl] else #[]
        else if head.isConstOf ``And then
          #[rules.andIntro]
        else if head.isConstOf ``EvaluatesCall then
          localRules ++ #[rules.callInstrs]
        else if head.isConstOf ``EvaluatesInstrs then
          #[rules.instrsNil, rules.instrsCons]
        else if head.isConstOf ``EvaluatesToAll then
          #[rules.evalsNil, rules.evalsCons]
        else if head.isConstOf ``EvaluatesTo then
          localRules ++ rules.semantic ++ #[rules.varBlock, rules.app, rules.call]
        else if head.isConstOf ``EvaluatesFrom || head.isConstOf ``EvaluatesApply then
          localRules
        else
          #[]
      if let some generated ← tryEvalVCRules goal rules candidates finalizer? (fuel - 1) then
        return .success generated
      if head.isConstOf ``EvaluatesTo then
        if let some generated ← tryEvalResultTransport goal rules finalizer? (fuel - 1) then
          return .success generated
      if isEvaluationHead head then return .blocked goal
      return .success [goal]

  private partial def tryEvalVCRules (goal : MVarId) (rules : EvalWPRules)
      (candidates : Array Sym.BackwardRule) (finalizer? : Option EvalSemanticFinalizer)
      (fuel : Nat) (canonicalProbe := false) :
      SymM (Option (List MVarId)) := do
    let parentTag ← goal.getTag
    for rule in candidates do
      let mctxSaved ← getMCtx
      let symSaved ← get
      let instrsRule := rule.expr.isConstOf ``EvaluatesInstrs.nil ||
        rule.expr.isConstOf ``EvaluatesInstrs.cons
      let listRule := rule.expr.isConstOf ``EvaluatesToAll.nil ||
        rule.expr.isConstOf ``EvaluatesToAll.cons
      let callRule := rule.expr.isConstOf ``EvaluatesCall.of_evaluatesInstrs
      let semanticRule := rules.semantic.any fun candidate => isSameExpr candidate.expr rule.expr
      let applied ← if canonicalProbe || callRule || instrsRule || listRule then
          applyCanonicalRule? goal rule
        else
          applyEvalBackwardRule? goal rule
      match applied with
      | none =>
          setMCtx mctxSaved
          set symSaved
      | some subgoals =>
          let mut residual := []
          let mut parameters := []
          let mut deferred := []
          let mut blocked := false
          for subgoal in subgoals do
            if residual.contains subgoal then continue
            if ← subgoal.isAssigned then continue
            subgoal.setTag parentTag
            let type ← subgoal.withContext do instantiateMVarsS (← subgoal.getType)
            if ← isProp type then
              let head := type.getAppFn
              let resultHead := forallResultHead type
              if head.isConstOf ``EvaluatesFrom || head.isConstOf ``EvaluatesApply ||
                  resultHead.isConstOf ``EvaluatesFrom || resultHead.isConstOf ``EvaluatesApply then
                deferred := subgoal :: deferred
              else
                match ← processEvalVCGoal subgoal rules finalizer? fuel
                    (assignEqMVars := !(canonicalProbe && rule.expr.isFVar)) with
                | .success generated =>
                    if semanticRule && !generated.isEmpty then
                      blocked := true
                      break
                    residual := residual ++ generated
                | .blocked _ =>
                    blocked := true
                    break
            else
              parameters := subgoal :: parameters
          unless blocked do
            for subgoal in deferred.reverse do
              match ← processEvalVCGoal subgoal rules finalizer? fuel with
              | .success generated => residual := residual ++ generated
              | .blocked _ =>
                  blocked := true
                  break
          unless blocked do
            for parameter in parameters do
              unless ← parameter.isAssigned do blocked := true
          unless blocked do return some residual
          setMCtx mctxSaved
          set symSaved
    return none

  private partial def tryEvalResultTransport (goal : MVarId) (rules : EvalWPRules)
      (finalizer? : Option EvalSemanticFinalizer) (fuel : Nat) :
      SymM (Option (List MVarId)) := do
    let mctxSaved ← getMCtx
    let symSaved ← get
    let target ← goal.withContext do instantiateMVarsS (← goal.getType)
    let args := target.getAppArgs
    unless target.getAppFn.isConstOf ``EvaluatesTo && args.size >= 4 do
      return none
    let fields := args.extract (args.size - 4) args.size
    let hcanonical ← goal.withContext do
      let primCtx ← mkAppM ``Ctx.primCtx #[fields[0]!]
      let valueType ← mkAppM ``Val #[primCtx]
      let canonical ← mkFreshExprMVar valueType
      let hcanonicalType ← mkAppM ``EvaluatesTo #[fields[0]!, fields[1]!, fields[2]!, canonical]
      let hcanonical ← mkFreshExprSyntheticOpaqueMVar hcanonicalType
      let equalityType ← mkEq canonical fields[3]!
      let equality ← mkFreshExprSyntheticOpaqueMVar equalityType
      goal.assign (← mkAppM ``EvaluatesTo.of_eq #[hcanonical, equality])
      pure (hcanonical.mvarId!, equality.mvarId!)
    let tag ← goal.getTag
    hcanonical.1.setTag tag
    hcanonical.2.setTag tag
    let evalTarget ← hcanonical.1.withContext do instantiateMVarsS (← hcanonical.1.getType)
    let localRules ← mkLocalEvalRules hcanonical.1 evalTarget.getAppFn
    let candidates := localRules ++ rules.semantic ++ #[rules.varBlock, rules.app, rules.call]
    let some residual ← withAssignableSyntheticOpaque do
        withTransparency .all <|
          tryEvalVCRules hcanonical.1 rules candidates finalizer? fuel (canonicalProbe := true)
      | setMCtx mctxSaved; set symSaved; return none
    match ← processEvalVCGoal hcanonical.2 rules finalizer? fuel with
    | .success generated => return some (residual ++ generated)
    | .blocked _ => pure ()
    setMCtx mctxSaved
    set symSaved
    return none

  private partial def processEvalFinalizer (goal : MVarId) (rules : EvalWPRules)
      (finalizer : EvalSemanticFinalizer) (finalizer? : Option EvalSemanticFinalizer)
      (fuel : Nat) : SymM EvalVCResult := do
    let mctxSaved ← getMCtx
    let symSaved ← get
    let some applied ← finalizer.apply goal
      | setMCtx mctxSaved; set symSaved; return .blocked goal
    for prerequisite in applied.prerequisites do
      if ← prerequisite.isAssigned then continue
      match ← processEvalVCGoal prerequisite rules finalizer? fuel with
      | .success [] => pure ()
      | _ =>
          setMCtx mctxSaved
          set symSaved
          return .blocked goal
    let mut residual := []
    for root in applied.roots do
      match root with
      | .goal name root =>
          if ← root.isAssigned then continue
          root.setTag name
          match ← processEvalVCGoal root rules finalizer? fuel with
          | .success generated => residual := residual ++ generated
          | .blocked blocked => residual := residual ++ [blocked]
      | .residual name root =>
          unless ← root.isAssigned do
            root.setTag name
            residual := residual ++ [root]
      | .forallAnd leftName rightName root =>
          if ← root.isAssigned then continue
          let split ← match ← Sym.intros root with
            | .failed =>
                setMCtx mctxSaved
                set symSaved
                return .blocked goal
            | .goal introduced next => substIntroduced next introduced
          let target ← split.withContext do instantiateMVarsS (← split.getType)
          unless target.getAppFn.isConstOf ``And do
            setMCtx mctxSaved
            set symSaved
            return .blocked goal
          let some children ← applyEvalBackwardRule? split rules.andIntro
            | setMCtx mctxSaved; set symSaved; return .blocked goal
          let [left, right] := children
            | setMCtx mctxSaved; set symSaved; return .blocked goal
          for (name, child) in [(leftName, left), (rightName, right)] do
            child.setTag name
            match ← processEvalVCGoal child rules finalizer? fuel with
            | .success generated => residual := residual ++ generated
            | .blocked blocked => residual := residual ++ [blocked]
    for parameter in applied.parameters do
      unless ← parameter.isAssigned do
        setMCtx mctxSaved
        set symSaved
        return .blocked goal
    return .success residual
end

/-- Generate evaluation verification conditions for all roots in one symbolic session. -/
def evalWPVCGen (roots : List MVarId) (finalizer? : Option EvalSemanticFinalizer := none)
    (fuel : Nat := 100) : SymM (List MVarId) := do
  let rules ← mkEvalWPRules
  let mut processed : List MVarId := []
  for root in roots do
    let tag ← root.getTag
    let generated := match ← processEvalVCGoal root rules finalizer? fuel
        (useLocalRules := finalizer?.isNone) with
      | .success generated => generated
      | .blocked goal => [goal]
    for goal in generated do
      unless processed.contains goal do
        if (← goal.getTag).isAnonymous then goal.setTag tag
        processed := processed ++ [goal]
  return processed

/-- Preserve the machine evaluator as a fallback for calls without direct semantic rules. -/
private def tryEvalCallFallback (goal : MVarId) (bound? : Option (TSyntax `num))
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option (List MVarId)) := do
  let target ← goal.withContext do instantiateMVars (← goal.getType)
  unless target.getAppFn.isConstOf ``EvaluatesCall do return none
  let saved ← saveState
  setGoals [goal]
  try
    evalTactic (← `(tactic| evaluates_call? $[$bound?]? [$lemmas,*]))
    return some (← getGoals)
  catch _ =>
    restoreState saved
    return none

elab_rules : tactic
| `(tactic| normalize_eval_refinement_goals [$lemmas,*]) => do
    let roots ← getGoals
    let normalized ← roots.mapM fun goal => do
      let goals ← normalizeEvalGoal goal lemmas.getElems
      pure goals
    setGoals normalized.flatten
| `(tactic| process_eval_wp_goals $[$bound?]? [$lemmas,*]) => do
    let roots ← SymM.run <| evalWPVCGen (← getGoals)
    let mut processed := []
    for root in roots do
      let generated ← match ← tryEvalCallFallback root bound? lemmas.getElems with
        | some goals => SymM.run <| evalWPVCGen goals
        | none => pure [root]
      processed := processed ++ generated
    setGoals processed

end Zag
