import Meta.Eval.VC
import Lib.Peano.Eval

/-!
# Peano `while` induction

`zspec whileInduction` builds the MultByAddLoopManual Exact apply spine under the hood.
-/

namespace Zag

open Lean Elab Tactic Meta

syntax (name := zspecWhileInduction) "zspec" &"whileInduction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

syntax (name := zspecWhileInductionQ) "zspec?" &"whileInduction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term " stopping_at " term
  (" returning " term)? : tactic

syntax (name := peanoExactSteps) "peano_exact_steps"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
| `(tactic| zspec whileInduction $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) =>
    -- Exact while spine only; do not run monadic `auto_eval_refinement_goals`.
    `(tactic|
      zspec? whileInduction $[$bound?]? [$lemmas,*] $I stopping_at $N
         $[returning $result?]?)

/-- One Exact apply-spine step (MultByAddLoopManual rules). -/
private def peanoExactStepOnce
    (lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Bool := do
  let tryTac (t : TSyntax `tactic) : TacticM Bool := do
    let s ← saveState
    let root? := (← getGoals).head?
    try
      -- Prevent failed `by ...` subterms from becoming `sorry`.
      Term.withoutErrToSorry do
        evalTactic t
      -- Reject steps that introduced sorry into the proof term.
      if let some r := root? then
        if let some prf ← getExprMVarAssignment? r then
          if (← instantiateMVars prf).hasSorry then
            restoreState s
            return false
      pure true
    catch _ =>
      restoreState s
      pure false
  -- Succeed only if the main goal is assigned/changed (no silent no-ops).
  let tryProgress (t : TSyntax `tactic) : TacticM Bool := do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let s ← saveState
    if ← tryTac t then
      if ← g.isAssigned then return true
      let ty' ← instantiateMVars (← g.getType)
      if ty == ty' then
        restoreState s
        pure false
      else
        pure true
    else
      pure false
  if (← getGoals).isEmpty then return true
  -- Prefer MetaM substVars before any judgment rules.
  let g0 ← getMainGoal
  let g0' ← g0.withContext do substVars g0
  if g0' != g0 then
    setGoals [g0']
    return true
  if ← tryTac (← `(tactic| rfl)) then return true
  if ← tryTac (← `(tactic| assumption)) then return true
  let tgt ← getMainTarget
  let head := tgt.getAppFn
  let isCallValues :=
    head.isConstOf ``EvalTriple.Exact.EvaluatesCallValues ||
    head.isConstOf ``Zag.EvalTriple.Exact.EvaluatesCallValues
  let isInstrs :=
    head.isConstOf ``EvalTriple.Exact.EvaluatesInstrs ||
    head.isConstOf ``Zag.EvalTriple.Exact.EvaluatesInstrs
  let isEvalTo :=
    head.isConstOf ``EvalTriple.Exact.EvaluatesTo ||
    head.isConstOf ``Zag.EvalTriple.Exact.EvaluatesTo ||
    (head.constName?.any fun n => (n.toString).endsWith "EvaluatesTo" &&
      !(n.toString).endsWith "EvaluatesToAll")
  let isEvalList :=
    head.isConstOf ``EvalTriple.Exact.EvaluatesList ||
    head.isConstOf ``Zag.EvalTriple.Exact.EvaluatesList
  let isEvalApply :=
    head.isConstOf ``EvalTriple.Exact.EvaluatesApply ||
    head.isConstOf ``Zag.EvalTriple.Exact.EvaluatesApply
  let isAnd := head.isConstOf ``And
  let isEq := tgt.isAppOfArity ``Eq 3
  let isFalse := head.isConstOf ``False || tgt.isConstOf ``False
  if isFalse then
    -- Never close False with omega/sorry; leave for filtering.
    return false
  -- Exact CallValues spine first (do not simp/subst before this).
  if isCallValues then
    let g ← getMainGoal
    let saved ← saveState
    try
      let c ← mkConstWithFreshMVarLevels ``EvalTriple.Exact.EvaluatesCallValues.of_evaluatesInstrs
      let gs ← g.withContext do g.apply c
      setGoals gs
      -- Close block/arity equalities immediately.
      let mut kept : List MVarId := []
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← g'.withContext do instantiateMVars (← g'.getType)
        if ty.isAppOfArity ``Eq 3 then
          setGoals [g']
          let closed ← tryTac (← `(tactic|
            first
            | rfl
            | simp [$lemmas,*, BlockCtx.get?, List.length, Block.params, Block.entryEnv]))
          if closed && (← getGoals).isEmpty then
            pure ()
          else
            kept := kept ++ (← getGoals)
        else
          kept := kept ++ [g']
      if let some prf ← getExprMVarAssignment? g then
        if (← instantiateMVars prf).hasSorry then
          restoreState saved
          return false
      setGoals kept
      return true
    catch _ =>
      restoreState saved
      return false
  if isInstrs then
    if ← tryTac (← `(tactic| apply EvalTriple.Exact.EvaluatesInstrs.nil)) then return true
    if ← tryTac (← `(tactic|
        refine EvalTriple.Exact.EvaluatesInstrs.cons (instrValue := ?_) ?_ ?_)) then
      return true
    return false
  if isEvalList then
    if ← tryTac (← `(tactic| apply EvalTriple.Exact.EvaluatesList.nil)) then return true
    -- Unfold zip/append env so var_local sees concrete bindings.
    if ← tryProgress (← `(tactic|
        simp only [List.zipWith, List.map, List.append, List.cons_append, List.nil_append,
          Prod.mk, Instr.ofTerm, Instr.name, $lemmas,*])) then
      return true
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesList.cons
          (EvalTriple.Exact.EvaluatesTo.var_local (by first | rfl | simp [Scope.get?]))
          (EvalTriple.Exact.EvaluatesList.cons
            (EvalTriple.Exact.EvaluatesTo.var_local (by first | rfl | simp [Scope.get?]))
            (EvalTriple.Exact.EvaluatesList.cons
              (EvalTriple.Exact.EvaluatesTo.var_local (by first | rfl | simp [Scope.get?]))
              EvalTriple.Exact.EvaluatesList.nil)))) then
      return true
    if ← tryTac (← `(tactic|
        refine EvalTriple.Exact.EvaluatesList.cons
          (EvalTriple.Exact.EvaluatesTo.var_local (by first | rfl | simp [Scope.get?])) ?_)) then
      return true
    if ← tryTac (← `(tactic| refine EvalTriple.Exact.EvaluatesList.cons ?_ ?_)) then return true
    return false
  if isEvalApply then
    -- Normalize `Prod.snd (_, v)` wrappers from var_local lookup.
    if ← tryProgress (← `(tactic| simp only [Prod.snd])) then return true
    -- Loop IH: `∀ nextArgs, nextArgs = L → EvaluatesApply ... nextArgs ...`
    -- Proof: `exact h <concreteArgs> (by simp ...)` via MetaM (anonymous fvars).
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let goalArgs := tgt.getAppArgs
    -- Exact.EvaluatesApply ctx fn args expected [hM]
    if goalArgs.size < 4 then return false
    let concreteArgs := goalArgs[2]!
    let lctx ← g.withContext getLCtx
    for localDecl in lctx do
      if localDecl.isImplementationDetail then continue
      let eTy ← g.withContext do instantiateMVars localDecl.type
      unless eTy.isForall do continue
      let s ← saveState
      try
        let (prfE, eqG) ← g.withContext do
          let h := mkFVar localDecl.fvarId
          let h1 := mkApp h concreteArgs
          let h1Ty ← whnf (← inferType h1)
          unless h1Ty.isForall do throwError "ih1 not forall"
          let eqTy := h1Ty.bindingDomain!
          let eqM ← mkFreshExprMVar eqTy
          let prfE := mkApp h1 eqM
          let prfTy ← inferType prfE
          unless ← isDefEq prfTy tgt do
            throwError "ih type mismatch"
          pure (prfE, eqM.mvarId!)
        g.assign prfE
        setGoals [eqG]
        Term.withoutErrToSorry do
          evalTactic (← `(tactic|
            first
            | rfl
            | simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm,
                Nat.sub_sub, Prod.snd, $lemmas,*]))
        if let some prf ← getExprMVarAssignment? g then
          if (← instantiateMVars prf).hasSorry then
            restoreState s
            return false
        if (← getGoals).isEmpty then return true
        if ← g.isAssigned then return true
        restoreState s
      catch _ =>
        restoreState s
    return false
  if isAnd then
    if ← tryTac (← `(tactic| constructor)) then return true
    return false
  if isEq then
    if ← tryTac (← `(tactic| rfl)) then return true
    if ← tryTac (← `(tactic|
        first
        | rw [decide_eq_true (Nat.sub_pos_of_lt (by assumption))]
        | rw [decide_eq_false (Nat.not_lt_zero _)]
        | rw [decide_eq_false (Nat.not_lt.mpr (Nat.le_refl _))]
        | simp [Val.bool_inj, Val.nat_inj, decide_eq_true_eq, decide_eq_false_iff_not,
            Nat.sub_self, Nat.zero_sub, List.head?, List.map, Val.ty,
            Option.some.injEq]
        | rfl)) then
      return true
    if ← tryProgress (← `(tactic|
        simp [$lemmas,*, Block.entryEnv, Scope.get?, BlockCtx.get?,
          Peano.Exact.whileCondRef, Peano.Exact.whileBodyRef, Peano.Exact.whileRef,
          decide_eq_true_eq, decide_eq_false_iff_not, Nat.succ_mul,
          Nat.add_assoc, Nat.add_comm, Nat.sub_sub, Nat.zero_mul, Nat.add_zero,
          Nat.sub_zero, List.head?, List.map, Val.ty])) then
      return true
    return false
  if isEvalTo then
    -- Unfold `block.result` / `entryEnv` so `.op "gt"` and concrete env are visible.
    if ← tryProgress (← `(tactic|
        simp only [Block.result, Block.entryEnv, Block.params, Block.instrs,
          List.map, List.zip, Prod.fst, Prod.snd, $lemmas,*])) then
      return true
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.var_local (by
          first | rfl | simp [Block.entryEnv, Scope.get?, $lemmas,*]))) then
      return true
    if ← tryTac (← `(tactic| exact EvalTriple.Exact.evaluates_nat _ _)) then return true
    -- MultByAddLoopManual cond: of_eq (evaluates_gt_nat var_local nat) (congrArg bool decide_eq).
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.evaluates_gt_nat
            (EvalTriple.Exact.EvaluatesTo.var_local (by rfl))
            (EvalTriple.Exact.evaluates_nat _ 0))
          (congrArg Val.bool
            (decide_eq_true (Nat.sub_pos_of_lt (by assumption)))))) then
      return true
    -- Exit cond: `gt remaining 0` is false when remaining reduces to 0.
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.evaluates_gt_nat
            (EvalTriple.Exact.EvaluatesTo.var_local (by rfl))
            (EvalTriple.Exact.evaluates_nat _ 0))
          (by simp [Nat.sub_self, Nat.zero_sub, decide_eq_false_iff_not, Nat.not_lt_zero]))) then
      return true
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.evaluates_add_nat
            (EvalTriple.Exact.EvaluatesTo.var_local (by rfl))
            (EvalTriple.Exact.EvaluatesTo.var_local (by rfl)))
          (by first | rfl | simp [Nat.add_comm, Nat.add_assoc, $lemmas,*]))) then
      return true
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.evaluates_sub_nat
            (EvalTriple.Exact.EvaluatesTo.var_local (by rfl))
            (EvalTriple.Exact.evaluates_nat _ 1))
          (by first | rfl | simp [Nat.sub_sub, $lemmas,*]))) then
      return true
    if ← tryTac (← `(tactic|
        exact EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.EvaluatesTo.var_block
            (by first | rfl | simp [Block.entryEnv, Scope.get?, $lemmas,*])
            (by first | rfl | simp [$lemmas,*]))
          (by first
              | rfl
              | simp [Peano.Exact.whileCondRef, Peano.Exact.whileBodyRef,
                  Peano.Exact.whileRef, Block.params, Block.outTy, List.map,
                  Prod.snd, Peano.NatTy, Peano.BoolTy, $lemmas,*]))) then
      return true
    if ← tryTac (← `(tactic| apply EvalTriple.Exact.EvaluatesTo.app)) then return true
    if ← tryTac (← `(tactic| apply EvalTriple.Exact.EvaluatesTo.call)) then return true
    if ← tryProgress (← `(tactic|
        simp [$lemmas,*, Block.entryEnv, Scope.get?, BlockCtx.get?])) then
      return true
    return false
  -- Outer arithmetic binders only (`∀ n, n < N → _`).
  if tgt.isForall then
    let dom := tgt.bindingDomain!
    let dHead := dom.getAppFn
    let isEvalDom :=
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesTo ||
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesFrom ||
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesCallValues ||
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesApply ||
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesList ||
      dHead.isConstOf ``EvalTriple.Exact.EvaluatesInstrs
    if !isEvalDom then
      if ← tryTac (← `(tactic| intro)) then return true
  if ← tryProgress (← `(tactic|
      simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.sub_sub, Nat.add_left_comm,
        $lemmas,*])) then
    return true
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    unless localDecl.userName.isAnonymous do
      if ← tryTac (← `(tactic| exact $(mkIdent localDecl.userName))) then return true
      if ← tryTac (← `(tactic| apply $(mkIdent localDecl.userName))) then return true
  return false

elab_rules : tactic
| `(tactic| peano_exact_steps [$lemmas,*]) => do
    let lemmas := lemmas.getElems
    let mut fuel := 128
    while fuel > 0 do
      fuel := fuel - 1
      let gs ← getGoals
      if gs.isEmpty then return
      let mut any := false
      let mut next : List MVarId := []
      for g in gs do
        if ← g.isAssigned then continue
        let gty ← g.withContext do instantiateMVars (← g.getType)
        -- Skip non-Prop goals (e.g. bare `Val` mvars for `canonical`); assigned by later steps.
        if !(← g.withContext do isProp gty) then
          next := next ++ [g]
        else
          setGoals [g]
          if ← peanoExactStepOnce lemmas then
            any := true
            for g' in ← getGoals do
              if ← g'.isAssigned then continue
              let t ← g'.withContext do instantiateMVars (← g'.getType)
              if !(← g'.withContext do isProp t) then
                next := next ++ [g']
              else if t.isAppOfArity ``Eq 3 then
                setGoals [g']
                try evalTactic (← `(tactic| first | rfl | simp [$lemmas,*,
                  Peano.Exact.whileCondRef, Peano.Exact.whileBodyRef, Peano.Exact.whileRef,
                  Block.params, Block.outTy, List.map, Prod.snd])) catch _ => pure ()
                next := next ++ (← getGoals)
              else
                next := next ++ [g']
          else
            next := next ++ [g]
      setGoals next
      unless any do return
    pure ()

elab_rules : tactic
| `(tactic| zspec? whileInduction $[$bound?]? [$lemmas,*] $I stopping_at $N
      $[returning $result?]?) => do
    let goals ← getGoals
    let some root := goals.head? | return
    let target ← root.withContext do instantiateMVars (← root.getType)
    let head := target.getAppFn
    let isExactCV := head.isConstOf ``EvalTriple.Exact.EvaluatesCallValues
    let isMonCV :=
      head.isConstOf ``EvalTriple.EvaluatesCallValues ||
      head.isConstOf ``Zag.EvaluatesCallValues
    unless isExactCV || isMonCV do
      throwError "zspec whileInduction expected EvaluatesCallValues (monadic or Exact)"
    -- Monadic goals use P/Q; reduce to Exact sugar (Id + equality post) when possible.
    if isMonCV then
      try evalTactic (← `(tactic|
        change EvalTriple.Exact.EvaluatesCallValues _ _ _ _ (hM := by first | assumption | rfl)))
      catch _ => pure ()
    let target ← root.withContext do instantiateMVars (← root.getType)
    let targs := target.getAppArgs
    unless targs.size >= 5 do throwError "malformed goal"
    let expected :=
      if target.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesCallValues then
        targs[targs.size - 2]!
      else
        targs[targs.size - 2]!
    let loopResultStx ← match result? with
      | some r => pure r
      | none => do
          let e ← root.withContext do PrettyPrinter.delab expected
          `(term| $e:term)
    let lemmasA := lemmas.getElems
    setGoals [root]
    -- Spine: of_evaluatesInstrs
    evalTactic (← `(tactic| apply EvalTriple.Exact.EvaluatesCallValues.of_evaluatesInstrs))
    -- close hblock, harity
    evalTactic (← `(tactic| all_goals (try first | rfl | simp [$lemmas,*])))
    -- body: EvaluatesInstrs.cons with while result
    evalTactic (← `(tactic|
      refine EvalTriple.Exact.EvaluatesInstrs.cons (instrValue := $loopResultStx) ?_ ?_))
    let gs ← getGoals
    let (whileG, tailG, rest) ← match gs with
      | a :: b :: r => pure (a, b, r)
      | _ => throwError "expected two goals after EvaluatesInstrs.cons"
    -- tail: nil + var_local on result
    setGoals [tailG]
    Term.withoutErrToSorry do
      evalTactic (← `(tactic|
        first
        | exact EvalTriple.Exact.EvaluatesInstrs.nil
            (EvalTriple.Exact.EvaluatesTo.var_local
              (by first | rfl | simp [Block.entryEnv, Scope.get?, $lemmas,*]))
        | apply EvalTriple.Exact.EvaluatesInstrs.nil <;> peano_exact_steps [$lemmas,*]))
    -- while instruction: recover cond/body/stateTys from the while term in the goal
    setGoals [whileG]
    let wTarget ← whileG.withContext do instantiateMVars (← whileG.getType)
    let wArgs := wTarget.getAppArgs
    let termE ← whileG.withContext do withTransparency .all <| whnf wArgs[wArgs.size - 3]!
    let targs := termE.getAppArgs
    let opsE := targs.back!
    -- ops = [var cond, var body, ...state]
    let ops ← whileG.withContext do
      let mut cur ← withTransparency .all <| whnf opsE
      let mut acc : Array Expr := #[]
      for _ in [:8] do
        if cur.isAppOfArity ``List.cons 3 then
          acc := acc.push (cur.getArg! 1)
          cur ← withTransparency .all <| whnf (cur.getArg! 2)
        else break
      pure acc
    unless ops.size ≥ 2 do throwError "while operands missing"
    let condT ← whileG.withContext do withTransparency .all <| whnf ops[0]!
    let bodyT ← whileG.withContext do withTransparency .all <| whnf ops[1]!
    unless condT.getAppFn.isConstOf ``Term.var && bodyT.getAppFn.isConstOf ``Term.var do
      throwError "while cond/body must be variables"
    let condNameE := condT.getAppArgs.back!
    let bodyNameE := bodyT.getAppArgs.back!
    let condNameStx ← whileG.withContext do PrettyPrinter.delab condNameE
    let bodyNameStx ← whileG.withContext do PrettyPrinter.delab bodyNameE
    -- stateTys / resultTy from block lookup
    let ctxE := wArgs[wArgs.size - 5]!
    let blockCtx ← whileG.withContext do mkAppM ``Ctx.blockCtx #[ctxE]
    let condBlk ← whileG.withContext do
      let l ← withTransparency .all <| whnf (← mkAppM ``BlockCtx.get? #[blockCtx, condNameE])
      pure l.getAppArgs.back!
    let bodyBlk ← whileG.withContext do
      let l ← withTransparency .all <| whnf (← mkAppM ``BlockCtx.get? #[blockCtx, bodyNameE])
      pure l.getAppArgs.back!
    let stateTys ← whileG.withContext do
      let params ← withTransparency .all <| whnf (← mkAppM ``Block.params #[condBlk])
      let mut cur := params
      let mut tys : Array Expr := #[]
      for _ in [:8] do
        if cur.isAppOfArity ``List.cons 3 then
          let p ← withTransparency .all <| whnf (cur.getArg! 1)
          let ty ←
            if p.isAppOf ``Prod.mk then pure p.getAppArgs.back!
            else mkAppM ``Prod.snd #[p]
          tys := tys.push ty
          cur ← withTransparency .all <| whnf (cur.getArg! 2)
        else break
      mkListLit (mkConst ``Ty) tys.toList
    let resultTy ← whileG.withContext do
      withTransparency .all <| whnf (← mkAppM ``Block.outTy #[bodyBlk])
    let stateTysStx ← whileG.withContext do PrettyPrinter.delab stateTys
    let resultTyStx ← whileG.withContext do PrettyPrinter.delab resultTy
    -- initial state values = while operands after cond/body, evaluated as locals
    evalTactic (← `(tactic|
      apply Peano.Exact.while_evaluatesTo
        (I := $I) (N := $N) (loopResult := $loopResultStx)
        (opName := "while")
        (condName := $condNameStx)
        (bodyName := $bodyNameStx)
        (stateTys := $stateTysStx)
        (resultTy := $resultTyStx)))
    -- Discharge hop / headTy / init / typed first.
    Term.withoutErrToSorry do
      evalTactic (← `(tactic|
        all_goals (try first
          | rfl
          | simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, List.map, Prod.snd,
              Block.params, Block.outTy, Peano.NatTy, $lemmas,*]
          | skip)))
    -- Build EvaluatesList for while operands (cond ref, body ref, state vars).
    let mut remaining ← getGoals
    let mut kept : List MVarId := []
    for g in remaining do
      if ← g.isAssigned then continue
      let ty ← g.withContext do instantiateMVars (← g.getType)
      if ty.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesList then
        setGoals [g]
        -- Unfold list by cons until empty.
        let mut guard := 8
        while guard > 0 do
          guard := guard - 1
          let gt ← getMainGoal
          let gty ← gt.withContext do instantiateMVars (← gt.getType)
          let gargs := gty.getAppArgs
          -- EvaluatesList ctx env terms values hM — terms near the end
          if gargs.size >= 5 then
            let terms ← gt.withContext do withTransparency .all <| whnf gargs[gargs.size - 3]!
            if terms.isAppOfArity ``List.nil 1 then
              evalTactic (← `(tactic| apply EvalTriple.Exact.EvaluatesList.nil))
              break
            if terms.isAppOfArity ``List.cons 3 then
              evalTactic (← `(tactic| refine EvalTriple.Exact.EvaluatesList.cons ?_ ?_))
              -- head EvaluatesTo
              let hs ← getGoals
              match hs with
              | h :: t :: r =>
                  setGoals [h]
                  let ht ← h.withContext do instantiateMVars (← h.getType)
                  let ha := ht.getAppArgs
                  if ha.size >= 5 then
                    let termE ← h.withContext do withTransparency .all <| whnf ha[ha.size - 3]!
                    if termE.getAppFn.isConstOf ``Term.var then
                      let nm := termE.getAppArgs.back!
                      let tryExact (t : TSyntax `tactic) : TacticM Bool := do
                        let s ← saveState
                        try
                          Term.withoutErrToSorry do evalTactic t
                          if let some prf ← getExprMVarAssignment? h then
                            if (← instantiateMVars prf).hasSorry then
                              restoreState s
                              return false
                          pure true
                        catch _ =>
                          restoreState s
                          pure false
                      unless ← tryExact (← `(tactic|
                          exact EvalTriple.Exact.EvaluatesTo.var_local
                            (by first | rfl | simp [Block.entryEnv, Scope.get?, $lemmas,*]))) do
                        let nmStx ← h.withContext do PrettyPrinter.delab nm
                        let _ ← tryExact (← `(tactic|
                            exact EvalTriple.Exact.EvaluatesTo.of_eq
                              (EvalTriple.Exact.EvaluatesTo.var_block (name := $nmStx)
                                (by first | rfl | simp [Block.entryEnv, Scope.get?, $lemmas,*])
                                (by first | rfl | simp [$lemmas,*]))
                              (by first
                                  | rfl
                                  | simp [Peano.Exact.whileCondRef, Peano.Exact.whileBodyRef,
                                      Peano.Exact.whileRef, Block.params, Block.outTy, List.map,
                                      Prod.snd, Peano.NatTy, Peano.BoolTy, $lemmas,*])))
                    else
                      evalTactic (← `(tactic| peano_exact_steps [$lemmas,*]))
                  else
                    evalTactic (← `(tactic| peano_exact_steps [$lemmas,*]))
                  setGoals ((← getGoals) ++ t :: r)
              | _ => break
            else break
          else break
        kept := kept ++ (← getGoals)
      else
        kept := kept ++ [g]
    setGoals kept
    -- preserved / exits / remaining
    -- Tag and discharge preserved / exits (and any other residuals).
    let mut finals ← getGoals
    for g in finals do
      if ← g.isAssigned then continue
      let ty ← g.withContext do instantiateMVars (← g.getType)
      if ty.isForall then g.setTag `step.preservation
      else if ty.getAppFn.isConstOf ``EvalTriple.Exact.EvaluatesCallValues then
        g.setTag `termination
      else if ty.isConstOf ``False then
        -- Drop bogus False goals from failed of_eq attempts by leaving them last.
        pure ()
    setGoals finals
    -- Unpack `∀ n, n < N → P ∧ Q` and `P ∧ Q` without touching eval judgments.
    let mut unpackFuel := 8
    while unpackFuel > 0 do
      unpackFuel := unpackFuel - 1
      let gs ← getGoals
      let mut next : List MVarId := []
      let mut any := false
      for g in gs do
        if ← g.isAssigned then continue
        let ty ← g.withContext do instantiateMVars (← g.getType)
        if ty.isConstOf ``False then continue
        if ty.getAppFn.isConstOf ``And then
          setGoals [g]
          evalTactic (← `(tactic| constructor))
          any := true
          next := next ++ (← getGoals)
        else if ty.isForall then
          let dom := ty.bindingDomain!
          let head := dom.getAppFn
          let isEvalDom :=
            head.isConstOf ``EvalTriple.Exact.EvaluatesTo ||
            head.isConstOf ``EvalTriple.Exact.EvaluatesFrom ||
            head.isConstOf ``EvalTriple.Exact.EvaluatesCallValues ||
            head.isConstOf ``EvalTriple.Exact.EvaluatesApply ||
            head.isConstOf ``EvalTriple.Exact.EvaluatesList ||
            head.isConstOf ``EvalTriple.Exact.EvaluatesInstrs
          if !isEvalDom then
            setGoals [g]
            let (_, g') ← g.introNP 1
            any := true
            next := next ++ [g']
          else
            next := next ++ [g]
        else
          next := next ++ [g]
      setGoals next
      unless any do break
    -- Exact apply spine on residuals.
    Term.withoutErrToSorry do
      evalTactic (← `(tactic| all_goals (try peano_exact_steps [$lemmas,*])))
    let isFalseTy (ty : Expr) : Bool :=
      let t := ty.consumeMData
      t.isConstOf ``False || t.isAppOf ``False
    -- Surface nested unassigned mvars from the root proof term.
    let mut nested : Array MVarId := #[]
    if let some prf0 ← getExprMVarAssignment? root then
      nested ← getMVars (← instantiateMVars prf0)
    else
      nested ← getMVars (mkMVar root)
    let mut live : List MVarId := []
    for g in nested.toList ++ (← getGoals) do
      if ← g.isAssigned then continue
      let ty ← g.withContext do instantiateMVars (← g.getType)
      let ty' ← g.withContext do whnf ty
      if isFalseTy ty || isFalseTy ty' then continue
      if ← g.withContext do isProp ty then
        unless live.contains g do live := live ++ [g]
    setGoals live
    -- Proof is complete: drop sticky errors from failed try-branches; reject sorry.
    if live.isEmpty then
      if let some prf0 ← getExprMVarAssignment? root then
        let prf ← instantiateMVars prf0
        if prf.hasSorry then
          throwError "zspec whileInduction: proof contains sorry"
        try
          check prf
          let expected ← root.withContext do instantiateMVars (← root.getType)
          let prfTy ← inferType prf
          if ← isDefEq prfTy expected then
            modifyThe Core.State fun s => { s with messages := {} }
        catch _ => pure ()



end Zag
