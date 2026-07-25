import Lang.Simple.Defs
import Lang.SSA

/-!
  Lifting the Zag-backed Simple local-state fragment to SSA.

  `Lang.Simple.Basic` is a typed Zag state expression under one state variable.
  This pass recognizes the Simple state ABI (`state.get.i`, `state.set.i`, and
  `state.pack.n`) and emits direct local SSA `let_` binders.
-/

namespace Lang.Simple.Lift

abbrev SSAVar := Zag.Lang.SSA.SSAVar
abbrev SSAValue (primCtx : Zag.PrimitiveCtx) := Zag.Lang.SSA.SSAValue primCtx
abbrev SSAExpr (primCtx : Zag.PrimitiveCtx) := Zag.Lang.SSA.SSAExpr primCtx

/-- The local SSA variables in scope while emitting code. -/
structure LocalContext where
  vars : List SSAVar
  loopResultName : String := "__simple_loop_state"
  condResultName : String := "__simple_cond_state"
  varCtx : Zag.VarCtx := []

namespace LocalContext

def tys (ctx : LocalContext) : List Zag.Ty :=
  Zag.Lang.SSA.SSAVar.tys ctx.vars

def resultTy (ctx : LocalContext) : Zag.Ty :=
  match ctx.vars with
  | [v] => v.ty
  | _ => .struct ctx.tys

def currentValues {primCtx : Zag.PrimitiveCtx} (ctx : LocalContext) : List (SSAValue primCtx) :=
  ctx.vars.map fun v => .var v.name

def packCurrent {primCtx : Zag.PrimitiveCtx} (ctx : LocalContext) : SSAValue primCtx :=
  match ctx.vars with
  | [v] => .var v.name
  | _ => .struct ctx.tys ctx.currentValues

def packSourceState {primCtx : Zag.PrimitiveCtx} (ctx : LocalContext) : SSAValue primCtx :=
  .call (.primFunc (_root_.Lang.Simple.statePackName ctx.vars.length)) ctx.currentValues

def inputEnvFrom {primCtx : Zag.PrimitiveCtx} :
    List SSAVar -> Nat -> List (String × Zag.Term primCtx)
  | [], _idx => []
  | v :: vars, idx => (v.name, .var idx) :: inputEnvFrom vars (idx + 1)

def inputEnv {primCtx : Zag.PrimitiveCtx} (ctx : LocalContext) : List (String × Zag.Term primCtx) :=
  inputEnvFrom ctx.vars 0

def hasVarName (ctx : LocalContext) (name : String) : Bool :=
  ctx.vars.any fun v => v.name == name

def unpackBindings {primCtx : Zag.PrimitiveCtx}
    (ctx : LocalContext)
    (packed : SSAValue primCtx) : List (String × SSAValue primCtx) :=
  match ctx.vars with
  | [] => []
  | [v] => [(v.name, packed)]
  | _ =>
      (List.finRange ctx.vars.length).map fun idx =>
        (ctx.vars[idx].name, .field ctx.tys (Zag.Lang.SSA.SSAVar.tyIndex idx) packed)

end LocalContext

def letBindings {primCtx : Zag.PrimitiveCtx}
    (bindings : List (String × SSAValue primCtx))
    (body : SSAExpr primCtx) : SSAExpr primCtx :=
  match bindings with
  | [] => body
  | (name, value) :: bindings => .let_ name value (letBindings bindings body)

def replaceAt? {α : Type u} : List α -> Nat -> α -> Option (List α)
  | [], _, _ => none
  | _ :: values, 0, value => some (value :: values)
  | head :: values, idx + 1, value => do
      let values' <- replaceAt? values idx value
      some (head :: values')

def stateGetIndex? (ctx : LocalContext) (name : String) : Option (Fin ctx.vars.length) :=
  (List.finRange ctx.vars.length).find? fun idx =>
    _root_.Lang.Simple.stateGetName idx.val == name

def stateSetIndex? (ctx : LocalContext) (name : String) : Option (Fin ctx.vars.length) :=
  (List.finRange ctx.vars.length).find? fun idx =>
    _root_.Lang.Simple.stateSetName idx.val == name

def isStatePackName (ctx : LocalContext) (name : String) : Bool :=
  name == _root_.Lang.Simple.statePackName ctx.vars.length

mutual

partial def termToSSAValue? {simpleCtx : _root_.Lang.Simple.Context}
    (ctx : LocalContext) : Zag.Term simpleCtx.primCtx -> Option (SSAValue simpleCtx.primCtx)
  | .prim ty value =>
      some (.raw (.prim ty value))
  | .primFunc name =>
      some (.primFunc name)
  | .var 0 =>
      some ctx.packSourceState
  | .var _ =>
      none
  | .app (.primFunc name) [stateTerm] =>
      match stateGetIndex? ctx name with
      | some idx => do
          let fields <- stateTermFields? ctx stateTerm
          fields[idx.val]?
      | none => do
          let stateValue <- termToSSAValue? ctx stateTerm
          some (.call (.primFunc name) [stateValue])
  | .app f args => do
      let fn <- termToSSAValue? ctx f
      let args <- termsToSSAValues? ctx args
      some (.call fn args)
  | .primEq lhs rhs => do
      let lhs <- termToSSAValue? ctx lhs
      let rhs <- termToSSAValue? ctx rhs
      some (.primEq lhs rhs)
  | .primLt lhs rhs => do
      let lhs <- termToSSAValue? ctx lhs
      let rhs <- termToSSAValue? ctx rhs
      some (.primLt lhs rhs)
  | .primGt lhs rhs => do
      let lhs <- termToSSAValue? ctx lhs
      let rhs <- termToSSAValue? ctx rhs
      some (.primGt lhs rhs)
  | .mkStruct tys =>
      some (.raw (.mkStruct tys))
  | .structProj tys idx =>
      some (.raw (.structProj tys idx))
  | .ite _ _ _ =>
      none
  | .recurse _ _ _ =>
      none

partial def termsToSSAValues? {simpleCtx : _root_.Lang.Simple.Context}
    (ctx : LocalContext) : List (Zag.Term simpleCtx.primCtx) -> Option (List (SSAValue simpleCtx.primCtx))
  | [] => some []
  | term :: terms => do
      let value <- termToSSAValue? ctx term
      let values <- termsToSSAValues? ctx terms
      some (value :: values)

partial def stateTermFields? {simpleCtx : _root_.Lang.Simple.Context}
    (ctx : LocalContext) : Zag.Term simpleCtx.primCtx -> Option (List (SSAValue simpleCtx.primCtx))
  | .var 0 =>
      some ctx.currentValues
  | .app (.primFunc name) fields =>
      if isStatePackName ctx name then
        if fields.length = ctx.vars.length then
          termsToSSAValues? ctx fields
        else
          none
      else
        match stateSetIndex? ctx name, fields with
        | some idx, [stateTerm, valueTerm] => do
            let values <- stateTermFields? ctx stateTerm
            let value <- termToSSAValue? ctx valueTerm
            replaceAt? values idx.val value
        | _, _ => none
  | _ => none

end

def assignFields? {primCtx : Zag.PrimitiveCtx}
    (ctx : LocalContext)
    (fields : List (SSAValue primCtx))
    (body : SSAExpr primCtx) : Option (SSAExpr primCtx) :=
  if fields.length = ctx.vars.length then
    some (letBindings ((ctx.vars.zip fields).map fun binding => (binding.1.name, binding.2)) body)
  else
    none

def assignPackedLocals? {primCtx : Zag.PrimitiveCtx}
    (ctx : LocalContext)
    (packedName : String)
    (packed : SSAValue primCtx)
    (body : SSAExpr primCtx) : Option (SSAExpr primCtx) :=
  match ctx.vars with
  | [] => some body
  | [_] => some (letBindings (ctx.unpackBindings packed) body)
  | _ =>
      if ctx.hasVarName packedName then
        none
      else
        some (.let_ packedName packed (letBindings (ctx.unpackBindings (.var packedName)) body))

def retToYield {primCtx : Zag.PrimitiveCtx}
    (ctx : LocalContext)
    (expr : SSAExpr primCtx) : Option (SSAExpr primCtx) :=
  match expr with
  | .ret _ => some (.yield ctx.currentValues)
  | .let_ name value body => do
      let body' <- retToYield ctx body
      some (.let_ name value body')
  | .seq expr next => do
      let next' <- retToYield ctx next
      some (.seq expr next')
  | .ite cond thenExpr elseExpr => do
      let thenExpr' <- retToYield ctx thenExpr
      let elseExpr' <- retToYield ctx elseExpr
      some (.ite cond thenExpr' elseExpr')
  | .yield values => some (.yield values)

def toSSA? {simpleCtx : _root_.Lang.Simple.Context} {proc : Type u} {fault : Type v}
    (ctx : LocalContext) : _root_.Lang.Simple.Com simpleCtx proc fault -> Option (SSAExpr simpleCtx.primCtx)
  | .Skip =>
      some (.ret ctx.packCurrent)
  | .Basic update => do
      let fields <- stateTermFields? ctx update.val
      assignFields? ctx fields (.ret ctx.packCurrent)
  | .Seq c1 c2 => do
      let first <- toSSA? ctx c1
      let second <- toSSA? ctx c2
      some (Zag.Lang.SSA.SSAExpr.seqLetBindings first second)
  | .Cond condition thenCmd elseCmd => do
      let condition <- termToSSAValue? ctx condition.val
      let thenExpr <- toSSA? ctx thenCmd
      let elseExpr <- toSSA? ctx elseCmd
      assignPackedLocals? ctx ctx.condResultName
        (.block ctx.resultTy (.ite condition thenExpr elseExpr))
        (.ret ctx.packCurrent)
  | .While condition body => do
      let condition <- termToSSAValue? ctx condition.val
      let bodyExpr <- toSSA? ctx body
      let bodyYield <- retToYield ctx bodyExpr
      let loopBody := Zag.Lang.SSA.SSAExpr.ite condition bodyYield (.ret ctx.packCurrent)
      let loopValue := Zag.Lang.SSA.SSAValue.loopBody
        ctx.varCtx ctx.vars ctx.currentValues ctx.resultTy loopBody
      assignPackedLocals? ctx ctx.loopResultName loopValue (.ret ctx.packCurrent)
  | .Call _ => none
  | .Throw => none
  | .Catch _ _ => none

def toTermWithLocals? {primCtx : Zag.PrimitiveCtx}
    (ctx : LocalContext)
    (expr : SSAExpr primCtx) : Option (Zag.Term primCtx) :=
  Zag.Lang.SSA.SSAExpr.toTerm? expr { vars := ctx.inputEnv }

def evalSSAWithLocals? {simpleCtx : _root_.Lang.Simple.Context}
    (ctx : LocalContext)
    (env : List (Zag.Val simpleCtx.primCtx))
    (expr : SSAExpr simpleCtx.primCtx) : Option (Zag.Val simpleCtx.primCtx) := do
  let term <- toTermWithLocals? ctx expr
  Zag.Term.eval simpleCtx.primCtx simpleCtx.primFuncCtx env term

def evalBasic? {simpleCtx : _root_.Lang.Simple.Context}
    (state : Zag.Val simpleCtx.primCtx)
    (update : _root_.Lang.Simple.Basic simpleCtx) : Option (Zag.Val simpleCtx.primCtx) :=
  Zag.Term.eval simpleCtx.primCtx simpleCtx.primFuncCtx [state] update.val

def evalBExp? {simpleCtx : _root_.Lang.Simple.Context}
    (state : Zag.Val simpleCtx.primCtx)
    (condition : _root_.Lang.Simple.BExp simpleCtx) : Option Bool := do
  let value <- Zag.Term.eval simpleCtx.primCtx simpleCtx.primFuncCtx [state] condition.val
  value.asBool?

inductive BigStep {simpleCtx : _root_.Lang.Simple.Context} {proc : Type u} {fault : Type v} :
    _root_.Lang.Simple.Com simpleCtx proc fault ->
      Zag.Val simpleCtx.primCtx -> Zag.Val simpleCtx.primCtx -> Prop where
  | skip (state : Zag.Val simpleCtx.primCtx) :
      BigStep .Skip state state
  | basic {update : _root_.Lang.Simple.Basic simpleCtx} {source target : Zag.Val simpleCtx.primCtx} :
      evalBasic? source update = some target ->
      BigStep (.Basic update) source target
  | seq {c1 c2 : _root_.Lang.Simple.Com simpleCtx proc fault}
      {source mid target : Zag.Val simpleCtx.primCtx} :
      BigStep c1 source mid ->
      BigStep c2 mid target ->
      BigStep (.Seq c1 c2) source target
  | condTrue {condition : _root_.Lang.Simple.BExp simpleCtx}
      {thenCmd elseCmd : _root_.Lang.Simple.Com simpleCtx proc fault}
      {source target : Zag.Val simpleCtx.primCtx} :
      evalBExp? source condition = some true ->
      BigStep thenCmd source target ->
      BigStep (.Cond condition thenCmd elseCmd) source target
  | condFalse {condition : _root_.Lang.Simple.BExp simpleCtx}
      {thenCmd elseCmd : _root_.Lang.Simple.Com simpleCtx proc fault}
      {source target : Zag.Val simpleCtx.primCtx} :
      evalBExp? source condition = some false ->
      BigStep elseCmd source target ->
      BigStep (.Cond condition thenCmd elseCmd) source target
  | whileTrue {condition : _root_.Lang.Simple.BExp simpleCtx}
      {body : _root_.Lang.Simple.Com simpleCtx proc fault}
      {source mid target : Zag.Val simpleCtx.primCtx} :
      evalBExp? source condition = some true ->
      BigStep body source mid ->
      BigStep (.While condition body) mid target ->
      BigStep (.While condition body) source target
  | whileFalse {condition : _root_.Lang.Simple.BExp simpleCtx}
      {body : _root_.Lang.Simple.Com simpleCtx proc fault}
      {source : Zag.Val simpleCtx.primCtx} :
      evalBExp? source condition = some false ->
      BigStep (.While condition body) source source

/-- Relates a source Simple state to the SSA local environment/result convention. -/
structure LocalModel (simpleCtx : _root_.Lang.Simple.Context) (ctx : LocalContext) where
  env : Zag.Val simpleCtx.primCtx -> List (Zag.Val simpleCtx.primCtx)
  result : Zag.Val simpleCtx.primCtx -> Zag.Val simpleCtx.primCtx

/--
  Correctness theorem for local-variable lifting.

  The intended statement is: if source Simple execution reaches `targetState`,
  then the lowered SSA expression evaluates from the corresponding local
  environment to the corresponding target result.
-/
theorem correct {simpleCtx : _root_.Lang.Simple.Context} {proc : Type u} {fault : Type v}
    (ctx : LocalContext)
    (model : LocalModel simpleCtx ctx)
    (cmd : _root_.Lang.Simple.Com simpleCtx proc fault) :
  ∀ (sourceState targetState : Zag.Val simpleCtx.primCtx)
      (expr : SSAExpr simpleCtx.primCtx),
    toSSA? ctx cmd = some expr ->
      BigStep cmd sourceState targetState ->
        evalSSAWithLocals? ctx (model.env sourceState) expr = some (model.result targetState) := by
  sorry

end Lang.Simple.Lift
