import Lang.AutoCorres.CParser.Ast

/-!
# Pure StrictC parser AST actions

Semantic helpers ported from `StrictC.grm` at l4v commit
`bc2599a59c43e673dca021b10b9841e9b8da4430`. Parser state and feedback are
kept out of this module; recovering actions return their diagnostics.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser.AstActions

structure ActionResult (α : Type u) where
  value : α
  diagnostics : List Diagnostic := []
deriving Repr, Inhabited

def enode : Expr → ExprNode
  | .e expression => expression.value

def eregion : Expr → Region
  | .e expression => expression.region

def eleft (expression : Expr) : SourcePos :=
  (eregion expression).left

def eright (expression : Expr) : SourcePos :=
  (eregion expression).right

def wrapExpr (node : ExprNode) (region : Region) : Expr :=
  .e { value := node, region }

def ewrap (node : ExprNode) (left right : SourcePos) : Expr :=
  wrapExpr node { left, right }

def ebogwrap (node : ExprNode) : Expr :=
  wrapExpr node .bogus

def snode : Statement → StatementNode
  | .stmt statement => statement.value

def sregion : Statement → Region
  | .stmt statement => statement.region

def sleft (statement : Statement) : SourcePos :=
  (sregion statement).left

def sright (statement : Statement) : SourcePos :=
  (sregion statement).right

def wrapStatement (node : StatementNode) (region : Region) : Statement :=
  .stmt { value := node, region }

def swrap (node : StatementNode) (left right : SourcePos) : Statement :=
  wrapStatement node { left, right }

def sbogwrap (node : StatementNode) : Statement :=
  wrapStatement node .bogus

def exprInt (value : Int) : Expr :=
  ebogwrap (.constant {
    value := .numConst { value, suffix := "", base := .decimal }
    region := .bogus
  })

def zeroConst : Expr := exprInt 0

def oneConst : Expr := exprInt 1

private def error (region : Region) (message : String) : Diagnostic :=
  { severity := .error, region, message }

private def warning (region : Region) (message : String) : Diagnostic :=
  { severity := .warning, region, message }

private def builtinExpectName : String :=
  "StrictC'__builtin_expect"

def handleBuiltinExpect (expression : Expr) : ActionResult Expr :=
  match enode expression with
  | .eFnCall function arguments =>
      match enode function with
      | .var name _ =>
          if name = builtinExpectName then
            match arguments with
            | [value, _expected] => { value }
            | _ =>
                { value := zeroConst
                  diagnostics := [error (eregion expression)
                    "__builtin_expect must take 2 args."] }
          else
            { value := expression }
      | _ => { value := expression }
  | _ => { value := expression }

def deleteVoidCast (expression : Expr) : Expr :=
  match enode expression with
  | .typeCast type value =>
      match type.value with
      | .void => value
      | _ => expression
  | _ => expression

/-- The restricted lvalue form which may receive a directly classified call. -/
def isSimpleLValue : Expr → Bool
  | .e ⟨.var _ _, _⟩ => true
  | .e ⟨.structDot base _, _⟩ => isSimpleLValue base
  | _ => false

def callAssignment? (left : Option Expr) (expression : Expr) : Option StatementNode :=
  match enode expression with
  | .eFnCall function arguments => some (.assignFnCall left function arguments)
  | _ => none

def assignment (left : Expr) (operator : Option BinOpType) (right : Expr) :
    ActionResult StatementNode :=
  let handled := handleBuiltinExpect right
  let right := handled.value
  let assignedValue :=
    match operator with
    | none => right
    | some binaryOperator =>
        ewrap (.binOp binaryOperator left right) (eleft right) (eright right)
  let value :=
    match enode right with
    | .eFnCall function arguments =>
        if operator.isNone && isSimpleLValue left then
          .assignFnCall (some left) function arguments
        else
          .assign left assignedValue
    | _ => .assign left assignedValue
  { value, diagnostics := handled.diagnostics }

def assignmentStatement (left : Expr) (operator : Option BinOpType) (right : Expr)
    (region : Region) : ActionResult Statement :=
  let result := assignment left operator right
  { value := wrapStatement result.value region, diagnostics := result.diagnostics }

def postIncrement (expression : Expr) : StatementNode :=
  .assign expression (ebogwrap (.binOp .plus expression oneConst))

def postDecrement (expression : Expr) : StatementNode :=
  .assign expression (ebogwrap (.binOp .minus expression oneConst))

def postIncrementStatement (expression : Expr) (region : Region) : Statement :=
  wrapStatement (postIncrement expression) region

def postDecrementStatement (expression : Expr) (region : Region) : Statement :=
  wrapStatement (postDecrement expression) region

def callExpressionStatement? (expression : Expr) (region : Region) :
    ActionResult (Option Statement) :=
  let handled := handleBuiltinExpect expression
  let expression := deleteVoidCast handled.value
  match callAssignment? none expression with
  | some node =>
      { value := some (wrapStatement node region), diagnostics := handled.diagnostics }
  | none => { value := none, diagnostics := handled.diagnostics }

def returnStatement (expression : Option Expr) (region : Region) :
    ActionResult Statement :=
  match expression with
  | none => { value := wrapStatement (.returnStmt none) region }
  | some original =>
      let handled := handleBuiltinExpect original
      let node :=
        match enode handled.value with
        | .eFnCall function arguments => .returnFnCall function arguments
        | _ => .returnStmt (some original)
      { value := wrapStatement node region, diagnostics := handled.diagnostics }

private def attributeEq (left right : GccAttribute) : Bool :=
  reprStr left == reprStr right

private def insertAttribute (newAttribute : GccAttribute)
    (attributes : List GccAttribute) : List GccAttribute :=
  if attributes.any (attributeEq newAttribute) then attributes else newAttribute :: attributes

private def insertName (name : String) : List String → List String
  | [] => [name]
  | current :: rest =>
      if name = current then
        current :: rest
      else if name < current then
        name :: current :: rest
      else
        current :: insertName name rest

/-- Collapse modifies and GCC attributes exactly as `merge_specs` does. -/
def mergeSpecs (first second : List FunctionSpec) : List FunctionSpec :=
  let (modifies, attributes, specifications) :=
    (first ++ second).foldl (fun (modifies, attributes, specifications) spec =>
      match spec with
      | .modifies names =>
          let names := names.foldl (fun names name => insertName name names)
            (modifies.getD [])
          (some names, attributes, specifications)
      | .gccAttributes newAttributes =>
          let attributes := newAttributes.foldl
            (fun attributes newAttribute => insertAttribute newAttribute attributes) attributes
          (modifies, attributes, specifications)
      | specification => (modifies, attributes, specification :: specifications))
      (none, [], [])
  let modifies := modifies.map (fun names => FunctionSpec.modifies names) |>.toList
  let attributes :=
    if attributes.isEmpty then [] else [FunctionSpec.gccAttributes attributes]
  modifies ++ attributes ++ specifications

def whileStatement (condition : Expr) (invariant : Option (Located String))
    (body : Statement) (region : Region) : Statement :=
  let body := wrapStatement (.trap .continue body) (sregion body)
  let loop := wrapStatement (.whileStmt condition invariant body) region
  wrapStatement (.trap .break loop) region

def doWhileStatement (condition : Expr) (invariant : Option (Located String))
    (body : Statement) (region : Region) : Statement :=
  let trappedBody := wrapStatement (.trap .continue body) (sregion body)
  let loop := wrapStatement (.whileStmt condition invariant trappedBody) region
  let blockRegion := Region.append (sregion body) region
  let block := wrapStatement (.block [
    .statement trappedBody,
    .statement loop
  ]) blockRegion
  wrapStatement (.trap .break block) region

def forCondition (condition : Option Expr) : Expr :=
  condition.getD oneConst

def forStatement (initializers : List BlockItem) (condition : Option Expr)
    (step body : Statement) (invariant : Option (Located String))
    (region : Region) : Statement :=
  let trappedBody := wrapStatement (.trap .continue body) (sregion body)
  let loopBody := wrapStatement (.block [
    .statement trappedBody,
    .statement step
  ]) (sregion body)
  let loop := wrapStatement
    (.whileStmt (forCondition condition) invariant loopBody) region
  let trappedLoop := wrapStatement (.trap .break loop) region
  wrapStatement (.block (initializers ++ [.statement trappedLoop])) region

def ifThenStatement (condition : Expr) (thenBranch : Statement)
    (region : Region) : Statement :=
  wrapStatement (.ifStmt condition thenBranch (sbogwrap .emptyStmt)) region

def ifThenElseStatement (condition : Expr) (thenBranch elseBranch : Statement)
    (region : Region) : Statement :=
  wrapStatement (.ifStmt condition thenBranch elseBranch) region

abbrev RawSwitchCase := Located (List (Located (Option Expr))) × List BlockItem

private def lastBlockItem? : List BlockItem → Option BlockItem
  | [] => none
  | [item] => some item
  | _ :: rest => lastBlockItem? rest

mutual
  private def caseEndsWithTransfer : Statement → Bool
    | .stmt ⟨.break, _⟩
    | .stmt ⟨.returnStmt _, _⟩
    | .stmt ⟨.returnFnCall _ _, _⟩ => true
    | .stmt ⟨.ifStmt _ thenBranch elseBranch, _⟩ =>
        caseEndsWithTransfer thenBranch && caseEndsWithTransfer elseBranch
    | .stmt ⟨.block items, _⟩ => blockEndsWithTransfer items
    | _ => false

  private def blockEndsWithTransfer : List BlockItem → Bool
    | [] => false
    | [.statement statement] => caseEndsWithTransfer statement
    | [_] => false
    | _ :: rest => blockEndsWithTransfer rest
end

mutual
  private def stripTrailingBreak : List BlockItem → List BlockItem
    | [] => []
    | [item] => stripTrailingBreakItem item
    | item :: rest => item :: stripTrailingBreak rest

  private def stripTrailingBreakItem : BlockItem → List BlockItem
    | .statement (.stmt ⟨.break, _⟩) => []
    | .statement (.stmt ⟨.block body, region⟩) =>
        [.statement (wrapStatement (.block (stripTrailingBreak body)) region)]
    | item => [item]
end

private def extractDefault : List RawSwitchCase →
    Option RawSwitchCase × List RawSwitchCase × List Diagnostic
  | [] => (none, [], [])
  | current :: rest =>
      let (labels, body) := current
      match labels.value.find? (fun label => label.value.isNone) with
      | some defaultLabel =>
          let diagnostics :=
            if labels.value.length > 1 then
              [warning defaultLabel.region
                "This default: label should be the only label associated with this case"]
            else []
          let defaultCase : RawSwitchCase :=
            ({ value := [defaultLabel], region := labels.region }, body)
          (some defaultCase, rest, diagnostics)
      | none =>
          let (defaultCase, remaining, diagnostics) := extractDefault rest
          (defaultCase, current :: remaining, diagnostics)

private def defaultSwitchCase : RawSwitchCase :=
  ({ value := [{ value := none, region := .bogus }], region := .bogus },
    [.statement (sbogwrap .emptyStmt)])

def cleanSwitchCases (cases : List RawSwitchCase) (region : Region) :
    ActionResult (List (List (Option Expr) × List BlockItem)) :=
  let countDiagnostics :=
    match cases with
    | [] => [error region "Switch has no cases"]
    | [_] => [error region "Switch has only one case"]
    | _ => []
  let breakDiagnostics := cases.dropLast.foldl (fun diagnostics current =>
    let (labels, body) := current
    match lastBlockItem? body with
    | some (.statement statement) =>
      if caseEndsWithTransfer statement then diagnostics
      else diagnostics ++ [error labels.region
        "Switch case beginning here does not end with a break or return"]
    | _ => diagnostics ++ [error labels.region
      "Switch case beginning here does not end with a break or return"]
    ) []
  let (defaultCase, remaining, defaultDiagnostics) := extractDefault cases
  let cases := remaining ++ [defaultCase.getD defaultSwitchCase]
  let cases := cases.map fun (labels, body) =>
    (labels.value.map (fun label => label.value), stripTrailingBreak body)
  { value := cases
    diagnostics := countDiagnostics ++ breakDiagnostics ++ defaultDiagnostics }

def switchStatement (value : Expr) (cases : List RawSwitchCase) (region : Region) :
    ActionResult Statement :=
  let result := cleanSwitchCases cases region
  let switch := wrapStatement (.switch value result.value) region
  { value := wrapStatement (.trap .break switch) region
    diagnostics := result.diagnostics }

end Zag.Lang.AutoCorres.CParser.Parser.AstActions
