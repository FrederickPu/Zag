import Lang.AutoCorres.CParser.Frontend
import Lang.AutoCorres.SimplConv

/-!
# Certified scalar C to SIMPL lowering

This is the first direct analyzed-C lowering slice.  It deliberately accepts a
small, closed fragment and resolves every identifier to the symbol allocated by
`ProgramAnalysis`; source regions are not used as identities.
-/

namespace Zag.Lang.AutoCorres.CParser.ScalarSimpl

open ProgramAnalysis

inductive Error where
  | functionNotFound (name : String)
  | ambiguousFunction (name : String)
  | unsupportedType (name : String) (type : AnalyzedCType)
  | unsupportedExpression (region : Region) (description : String)
  | unsupportedStatement (region : Region) (description : String)
  | unresolvedIdentifier (region : Region) (name : String)
  | argumentCountMismatch (name : String) (expected actual : Nat)
  | malformedAnalysis (description : String)
deriving Repr, Inhabited

inductive Signedness where
  | signed
  | unsigned
deriving Repr, DecidableEq, Inhabited

structure ScalarType where
  signedness : Signedness
  width : Nat
deriving Repr, DecidableEq, Inhabited

namespace ScalarType

def ofCType (target : Target) : AnalyzedCType → Option ScalarType
  | .signed kind => some ⟨.signed, target.intWidthOf kind⟩
  | .unsigned kind => some ⟨.unsigned, target.intWidthOf kind⟩
  | _ => none

def modulus (type : ScalarType) : Int :=
  (2 : Int) ^ type.width

def unsignedValue (type : ScalarType) (value : Int) : Int :=
  ((value % type.modulus) + type.modulus) % type.modulus

def cast (type : ScalarType) (value : Int) : Int :=
  let value := type.unsignedValue value
  match type.signedness with
  | .unsigned => value
  | .signed =>
      let sign := (2 : Int) ^ (type.width - 1)
      if value ≥ sign then value - type.modulus else value

def inRange (type : ScalarType) (value : Int) : Bool :=
  match type.signedness with
  | .unsigned => decide (0 ≤ value ∧ value < type.modulus)
  | .signed =>
      decide (-((2 : Int) ^ (type.width - 1)) ≤ value ∧
        value < (2 : Int) ^ (type.width - 1))

end ScalarType

structure SavedSlot where
  symbolId : Nat
  value : Int
  initialized : Bool
deriving Repr, Inhabited

structure CallFrame where
  slots : List SavedSlot
  returned : Bool
  result : Int
deriving Repr, Inhabited

structure State where
  value : Nat → Int := fun _ => 0
  initialized : Nat → Bool := fun _ => false
  returned : Bool := false
  result : Int := 0
  callStack : List CallFrame := []
  temporaries : List Int := []

namespace State

def read? (state : State) (id : Nat) : Option Int :=
  if state.initialized id then some (state.value id) else none

def write (state : State) (id : Nat) (type : ScalarType) (value : Int) : State :=
  { state with
    value := fun key => if key = id then type.cast value else state.value key
    initialized := fun key => if key = id then true else state.initialized key }

def clear (state : State) (id : Nat) : State :=
  { state with initialized := fun key => if key = id then false else state.initialized key }

def returnValue (state : State) (type : ScalarType) (value : Int) : State :=
  { state with returned := true, result := type.cast value }

def resetReturn (state : State) : State :=
  { state with returned := false }

def saveSlots (state : State) (ids : List Nat) : List SavedSlot :=
  ids.map fun id => SavedSlot.mk id (state.value id) (state.initialized id)

def restoreSlots (state : State) (slots : List SavedSlot) : State :=
  slots.foldl (fun state slot =>
    { state with
      value := fun id => if id = slot.symbolId then slot.value else state.value id
      initialized := fun id => if id = slot.symbolId then slot.initialized else state.initialized id }) state

/-- Enter a direct call after all arguments have been evaluated in the caller. -/
def enterCall (state : State) (parameters : List (Nat × ScalarType))
    (locals : List Nat) (arguments : List Int) : State :=
  let ids := parameters.map (·.1) ++ locals
  let frame : CallFrame :=
    { slots := state.saveSlots ids, returned := state.returned, result := state.result }
  let cleared := ids.foldl State.clear
    { state with returned := false, result := 0, callStack := frame :: state.callStack }
  (parameters.zip arguments).foldl
    (fun current argument => current.write argument.1.1 argument.1.2 argument.2) cleared

/-- Restore the caller frame while retaining global writes and the callee result. -/
def leaveCall? (state : State) : Option (Int × State) := do
  let frame ← state.callStack.head?
  let restored := restoreSlots { state with
    returned := frame.returned, result := frame.result,
    callStack := state.callStack.tail } frame.slots
  return (state.result, restored)

def pushTemporary (state : State) (value : Int) : State :=
  { state with temporaries := value :: state.temporaries }

def popTemporary? (state : State) : Option (Int × State) := do
  let value ← state.temporaries.head?
  return (value, { state with temporaries := state.temporaries.tail })

end State

inductive UnaryOp where
  | negate
  | logicalNot
deriving Repr, DecidableEq, Inhabited

inductive BinaryOp where
  | add | subtract | multiply | divide | modulus
  | equal | notEqual | less | greater | lessEqual | greaterEqual
deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | literal (type : ScalarType) (value : Int)
  | variable (type : ScalarType) (symbolId : Nat)
  | cast (type : ScalarType) (value : Expr)
  | unary (type : ScalarType) (operator : UnaryOp) (value : Expr)
  | binary (type operandType : ScalarType) (operator : BinaryOp) (left right : Expr)
deriving Repr, DecidableEq, Inhabited

namespace Expr

def type : Expr → ScalarType
  | .literal type _ | .variable type _ | .cast type _ | .unary type _ _ |
      .binary type _ _ _ _ => type

def checked (type : ScalarType) (value : Int) : Option Int :=
  match type.signedness with
  | .unsigned => some (type.cast value)
  | .signed => if type.inRange value then some value else none

def truncDiv (left right : Int) : Int :=
  let quotient := Int.ofNat (left.natAbs / right.natAbs)
  if (left < 0) != (right < 0) then -quotient else quotient

def truncMod (left right : Int) : Int :=
  left - truncDiv left right * right

def eval : Expr → State → Option Int
  | .literal type value, _ => some (type.cast value)
  | .variable _ id, state => state.read? id
  | .cast type value, state => return type.cast (← value.eval state)
  | .unary _ .logicalNot value, state =>
      return if (← value.eval state) = 0 then 1 else 0
  | .unary type .negate value, state => do
      checked type (-(← value.eval state))
  | .binary resultType operandType operator left right, state => do
      let left := operandType.cast (← left.eval state)
      let right := operandType.cast (← right.eval state)
      match operator with
      | .add => checked operandType (left + right)
      | .subtract => checked operandType (left - right)
      | .multiply => checked operandType (left * right)
      | .divide =>
          if right = 0 then none
          else if operandType.signedness = .signed &&
              left = -((2 : Int) ^ (operandType.width - 1)) && right = -1 then none
          else some (resultType.cast (truncDiv left right))
      | .modulus =>
          if right = 0 then none
          else if operandType.signedness = .signed &&
              left = -((2 : Int) ^ (operandType.width - 1)) && right = -1 then none
          else some (resultType.cast (truncMod left right))
      | .equal => some (if left = right then 1 else 0)
      | .notEqual => some (if left ≠ right then 1 else 0)
      | .less => some (if left < right then 1 else 0)
      | .greater => some (if left > right then 1 else 0)
      | .lessEqual => some (if left ≤ right then 1 else 0)
      | .greaterEqual => some (if left ≥ right then 1 else 0)

end Expr

namespace Raw

/-- A lexical C binding, retaining both analyzer identity and C type. -/
structure Binding where
  name : String
  symbolId : Nat
  ctype : AnalyzedCType
  type : ScalarType
deriving Repr, Inhabited

abbrev Env := List (List Binding)

namespace Env

private def lookupScope (name : String) : List Binding → Option Binding
  | [] => none
  | binding :: rest => if binding.name = name then some binding else lookupScope name rest

def lookup (name : String) : Env → Option Binding
  | [] => none
  | scope :: scopes => (lookupScope name scope).orElse fun _ => lookup name scopes

def bind (binding : Binding) : Env → Env
  | [] => [[binding]]
  | scope :: scopes => (binding :: scope) :: scopes

end Env

def scalarCType : CType CParser.Expr → Option AnalyzedCType
  | .signed kind => some (.signed kind)
  | .unsigned kind => some (.unsigned kind)
  | _ => none

private def checked (type : ScalarType) (value : Int) : Option Int :=
  match type.signedness with
  | .unsigned => some (type.cast value)
  | .signed => if type.inRange value then some value else none

private def truncDiv (left right : Int) : Int :=
  let quotient := Int.ofNat (left.natAbs / right.natAbs)
  if (left < 0) != (right < 0) then -quotient else quotient

private def truncMod (left right : Int) : Int :=
  left - truncDiv left right * right

def isRelational : BinOpType → Bool
  | .equals | .notEquals | .lt | .gt | .leq | .geq => true
  | _ => false

/-- Direct evaluation of accepted raw C expressions. Unsupported syntax and C UB return `none`. -/
def evalExpr (target : Target) (environment : Env) : CParser.Expr → State →
    Option (AnalyzedCType × Int)
  | .e ⟨node, _⟩, state => do
      match node with
      | .constant ⟨.numConst info, _⟩ =>
          let ctype ← ProgramAnalysis.numericLiteralType target info
          let type ← ScalarType.ofCType target ctype
          return (ctype, type.cast info.value)
      | .var name _ =>
          let binding ← environment.lookup name
          return (binding.ctype, ← state.read? binding.symbolId)
      | .typeCast rawType value =>
          let ctype ← scalarCType rawType.value
          let type ← ScalarType.ofCType target ctype
          let (_, value) ← evalExpr target environment value state
          return (ctype, type.cast value)
      | .unOp .negate value =>
          let (ctype, value) ← evalExpr target environment value state
          let promoted := ctype.integerPromotions target
          let type ← ScalarType.ofCType target promoted
          return (promoted, ← checked type (-value))
      | .unOp .not value =>
          let (_, value) ← evalExpr target environment value state
          return (.signed .int, if value = 0 then 1 else 0)
      | .binOp operator left right =>
          let (leftType, left) ← evalExpr target environment left state
          let (rightType, right) ← evalExpr target environment right state
          let operandCType ← (CType.arithmeticConversion target leftType rightType).toOption
          let operandType ← ScalarType.ofCType target operandCType
          let left := operandType.cast left
          let right := operandType.cast right
          let relational := isRelational operator
          let resultCType := if relational then .signed .int else operandCType
          let resultType := if relational then
            { signedness := .signed, width := target.intWidth } else operandType
          let result ← match operator with
            | .plus => checked operandType (left + right)
            | .minus => checked operandType (left - right)
            | .times => checked operandType (left * right)
            | .divides =>
                if right = 0 then none
                else if operandType.signedness = .signed &&
                    left = -((2 : Int) ^ (operandType.width - 1)) && right = -1 then none
                else some (resultType.cast (truncDiv left right))
            | .modulus =>
                if right = 0 then none
                else if operandType.signedness = .signed &&
                    left = -((2 : Int) ^ (operandType.width - 1)) && right = -1 then none
                else some (resultType.cast (truncMod left right))
            | .equals => some (if left = right then 1 else 0)
            | .notEquals => some (if left ≠ right then 1 else 0)
            | .lt => some (if left < right then 1 else 0)
            | .gt => some (if left > right then 1 else 0)
            | .leq => some (if left ≤ right then 1 else 0)
            | .geq => some (if left ≥ right then 1 else 0)
            | _ => none
          return (resultCType, result)
      | .mkBool value =>
          let (_, value) ← evalExpr target environment value state
          return (.signed .int, if value = 0 then 0 else 1)
      | _ => none
termination_by expression _ => sizeOf expression
decreasing_by all_goals simp_wf <;> decreasing_trivial

def bindingFor? (program : Program) (id : Nat) : Option Binding := do
  let symbol ← program.symbolById? id
  let type ← ScalarType.ofCType program.target symbol.type
  return { name := symbol.sourceName, symbolId := id, ctype := symbol.type, type }

theorem bindingFor_symbolId {id : Nat} {binding : Binding}
    (bindingEq : bindingFor? program id = some binding) :
    binding.symbolId = id := by
  unfold bindingFor? at bindingEq
  cases symbolEq : program.symbolById? id with
  | none => simp [symbolEq] at bindingEq
  | some symbol =>
      simp only [symbolEq] at bindingEq
      cases typeEq : ScalarType.ofCType program.target symbol.type with
      | none => simp [typeEq] at bindingEq
      | some type =>
          simp [typeEq] at bindingEq
          cases bindingEq
          rfl

def localBinding? (program : Program) (functionId : Nat) (region : Region)
    (name : String) (rawType : CType CParser.Expr) : Option Binding := do
  let ctype ← scalarCType rawType
  let symbol ← match program.symbols.filter fun symbol =>
      symbol.sourceName = name && symbol.region = region && symbol.kind = .local functionId with
    | [symbol] => some symbol
    | _ => none
  if symbol.type != ctype then none
  let binding ← bindingFor? program symbol.id
  if binding.name != name || binding.ctype != symbol.type then none
  return binding

inductive Outcome where
  | normal (state : State)
  | returned (state : State)
  | undefinedBehavior

mutual
  /-- Direct finite execution of an accepted raw C statement. -/
  inductive StatementExec (program : Program) (functionId : Nat) (returnType : ScalarType) :
      Statement → Env → State → Outcome → Prop where
    | assign
        (bound : environment.lookup name = some binding)
        (evaluation : evalExpr program.target environment value state = some (ctype, result)) :
        StatementExec program functionId returnType
          (.stmt ⟨.assign (.e ⟨.var name info, leftRegion⟩) value, region⟩) environment state
          (.normal (state.write binding.symbolId binding.type result))
    | assignFault
        (bound : environment.lookup name = some binding)
        (evaluation : evalExpr program.target environment value state = none) :
        StatementExec program functionId returnType
          (.stmt ⟨.assign (.e ⟨.var name info, leftRegion⟩) value, region⟩) environment state
          .undefinedBehavior
    | block (execution : BodyExec program functionId returnType items ([] :: environment) state outcome) :
        StatementExec program functionId returnType
          (.stmt ⟨.block items, region⟩) environment state outcome
    | trap (execution : StatementExec program functionId returnType body environment state outcome) :
        StatementExec program functionId returnType
          (.stmt ⟨.trap kind body, region⟩) environment state outcome
    | ret (evaluation : evalExpr program.target environment value state = some (ctype, result)) :
        StatementExec program functionId returnType
          (.stmt ⟨.returnStmt (some value), region⟩) environment state
          (.returned (state.returnValue returnType result))
    | retFault (evaluation : evalExpr program.target environment value state = none) :
        StatementExec program functionId returnType
          (.stmt ⟨.returnStmt (some value), region⟩) environment state .undefinedBehavior
    | condTrue
        (evaluation : evalExpr program.target environment condition state = some (ctype, value))
        (nonzero : value ≠ 0)
        (branch : StatementExec program functionId returnType thenBranch environment state outcome) :
        StatementExec program functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state outcome
    | condFalse
        (evaluation : evalExpr program.target environment condition state = some (ctype, 0))
        (branch : StatementExec program functionId returnType elseBranch environment state outcome) :
        StatementExec program functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state outcome
    | condFault (evaluation : evalExpr program.target environment condition state = none) :
        StatementExec program functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state
          .undefinedBehavior
    | whileFalse (evaluation : evalExpr program.target environment condition state = some (ctype, 0)) :
        StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state (.normal state)
    | whileTrue
        (evaluation : evalExpr program.target environment condition state = some (ctype, value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec program functionId returnType body environment state (.normal middle))
        (rest : StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment middle outcome) :
        StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state outcome
    | whileRet
        (evaluation : evalExpr program.target environment condition state = some (ctype, value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec program functionId returnType body environment state (.returned result)) :
        StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state (.returned result)
    | whileBodyFault
        (evaluation : evalExpr program.target environment condition state = some (ctype, value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec program functionId returnType body environment state .undefinedBehavior) :
        StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state .undefinedBehavior
    | whileGuardFault (evaluation : evalExpr program.target environment condition state = none) :
        StatementExec program functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state .undefinedBehavior
    | empty : StatementExec program functionId returnType
        (.stmt ⟨.emptyStmt, region⟩) environment state (.normal state)

  /-- Direct finite execution of raw block items, including lexical declaration scope. -/
  inductive BodyExec (program : Program) (functionId : Nat) (returnType : ScalarType) :
      List BlockItem → Env → State → Outcome → Prop where
    | nil : BodyExec program functionId returnType [] environment state (.normal state)
    | statementNormal
        (first : StatementExec program functionId returnType statement environment state (.normal middle))
        (rest : BodyExec program functionId returnType items environment middle outcome) :
        BodyExec program functionId returnType (.statement statement :: items) environment state outcome
    | statementReturned
        (first : StatementExec program functionId returnType statement environment state (.returned result)) :
        BodyExec program functionId returnType (.statement statement :: items) environment state
          (.returned result)
    | statementFault
        (first : StatementExec program functionId returnType statement environment state .undefinedBehavior) :
        BodyExec program functionId returnType (.statement statement :: items) environment state
          .undefinedBehavior
    | declaration
        (bindingEq : localBinding? program functionId declarationRegion name.value rawType = some binding)
        (rest : BodyExec program functionId returnType items (environment.bind binding)
          (state.clear binding.symbolId) outcome) :
        BodyExec program functionId returnType
          (.declaration ⟨.varDecl rawType name [] none attributes, declarationRegion⟩ :: items)
          environment state outcome
    | init
        (bindingEq : localBinding? program functionId declarationRegion name.value rawType = some binding)
        (evaluation : evalExpr program.target (environment.bind binding) value
          (state.clear binding.symbolId) = some (ctype, result))
        (rest : BodyExec program functionId returnType items (environment.bind binding)
          ((state.clear binding.symbolId).write binding.symbolId binding.type result) outcome) :
        BodyExec program functionId returnType
          (.declaration ⟨.varDecl rawType name [] (some (.initE value)) attributes,
            declarationRegion⟩ :: items) environment state outcome
    | initFault
        (bindingEq : localBinding? program functionId declarationRegion name.value rawType = some binding)
        (evaluation : evalExpr program.target (environment.bind binding) value
          (state.clear binding.symbolId) = none) :
        BodyExec program functionId returnType
          (.declaration ⟨.varDecl rawType name [] (some (.initE value)) attributes,
            declarationRegion⟩ :: items) environment state .undefinedBehavior
end

def parameterBindings? (program : Program) (functionId : Nat) : List Nat → Option (List Binding)
  | [] => some []
  | id :: ids => do
    let binding ← bindingFor? program id
    return binding :: (← parameterBindings? program functionId ids)

def parameterEnv? (program : Program) (functionId : Nat) (parameters : List Nat) : Option Env :=
  (parameterBindings? program functionId parameters).map fun bindings => [bindings]

/-- Source-level function outcomes do not mention SIMPL control states. -/
inductive FunctionOutcome where
  | success (state : State)
  | undefinedBehavior

inductive FunctionExec (program : Program) (name : String) (info : FunctionInfo)
    (rawBody : Body) (returnType : ScalarType) : State → FunctionOutcome → Prop where
  | returned
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec program info.symbolId returnType rawBody.value environment state.resetReturn
        (.returned result)) :
      FunctionExec program name info rawBody returnType state (.success result)
  | fault
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec program info.symbolId returnType rawBody.value environment state.resetReturn
        .undefinedBehavior) :
      FunctionExec program name info rawBody returnType state .undefinedBehavior
  | fellOff
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec program info.symbolId returnType rawBody.value environment state.resetReturn
        (.normal result)) :
      FunctionExec program name info rawBody returnType state
        (if name = "main" then .success (result.returnValue returnType 0) else .undefinedBehavior)

mutual
  def runStatement (fuel : Nat) (program : Program) (functionId : Nat)
      (returnType : ScalarType) (environment : Env) (state : State) : Statement → Option Outcome
    | statement =>
        match fuel, statement with
        | 0, _ => none
        | _ + 1, .stmt ⟨.assign (.e ⟨.var name _, _⟩) value, _⟩ =>
            match environment.lookup name, evalExpr program.target environment value state with
            | some binding, some (_, result) => some (.normal (state.write binding.symbolId binding.type result))
            | _, _ => some .undefinedBehavior
        | next + 1, .stmt ⟨.block items, _⟩ =>
            runBody next program functionId returnType environment state items
        | next + 1, .stmt ⟨.trap _ body, _⟩ =>
            runStatement next program functionId returnType environment state body
        | _ + 1, .stmt ⟨.returnStmt (some value), _⟩ =>
            match evalExpr program.target environment value state with
            | some (_, result) => some (.returned (state.returnValue returnType result))
            | none => some .undefinedBehavior
        | next + 1, .stmt ⟨.ifStmt condition thenBranch elseBranch, _⟩ =>
            match evalExpr program.target environment condition state with
            | some (_, value) => runStatement next program functionId returnType environment state
                (if value = 0 then elseBranch else thenBranch)
            | none => some .undefinedBehavior
        | next + 1, .stmt ⟨statement@(.whileStmt condition _ body), region⟩ =>
            match evalExpr program.target environment condition state with
            | none => some .undefinedBehavior
            | some (_, 0) => some (.normal state)
            | some _ =>
                match runStatement next program functionId returnType environment state body with
                | some (.normal middle) => runStatement next program functionId returnType environment middle
                    (.stmt ⟨statement, region⟩)
                | outcome => outcome
        | _ + 1, .stmt ⟨.emptyStmt, _⟩ => some (.normal state)
        | _, _ => some .undefinedBehavior

  def runBody (fuel : Nat) (program : Program) (functionId : Nat)
      (returnType : ScalarType) (environment : Env) (state : State) : List BlockItem → Option Outcome
    | items =>
        match fuel, items with
        | 0, _ => none
        | _ + 1, [] => some (.normal state)
        | next + 1, .statement statement :: items =>
            match runStatement next program functionId returnType environment state statement with
            | some (.normal middle) => runBody next program functionId returnType environment middle items
            | outcome => outcome
        | next + 1, .declaration declaration :: items =>
            match declaration.value with
            | .varDecl rawType name [] initializer _ =>
                match localBinding? program functionId declaration.region name.value rawType with
                | none => some .undefinedBehavior
                | some binding =>
                    match initializer with
                    | none => runBody next program functionId returnType (environment.bind binding)
                        (state.clear binding.symbolId) items
                    | some (.initE value) =>
                        let bound := environment.bind binding
                        let cleared := state.clear binding.symbolId
                        match evalExpr program.target bound value cleared with
                        | some (_, result) => runBody next program functionId returnType
                            bound (cleared.write binding.symbolId binding.type result) items
                        | none => some .undefinedBehavior
                    | _ => some .undefinedBehavior
            | _ => some .undefinedBehavior
end

def runFunction (fuel : Nat) (program : Program) (name : String) (info : FunctionInfo)
    (rawBody : Body) (returnType : ScalarType) (state : State) : Option FunctionOutcome :=
  match parameterEnv? program info.symbolId info.parameters with
  | none => some .undefinedBehavior
  | some environment =>
      match runBody fuel program info.symbolId returnType environment state.resetReturn rawBody.value with
      | none => none
      | some (.returned result) => some (.success result)
      | some .undefinedBehavior => some .undefinedBehavior
      | some (.normal result) =>
          some (if name = "main" then .success (result.returnValue returnType 0) else .undefinedBehavior)

end Raw

inductive Stmt where
  | skip
  | seq (first second : Stmt)
  | assign (symbolId : Nat) (type : ScalarType) (value : Expr)
  | declare (symbolId : Nat) (type : ScalarType) (initializer : Option Expr)
  | return (type : ScalarType) (value : Expr)
  | cond (condition : Expr) (thenStmt elseStmt : Stmt)
  | while (condition : Expr) (body : Stmt)
deriving Repr, DecidableEq, Inhabited

inductive Outcome where
  | normal (state : State)
  | returned (state : State)
  | fault

namespace Stmt

def declaredIds : Stmt → List Nat
  | .skip | .assign .. | .return .. => []
  | .declare id _ _ => [id]
  | .seq first second => first.declaredIds ++ second.declaredIds
  | .cond _ thenStmt elseStmt => thenStmt.declaredIds ++ elseStmt.declaredIds
  | .while _ body => body.declaredIds

/-- Big-step semantics independent of SIMPL.  Expression failure is C undefined behavior. -/
inductive Exec : Stmt → State → Outcome → Prop where
  | skip : Exec .skip state (.normal state)
  | seqNormal : Exec first state (.normal middle) → Exec second middle outcome →
      Exec (.seq first second) state outcome
  | seqReturned : Exec first state (.returned result) →
      Exec (.seq first second) state (.returned result)
  | seqFault : Exec first state .fault → Exec (.seq first second) state .fault
  | assign (id : Nat) (type : ScalarType) (value : Expr)
      (evaluation : value.eval state = some result) :
      Exec (.assign id type value) state (.normal (state.write id type result))
  | assignFault (id : Nat) (type : ScalarType) (value : Expr)
      (evaluation : value.eval state = none) :
      Exec (.assign id type value) state .fault
  | declare (id : Nat) (type : ScalarType) :
      Exec (.declare id type none) state (.normal (state.clear id))
  | init (id : Nat) (type : ScalarType) (value : Expr)
      (evaluation : value.eval (state.clear id) = some result) :
      Exec (.declare id type (some value)) state
        (.normal ((state.clear id).write id type result))
  | initFault (id : Nat) (type : ScalarType) (value : Expr)
      (evaluation : value.eval (state.clear id) = none) :
      Exec (.declare id type (some value)) state .fault
  | ret (evaluation : value.eval state = some result) :
      Exec (.return type value) state (.returned (state.returnValue type result))
  | retFault (evaluation : value.eval state = none) :
      Exec (.return type value) state .fault
  | condTrue (evaluation : condition.eval state = some value) (nonzero : value ≠ 0)
      (branch : Exec thenStmt state outcome) :
      Exec (.cond condition thenStmt elseStmt) state outcome
  | condFalse (evaluation : condition.eval state = some 0)
      (branch : Exec elseStmt state outcome) :
      Exec (.cond condition thenStmt elseStmt) state outcome
  | condFault (evaluation : condition.eval state = none) :
      Exec (.cond condition thenStmt elseStmt) state .fault
  | whileFalse (evaluation : condition.eval state = some 0) :
      Exec (.while condition body) state (.normal state)
  | whileTrue (evaluation : condition.eval state = some value) (nonzero : value ≠ 0)
      (iteration : Exec body state (.normal middle))
      (rest : Exec (.while condition body) middle outcome) :
      Exec (.while condition body) state outcome
  | whileRet (evaluation : condition.eval state = some value) (nonzero : value ≠ 0)
      (iteration : Exec body state (.returned result)) :
      Exec (.while condition body) state (.returned result)
  | whileBodyFault (evaluation : condition.eval state = some value) (nonzero : value ≠ 0)
      (iteration : Exec body state .fault) :
      Exec (.while condition body) state .fault
  | whileGuardFault (evaluation : condition.eval state = none) :
      Exec (.while condition body) state .fault

end Stmt

inductive Fault where
  | undefinedBehavior
deriving Repr, DecidableEq, Inhabited

def Raw.embedOutcome : Raw.FunctionOutcome → Simpl.XState State Fault
  | .success state => .normal state
  | .undefinedBehavior => .fault .undefinedBehavior

theorem Raw.embedOutcome_injective : Function.Injective Raw.embedOutcome := by
  intro left right
  cases left <;> cases right <;> simp_all [Raw.embedOutcome]

abbrev Command := Simpl.Com State Nat Fault
abbrev Environment := Simpl.Body State Nat Fault

def emptyEnvironment : Environment := fun _ => none

private def valid (expression : Expr) (state : State) : Prop :=
  ∃ value, expression.eval state = some value

private def expressionValue (expression : Expr) (state : State) : Int :=
  (expression.eval state).getD 0

private def assignCommand (id : Nat) (type : ScalarType) (value : Expr) : Command :=
  .Guard .undefinedBehavior (valid value)
    (.Basic fun state => state.write id type (expressionValue value state))

def compile : Stmt → Command
  | .skip => .Skip
  | .seq first second => .Seq (compile first) (compile second)
  | .assign id type value => assignCommand id type value
  | .declare id _ none => .Basic fun state => state.clear id
  | .declare id type (some value) =>
      .Seq (.Basic fun state => state.clear id) (assignCommand id type value)
  | .return type value =>
      .Guard .undefinedBehavior (valid value)
        (.Seq (.Basic fun state => state.returnValue type (expressionValue value state)) .Throw)
  | .cond condition thenStmt elseStmt =>
      .Guard .undefinedBehavior (valid condition)
        (.Cond (fun state => expressionValue condition state ≠ 0)
          (compile thenStmt) (compile elseStmt))
  | .while condition body =>
      .While (fun state => condition.eval state ≠ some 0)
        (.Seq (.Guard .undefinedBehavior (valid condition) .Skip) (compile body))

def supported : (statement : Stmt) → SimplConv.Kernel.Supported (compile statement)
  | .skip => .skip
  | .seq first second => .seq (supported first) (supported second)
  | .assign id type value => by
      simpa [compile, assignCommand] using
        (SimplConv.Kernel.Supported.guard Fault.undefinedBehavior (valid value)
          (SimplConv.Kernel.Supported.basic fun state : State =>
            state.write id type (expressionValue value state)))
  | .declare id type none => by
      simpa [compile] using (SimplConv.Kernel.Supported.basic fun state : State => state.clear id)
  | .declare id type (some value) => by
      simpa [compile, assignCommand] using
        (SimplConv.Kernel.Supported.seq
          (SimplConv.Kernel.Supported.basic fun state : State => state.clear id)
          (SimplConv.Kernel.Supported.guard Fault.undefinedBehavior (valid value)
            (SimplConv.Kernel.Supported.basic fun state : State =>
              state.write id type (expressionValue value state))))
  | .return type value => by
      simpa [compile] using
        (SimplConv.Kernel.Supported.guard Fault.undefinedBehavior (valid value)
          (SimplConv.Kernel.Supported.seq
            (SimplConv.Kernel.Supported.basic fun state : State =>
              state.returnValue type (expressionValue value state))
            SimplConv.Kernel.Supported.throw))
  | .cond condition thenStmt elseStmt => by
      simpa [compile] using
        (SimplConv.Kernel.Supported.guard Fault.undefinedBehavior (valid condition)
          (SimplConv.Kernel.Supported.cond
            (fun state : State => expressionValue condition state ≠ 0)
            (supported thenStmt) (supported elseStmt)))
  | .while condition body =>
      .while (fun state => condition.eval state ≠ some 0)
        (.seq (.guard Fault.undefinedBehavior (valid condition) .skip) (supported body))

def embedOutcome : Outcome → Simpl.XState State Fault
  | .normal state => .normal state
  | .returned state => .abrupt state
  | .fault => .fault .undefinedBehavior

def Corresponds (statement : Stmt) (command : Command) : Prop :=
  ∀ state outcome, Stmt.Exec statement state outcome →
    Simpl.Exec emptyEnvironment command (.normal state) (embedOutcome outcome)

theorem compile_correct (statement : Stmt) : Corresponds statement (compile statement) := by
  intro state outcome execution
  induction execution with
  | skip => exact .skip
  | seqNormal _ _ firstCorrect secondCorrect => exact .seq firstCorrect secondCorrect
  | seqReturned _ firstCorrect => exact .seq firstCorrect .abruptProp
  | seqFault _ firstCorrect => exact .seq firstCorrect .faultProp
  | assign id type value evaluation =>
      rename_i initial result
      apply Simpl.Exec.guard
      · exact ⟨_, evaluation⟩
      · simpa [expressionValue, evaluation, embedOutcome] using
          (Simpl.Exec.basic (env := emptyEnvironment)
            (transform := fun current => current.write id type (expressionValue value current))
            (s := initial))
  | assignFault _ _ _ evaluation =>
      exact .guardFault (by rintro ⟨value, equality⟩; simp [evaluation] at equality)
  | declare _ _ => exact .basic
  | init id type value evaluation =>
      rename_i initial result
      apply Simpl.Exec.seq Simpl.Exec.basic
      apply Simpl.Exec.guard
      · exact ⟨_, evaluation⟩
      · simpa [expressionValue, evaluation, embedOutcome] using
          (Simpl.Exec.basic (env := emptyEnvironment)
            (transform := fun current => current.write id type (expressionValue value current))
            (s := result.clear id))
  | initFault _ _ _ evaluation =>
      apply Simpl.Exec.seq Simpl.Exec.basic
      exact .guardFault (by rintro ⟨value, equality⟩; simp [evaluation] at equality)
  | ret evaluation =>
      rename_i result type value initial
      apply Simpl.Exec.guard ⟨_, evaluation⟩
      apply Simpl.Exec.seq
      · simpa [expressionValue, evaluation] using
          (Simpl.Exec.basic (env := emptyEnvironment)
            (transform := fun current => current.returnValue type (expressionValue value current))
            (s := initial))
      · exact .throw
  | retFault evaluation =>
      exact .guardFault (by rintro ⟨value, equality⟩; simp [evaluation] at equality)
  | condTrue evaluation nonzero _ branchCorrect =>
      apply Simpl.Exec.guard ⟨_, evaluation⟩
      apply Simpl.Exec.condTrue
      · simpa [expressionValue, evaluation]
      · exact branchCorrect
  | condFalse evaluation _ branchCorrect =>
      apply Simpl.Exec.guard ⟨_, evaluation⟩
      apply Simpl.Exec.condFalse
      · simp [expressionValue, evaluation]
      · exact branchCorrect
  | condFault evaluation =>
      exact .guardFault (by rintro ⟨value, equality⟩; simp [evaluation] at equality)
  | whileFalse evaluation =>
      exact .whileFalse (by simp [evaluation])
  | whileTrue evaluation nonzero _ _ iterationCorrect restCorrect =>
      apply Simpl.Exec.whileTrue
      · simp [evaluation, nonzero]
      · apply Simpl.Exec.seq
        · exact .guard ⟨_, evaluation⟩ .skip
        · exact iterationCorrect
      · exact restCorrect
  | whileRet evaluation nonzero _ iterationCorrect =>
      apply Simpl.Exec.whileTrue
      · simp [evaluation, nonzero]
      · apply Simpl.Exec.seq
        · exact .guard ⟨_, evaluation⟩ .skip
        · exact iterationCorrect
      · exact .abruptProp
  | whileBodyFault evaluation nonzero _ iterationCorrect =>
      apply Simpl.Exec.whileTrue
      · simp [evaluation, nonzero]
      · apply Simpl.Exec.seq
        · exact .guard ⟨_, evaluation⟩ .skip
        · exact iterationCorrect
      · exact .faultProp
  | whileGuardFault evaluation =>
      apply Simpl.Exec.whileTrue
      · simp [evaluation]
      · apply Simpl.Exec.seq
        · exact .guardFault (by rintro ⟨value, equality⟩; simp [evaluation] at equality)
        · exact .faultProp
      · exact .faultProp

def sourceOutcome : Simpl.XState State Fault → Outcome
  | .normal state => .normal state
  | .abrupt state => .returned state
  | .fault _ | .stuck => .fault

private theorem exec_from_abrupt (execution :
    Simpl.Exec environment command (.abrupt state) result) : result = .abrupt state := by
  cases execution
  rfl

private theorem exec_from_fault (execution :
    Simpl.Exec environment command (.fault label) result) : result = .fault label := by
  cases execution
  rfl

/-- Reverse finite correspondence. Generated commands cannot finitely execute to `stuck`. -/
theorem compile_complete (statement : Stmt) (execution :
    Simpl.Exec emptyEnvironment (compile statement) (.normal state) result) :
    Stmt.Exec statement state (sourceOutcome result) ∧ result ≠ .stuck := by
  induction statement generalizing state result with
  | skip =>
      cases execution
      exact ⟨.skip, by simp⟩
  | seq first second firstComplete secondComplete =>
      cases execution with
      | seq firstExecution secondExecution =>
          obtain ⟨firstSource, firstNotStuck⟩ := firstComplete firstExecution
          rename_i middle
          cases middle with
          | normal middle =>
              obtain ⟨secondSource, secondNotStuck⟩ := secondComplete secondExecution
              exact ⟨.seqNormal firstSource secondSource, secondNotStuck⟩
          | abrupt middle =>
              rw [exec_from_abrupt secondExecution]
              exact ⟨.seqReturned firstSource, by simp⟩
          | fault label =>
              rw [exec_from_fault secondExecution]
              exact ⟨.seqFault firstSource, by simp⟩
          | stuck => exact False.elim (firstNotStuck rfl)
  | assign id type value =>
      simp only [compile, assignCommand] at execution
      cases execution with
      | guard validExecution bodyExecution =>
          cases bodyExecution
          obtain ⟨evaluated, evaluation⟩ := validExecution
          have exactEvaluation : value.eval state = some (expressionValue value state) := by
            simp [expressionValue, evaluation]
          exact ⟨.assign id type value exactEvaluation, by simp⟩
      | guardFault invalid =>
          have evaluation : value.eval state = none := by
            cases found : value.eval state with
            | none => rfl
            | some result => exact False.elim (invalid ⟨result, found⟩)
          exact ⟨.assignFault id type value evaluation, by simp⟩
  | declare id type initializer =>
      cases initializer with
      | none =>
          simp only [compile] at execution
          cases execution
          exact ⟨.declare id type, by simp⟩
      | some value =>
          simp only [compile, assignCommand] at execution
          cases execution with
          | seq clearExecution initializerExecution =>
              cases clearExecution
              cases initializerExecution with
              | guard validExecution bodyExecution =>
                  cases bodyExecution
                  obtain ⟨evaluated, evaluation⟩ := validExecution
                  have exactEvaluation : value.eval (state.clear id) =
                      some (expressionValue value (state.clear id)) := by
                    simp [expressionValue, evaluation]
                  exact ⟨.init id type value exactEvaluation, by simp⟩
              | guardFault invalid =>
                  have evaluation : value.eval (state.clear id) = none := by
                    cases found : value.eval (state.clear id) with
                    | none => rfl
                    | some result => exact False.elim (invalid ⟨result, found⟩)
                  exact ⟨.initFault id type value evaluation, by simp⟩
  | «return» type value =>
      simp only [compile] at execution
      cases execution with
      | guard validExecution bodyExecution =>
          cases bodyExecution with
          | seq updateExecution throwExecution =>
              cases updateExecution
              cases throwExecution
              obtain ⟨evaluated, evaluation⟩ := validExecution
              have exactEvaluation : value.eval state = some (expressionValue value state) := by
                simp [expressionValue, evaluation]
              exact ⟨.ret exactEvaluation, by simp⟩
      | guardFault invalid =>
          have evaluation : value.eval state = none := by
            cases found : value.eval state with
            | none => rfl
            | some result => exact False.elim (invalid ⟨result, found⟩)
          exact ⟨.retFault evaluation, by simp⟩
  | cond condition thenStmt elseStmt thenComplete elseComplete =>
      simp only [compile] at execution
      cases execution with
      | guard validExecution branchExecution =>
          obtain ⟨value, evaluation⟩ := validExecution
          cases branchExecution with
          | condTrue nonzero thenExecution =>
              have valueNonzero : value ≠ 0 := by
                simpa [expressionValue, evaluation] using nonzero
              obtain ⟨source, notStuck⟩ := thenComplete thenExecution
              exact ⟨.condTrue evaluation valueNonzero source, notStuck⟩
          | condFalse zero elseExecution =>
              have valueZero : value = 0 := by
                simpa [expressionValue, evaluation] using Classical.byContradiction zero
              subst value
              obtain ⟨source, notStuck⟩ := elseComplete elseExecution
              exact ⟨.condFalse evaluation source, notStuck⟩
      | guardFault invalid =>
          have evaluation : condition.eval state = none := by
            cases found : condition.eval state with
            | none => rfl
            | some value => exact False.elim (invalid ⟨value, found⟩)
          exact ⟨.condFault evaluation, by simp⟩
  | «while» condition body bodyComplete =>
      simp only [compile] at execution
      generalize commandEq :
        (Simpl.Com.While (fun state => condition.eval state ≠ some 0)
          (.Seq (.Guard .undefinedBehavior (valid condition) .Skip) (compile body))) = command
        at execution
      generalize inputEq : Simpl.XState.normal state = input at execution
      revert state
      induction execution with
      | whileFalse stopped =>
          intro state inputEq
          let source := state
          cases commandEq
          cases inputEq
          have evaluation : condition.eval source = some 0 := by
            simpa using Classical.byContradiction stopped
          exact ⟨.whileFalse evaluation, by simp⟩
      | whileTrue continues iteration rest iterationComplete restComplete =>
          intro state inputEq
          let source := state
          cases commandEq
          cases inputEq
          cases iteration with
          | seq guardExecution bodyExecution =>
              cases guardExecution with
              | guard valid guardBody =>
                  cases guardBody
                  obtain ⟨value, evaluation⟩ := valid
                  have nonzero : value ≠ 0 := by
                    intro equality
                    subst value
                    exact continues evaluation
                  obtain ⟨bodySource, bodyNotStuck⟩ := bodyComplete bodyExecution
                  rename_i middleState finalResult
                  cases middleState with
                  | normal middle =>
                      obtain ⟨restSource, restNotStuck⟩ := restComplete rfl rfl
                      exact ⟨.whileTrue evaluation nonzero bodySource restSource, restNotStuck⟩
                  | abrupt middle =>
                      rw [exec_from_abrupt rest]
                      exact ⟨.whileRet evaluation nonzero bodySource, by simp⟩
                  | fault label =>
                      rw [exec_from_fault rest]
                      exact ⟨.whileBodyFault evaluation nonzero bodySource, by simp⟩
                  | stuck => exact False.elim (bodyNotStuck rfl)
              | guardFault invalid =>
                  rw [exec_from_fault bodyExecution] at rest
                  rw [exec_from_fault rest]
                  have evaluation : condition.eval source = none := by
                    cases found : condition.eval source with
                    | none => rfl
                    | some value => exact False.elim (invalid ⟨value, found⟩)
                  exact ⟨.whileGuardFault evaluation, by simp⟩
      | skip => cases commandEq
      | guard => cases commandEq
      | guardFault => cases commandEq
      | faultProp => intro state inputEq; cases inputEq
      | basic => cases commandEq
      | spec => cases commandEq
      | specStuck => cases commandEq
      | seq => cases commandEq
      | condTrue => cases commandEq
      | condFalse => cases commandEq
      | «call» => cases commandEq
      | callUndefined => cases commandEq
      | stuckProp => intro state inputEq; cases inputEq
      | dynCom => cases commandEq
      | «throw» => cases commandEq
      | abruptProp => intro state inputEq; cases inputEq
      | catchMatch => cases commandEq
      | catchMiss => cases commandEq

private theorem Stmt.Exec.flags (execution : Stmt.Exec statement state outcome) :
    (∀ result, outcome = .returned result → result.returned = true) ∧
    (∀ result, outcome = .normal result → result.returned = state.returned) := by
  induction execution <;> constructor <;> intro result equality <;> cases equality <;>
    simp_all [State.returnValue, State.write, State.clear]

theorem Stmt.Exec.returned_flag (execution : Stmt.Exec statement state (.returned result)) :
    result.returned = true :=
  execution.flags.1 result rfl

theorem Stmt.Exec.normal_flag (execution : Stmt.Exec statement state (.normal result)) :
    result.returned = state.returned :=
  execution.flags.2 result rfl

theorem Stmt.Exec.deterministic
    (first : Stmt.Exec statement state firstOutcome)
    (second : Stmt.Exec statement state secondOutcome) :
    firstOutcome = secondOutcome := by
  induction first generalizing secondOutcome with
  | skip => cases second; rfl
  | seqNormal first rest firstIH restIH =>
      cases second with
      | seqNormal otherFirst otherRest =>
          cases firstIH otherFirst
          exact restIH otherRest
      | seqReturned otherFirst => cases firstIH otherFirst
      | seqFault otherFirst => cases firstIH otherFirst
  | seqReturned first firstIH =>
      cases second with
      | seqNormal otherFirst _ => cases firstIH otherFirst
      | seqReturned otherFirst => cases firstIH otherFirst; rfl
      | seqFault otherFirst => cases firstIH otherFirst
  | seqFault first firstIH =>
      cases second with
      | seqNormal otherFirst _ => cases firstIH otherFirst
      | seqReturned otherFirst => cases firstIH otherFirst
      | seqFault otherFirst => cases firstIH otherFirst; rfl
  | assign id type value evaluation =>
      cases second with
      | assign _ _ _ other => rw [evaluation] at other; cases other; rfl
      | assignFault _ _ _ other => rw [evaluation] at other; cases other
  | assignFault id type value evaluation =>
      cases second with
      | assign _ _ _ other => rw [evaluation] at other; cases other
      | assignFault => rfl
  | declare => cases second; rfl
  | init id type value evaluation =>
      cases second with
      | init _ _ _ other => rw [evaluation] at other; cases other; rfl
      | initFault _ _ _ other => rw [evaluation] at other; cases other
  | initFault id type value evaluation =>
      cases second with
      | init _ _ _ other => rw [evaluation] at other; cases other
      | initFault => rfl
  | ret evaluation =>
      cases second with
      | ret other => rw [evaluation] at other; cases other; rfl
      | retFault other => rw [evaluation] at other; cases other
  | retFault evaluation =>
      cases second with
      | ret other => rw [evaluation] at other; cases other
      | retFault => rfl
  | condTrue evaluation nonzero branch branchIH =>
      cases second with
      | condTrue otherEvaluation _ otherBranch =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact branchIH otherBranch
      | condFalse otherEvaluation _ =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (nonzero rfl).elim
      | condFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | condFalse evaluation branch branchIH =>
      cases second with
      | condTrue otherEvaluation otherNonzero _ =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (otherNonzero rfl).elim
      | condFalse otherEvaluation otherBranch =>
          rw [evaluation] at otherEvaluation
          exact branchIH otherBranch
      | condFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | condFault evaluation =>
      cases second with
      | condTrue otherEvaluation _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | condFalse otherEvaluation _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | condFault => rfl
  | whileFalse evaluation =>
      cases second with
      | whileFalse => rfl
      | whileTrue otherEvaluation otherNonzero _ _ =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (otherNonzero rfl).elim
      | whileRet otherEvaluation otherNonzero _ =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (otherNonzero rfl).elim
      | whileBodyFault otherEvaluation otherNonzero _ =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (otherNonzero rfl).elim
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileTrue evaluation nonzero iteration rest iterationIH restIH =>
      cases second with
      | whileFalse otherEvaluation =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration otherRest =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          cases iterationIH otherIteration
          exact restIH otherRest
      | whileRet otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileRet evaluation nonzero iteration iterationIH =>
      cases second with
      | whileFalse otherEvaluation =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration _ => cases iterationIH otherIteration
      | whileRet otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
  | whileBodyFault evaluation nonzero iteration iterationIH =>
      cases second with
      | whileFalse otherEvaluation =>
          rw [evaluation] at otherEvaluation
          cases otherEvaluation
          exact (nonzero rfl).elim
      | whileTrue otherEvaluation _ otherIteration _ => cases iterationIH otherIteration
      | whileRet otherEvaluation _ otherIteration => cases iterationIH otherIteration
      | whileBodyFault otherEvaluation _ otherIteration => exact iterationIH otherIteration
      | whileGuardFault otherEvaluation => rw [evaluation] at otherEvaluation
  | whileGuardFault evaluation =>
      cases second with
      | whileFalse otherEvaluation => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileTrue otherEvaluation _ _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileRet otherEvaluation _ _ => rw [evaluation] at otherEvaluation; cases otherEvaluation
      | whileBodyFault otherEvaluation _ _ => rw [evaluation] at otherEvaluation
      | whileGuardFault => rfl

structure Function where
  name : String
  returnType : ScalarType
  parameters : List (Nat × ScalarType)
  locals : List Nat
  body : Stmt
deriving Repr, DecidableEq, Inhabited

namespace Function

def finalize (function : Function) (state : State) : State :=
  if state.returned then state
  else if function.name = "main" then state.returnValue function.returnType 0 else state

def command (function : Function) : Command :=
  .Seq (.Basic State.resetReturn)
    (.Seq (.Catch (compile function.body) .Skip)
      (.Seq (.Basic function.finalize)
        (.Guard Fault.undefinedBehavior (fun state : State => state.returned) .Skip)))

def supported (function : Function) : SimplConv.Kernel.Supported function.command :=
  .seq (.basic State.resetReturn)
    (.seq (.catch (ScalarSimpl.supported function.body) .skip)
      (.seq (.basic function.finalize)
        (.guard Fault.undefinedBehavior (fun state : State => state.returned) .skip)))

inductive Exec (function : Function) : State → Simpl.XState State Fault → Prop where
  | returned (body : Stmt.Exec function.body state.resetReturn (.returned result)) :
      Exec function state (.normal result)
  | fault (body : Stmt.Exec function.body state.resetReturn .fault) :
      Exec function state (.fault .undefinedBehavior)
  | fellOff (body : Stmt.Exec function.body state.resetReturn (.normal result)) :
      Exec function state (if function.name = "main" then
        .normal (result.returnValue function.returnType 0) else .fault .undefinedBehavior)

def Corresponds (function : Function) (command : Command) : Prop :=
  ∀ state outcome, function.Exec state outcome →
    Simpl.Exec emptyEnvironment command (.normal state) outcome

theorem command_correct (function : Function) : function.Corresponds function.command := by
  intro state outcome execution
  apply Simpl.Exec.seq .basic
  cases execution with
  | returned body =>
      rename_i result
      apply Simpl.Exec.seq
      · exact .catchMatch (compile_correct _ _ _ body) .skip
      · apply Simpl.Exec.seq (middle := .normal result)
        · have flag : result.returned = true := Stmt.Exec.returned_flag body
          simpa [finalize, flag] using
            (Simpl.Exec.basic (env := emptyEnvironment) (transform := function.finalize)
              (s := result))
        · exact .guard (Stmt.Exec.returned_flag body) .skip
  | fault body =>
      apply Simpl.Exec.seq
      · apply Simpl.Exec.catchMiss (compile_correct _ _ _ body)
        simp [embedOutcome, Simpl.XState.IsAbrupt]
      · exact .faultProp
  | fellOff body =>
      apply Simpl.Exec.seq
      · apply Simpl.Exec.catchMiss (compile_correct _ _ _ body)
        simp [embedOutcome, Simpl.XState.IsAbrupt]
      · apply Simpl.Exec.seq .basic
        have flag := Stmt.Exec.normal_flag body
        simp [State.resetReturn] at flag
        by_cases isMain : function.name = "main"
        · simp [finalize, flag, isMain]
          exact .guard (by simp [State.returnValue]) .skip
        · simp [finalize, flag, isMain]
          exact .guardFault (by simp [flag])

theorem Exec.deterministic {function : Function}
    (first : function.Exec state firstOutcome)
    (second : function.Exec state secondOutcome) : firstOutcome = secondOutcome := by
  cases first with
  | returned firstBody =>
      cases second with
      | returned secondBody => cases firstBody.deterministic secondBody; rfl
      | fault secondBody => cases firstBody.deterministic secondBody
      | fellOff secondBody => cases firstBody.deterministic secondBody
  | fault firstBody =>
      cases second with
      | returned secondBody => cases firstBody.deterministic secondBody
      | fault secondBody => cases firstBody.deterministic secondBody; rfl
      | fellOff secondBody => cases firstBody.deterministic secondBody
  | fellOff firstBody =>
      cases second with
      | returned secondBody => cases firstBody.deterministic secondBody
      | fault secondBody => cases firstBody.deterministic secondBody
      | fellOff secondBody => cases firstBody.deterministic secondBody; rfl

private theorem finish_result (function : Function) (execution :
    Simpl.Exec emptyEnvironment
      (.Seq (.Basic function.finalize)
        (.Guard Fault.undefinedBehavior (fun state : State => state.returned) .Skip))
      (.normal state) result) :
    result = if (function.finalize state).returned then
      .normal (function.finalize state) else .fault .undefinedBehavior := by
  cases execution with
  | seq finalizeExecution guardExecution =>
      cases finalizeExecution
      cases guardExecution with
      | guard accepted skipExecution =>
          cases skipExecution
          simp [accepted]
      | guardFault rejected =>
          simp at rejected ⊢
          exact rejected

/-- Reverse finite correspondence for a compiled function. Divergence is not claimed. -/
theorem command_complete (function : Function) (execution :
    Simpl.Exec emptyEnvironment function.command (.normal state) result) :
    function.Exec state result := by
  simp only [command] at execution
  cases execution with
  | seq resetExecution remainderExecution =>
      cases resetExecution
      cases remainderExecution with
      | seq catchExecution finishExecution =>
          cases catchExecution with
          | catchMatch bodyExecution handlerExecution =>
              cases handlerExecution
              obtain ⟨sourceExecution, _⟩ := compile_complete function.body bodyExecution
              have flag := Stmt.Exec.returned_flag sourceExecution
              have resultEq := finish_result function finishExecution
              simp [finalize, flag] at resultEq
              rw [resultEq]
              exact Function.Exec.returned sourceExecution
          | catchMiss bodyExecution notAbrupt =>
              obtain ⟨sourceExecution, notStuck⟩ := compile_complete function.body bodyExecution
              rename_i bodyResult
              cases bodyResult with
              | normal bodyState =>
                  have flag := Stmt.Exec.normal_flag sourceExecution
                  simp [State.resetReturn] at flag
                  have resultEq := finish_result function finishExecution
                  by_cases isMain : function.name = "main"
                  · simp [finalize, flag, isMain, State.returnValue] at resultEq
                    rw [resultEq]
                    simpa [isMain, State.returnValue] using Function.Exec.fellOff sourceExecution
                  · simp [finalize, flag, isMain] at resultEq
                    rw [resultEq]
                    simpa [isMain] using Function.Exec.fellOff sourceExecution
              | abrupt bodyState => exact False.elim (notAbrupt (by simp [Simpl.XState.IsAbrupt]))
              | fault label =>
                  rw [exec_from_fault finishExecution]
                  exact Function.Exec.fault sourceExecution
              | stuck => exact False.elim (notStuck rfl)

def Equivalent (function : Function) (command : Command) : Prop :=
  function.Corresponds command ∧
    ∀ state result, Simpl.Exec emptyEnvironment command (.normal state) result →
      function.Exec state result

theorem command_equivalent (function : Function) : function.Equivalent function.command :=
  ⟨function.command_correct, fun _ _ => function.command_complete⟩

def enter (function : Function) (arguments : List Int) (base : State := {}) : Except Error State := do
  if arguments.length != function.parameters.length then
    .error (.argumentCountMismatch function.name function.parameters.length arguments.length)
  let cleared := function.locals.foldl State.clear { base with returned := false }
  .ok <| (function.parameters.zip arguments).foldl
    (fun state parameter => state.write parameter.1.1 parameter.1.2 parameter.2) cleared

end Function

private structure ResolveState where
  scopes : List (List (String × Nat))
  remainingLocals : List Nat

private abbrev ResolveM := StateT ResolveState (Except Error)

private def resolveGet : ResolveM ResolveState := fun state => .ok (state, state)

private def resolveSet (state : ResolveState) : ResolveM Unit := fun _ => .ok ((), state)

private def resolveModify (update : ResolveState → ResolveState) : ResolveM Unit := fun state =>
  .ok ((), update state)

private def resolveError (error : Error) : ResolveM α := fun _ => .error error

private def resolvePure (value : α) : ResolveM α := fun state => .ok (value, state)

private def resolveExcept : Except Error α → ResolveM α
  | .ok value => fun state => .ok (value, state)
  | .error error => resolveError error

private def lookupBinding (name : String) : List (String × Nat) → Option Nat
  | [] => none
  | (candidate, id) :: rest => if candidate = name then some id else lookupBinding name rest

private def lookupScopes (name : String) : List (List (String × Nat)) → Option Nat
  | [] => none
  | scope :: scopes => (lookupBinding name scope).orElse fun _ => lookupScopes name scopes

inductive Raw.Binding.Agrees (program : Program) : Raw.Binding → String × Nat → Prop where
  | mk {binding : Raw.Binding} {name : String} {id : Nat}
      (nameEq : binding.name = name) (idEq : binding.symbolId = id)
      (bindingEq : Raw.bindingFor? program id = some binding) :
      Raw.Binding.Agrees program binding (name, id)

inductive Raw.Scope.Agrees (program : Program) :
    List Raw.Binding → List (String × Nat) → Prop where
  | nil : Raw.Scope.Agrees program [] []
  | cons (binding : Raw.Binding.Agrees program raw resolved)
      (rest : Raw.Scope.Agrees program rawScope resolvedScope) :
      Raw.Scope.Agrees program (raw :: rawScope) (resolved :: resolvedScope)

inductive Raw.Env.Agrees (program : Program) : Raw.Env → List (List (String × Nat)) → Prop where
  | nil : Raw.Env.Agrees program [] []
  | cons (scope : Raw.Scope.Agrees program rawScope resolvedScope)
      (rest : Raw.Env.Agrees program rawScopes resolvedScopes) :
      Raw.Env.Agrees program (rawScope :: rawScopes) (resolvedScope :: resolvedScopes)

private theorem Raw.Scope.Agrees.lookup (agreement : Raw.Scope.Agrees program raw resolved) :
    Raw.Env.lookupScope name raw = (lookupBinding name resolved).bind (Raw.bindingFor? program) := by
  induction agreement with
  | nil => rfl
  | cons binding rest ih =>
      cases binding
      simp_all [Raw.Env.lookupScope, lookupBinding]
      split <;> simp_all

private theorem Raw.Scope.Agrees.bindingFor_of_lookup
    {name : String} {id : Nat} (agreement : Raw.Scope.Agrees program raw resolved)
    (found : lookupBinding name resolved = some id) :
    ∃ binding, Raw.bindingFor? program id = some binding := by
  induction agreement with
  | nil => simp [lookupBinding] at found
  | cons binding rest ih =>
      cases binding with
      | mk nameEq idEq bindingEq =>
          simp only [lookupBinding] at found
          split at found
          · cases found
            exact ⟨_, bindingEq⟩
          · exact ih found

theorem Raw.Env.Agrees.lookup (agreement : Raw.Env.Agrees program environment scopes) :
    environment.lookup name = (lookupScopes name scopes).bind (Raw.bindingFor? program) := by
  induction agreement with
  | nil => rfl
  | @cons rawScope resolvedScope rawScopes resolvedScopes scope rest ih =>
      simp only [Raw.Env.lookup, lookupScopes]
      rw [scope.lookup, ih]
      cases found : lookupBinding name resolvedScope with
      | none => simp
      | some id =>
          obtain ⟨binding, bindingEq⟩ := scope.bindingFor_of_lookup found
          simp [bindingEq, Option.orElse]

theorem Raw.Env.Agrees.push (agreement : Raw.Env.Agrees program environment scopes) :
    Raw.Env.Agrees program ([] :: environment) ([] :: scopes) :=
  .cons .nil agreement

def bindScopes (resolved : String × Nat) : List (List (String × Nat)) →
    List (List (String × Nat))
  | [] => [[resolved]]
  | scope :: scopes => (resolved :: scope) :: scopes

theorem Raw.Env.Agrees.bind (agreement : Raw.Env.Agrees program environment scopes)
    (binding : Raw.Binding.Agrees program raw resolved) :
    Raw.Env.Agrees program (environment.bind raw) (bindScopes resolved scopes) := by
  cases agreement with
  | nil => exact .cons (.cons binding .nil) .nil
  | cons scope rest => exact .cons (.cons binding scope) rest

private theorem Raw.localBinding_agrees
    (localEq : Raw.localBinding? program functionId region name rawType = some binding) :
    Raw.Binding.Agrees program binding (name, binding.symbolId) := by
  unfold Raw.localBinding? at localEq
  cases ctypeEq : Raw.scalarCType rawType with
  | none => simp [ctypeEq] at localEq
  | some ctype =>
      simp only [ctypeEq] at localEq
      cases symbolsEq : program.symbols.filter fun symbol =>
          symbol.sourceName = name && symbol.region = region && symbol.kind = .local functionId with
      | nil => simp [symbolsEq] at localEq
      | cons symbol rest =>
          cases rest with
          | cons next tail => simp [symbolsEq] at localEq
          | nil =>
              simp [symbolsEq] at localEq
              rcases localEq with ⟨typeEq, localEq⟩
              cases candidateEq : Raw.bindingFor? program symbol.id with
                | none => simp [candidateEq] at localEq
                | some candidate =>
                    simp only [candidateEq, Option.bind_some] at localEq
                    split at localEq
                    · contradiction
                    · cases localEq
                      have idEq := Raw.bindingFor_symbolId candidateEq
                      exact Raw.Binding.Agrees.mk (by simp_all) rfl (idEq ▸ candidateEq)

private def bind (name : String) (id : Nat) : ResolveM Unit := resolveModify fun state =>
  { state with scopes := bindScopes (name, id) state.scopes }

private def scalarType (target : Target) (name : String) (type : AnalyzedCType) : Except Error ScalarType :=
  match ScalarType.ofCType target type with
  | some type => .ok type
  | none => .error (.unsupportedType name type)

private def requireSome (error : Error) : Option α → Except Error α
  | some value => .ok value
  | none => .error error

private def binaryOp (region : Region) : BinOpType → Except Error BinaryOp
  | .plus => .ok .add
  | .minus => .ok .subtract
  | .times => .ok .multiply
  | .divides => .ok .divide
  | .modulus => .ok .modulus
  | .equals => .ok .equal
  | .notEquals => .ok .notEqual
  | .lt => .ok .less
  | .gt => .ok .greater
  | .leq => .ok .lessEqual
  | .geq => .ok .greaterEqual
  | _ => .error (.unsupportedExpression region "operator outside scalar arithmetic/comparison slice")

private def symbolType (program : Program) (_region : Region) (name : String) (id : Nat) :
    Except Error (AnalyzedCType × ScalarType) := do
  let symbol ← requireSome (.malformedAnalysis s!"missing symbol {id} for {name}")
    (program.symbolById? id)
  let type ← scalarType program.target name symbol.type
  return (symbol.type, type)

structure CheckedExpr (program : Program) (scopes : List (List (String × Nat)))
    (raw : CParser.Expr) where
  ctype : AnalyzedCType
  expression : Expr
  correct : ∀ environment, Raw.Env.Agrees program environment scopes → ∀ state,
    Raw.evalExpr program.target environment raw state =
      (expression.eval state).map fun value => (ctype, value)

@[simp] private theorem option_bind_pair (value : Option Int) (ctype : AnalyzedCType) :
    value.bind (fun result => some (ctype, result)) = value.map fun result => (ctype, result) := by
  cases value <;> rfl

private structure CheckedScalar (target : Target) (ctype : AnalyzedCType) where
  type : ScalarType
  valid : ScalarType.ofCType target ctype = some type

private def checkedScalar (target : Target) (name : String) (ctype : AnalyzedCType) :
    Except Error (CheckedScalar target ctype) :=
  match valid : ScalarType.ofCType target ctype with
  | some type => .ok { type, valid }
  | none => .error (.unsupportedType name ctype)

private structure CheckedBinaryOp (region : Region) (operator : BinOpType) where
  resolved : BinaryOp
  valid : binaryOp region operator = .ok resolved

private def checkedBinaryOp (region : Region) (operator : BinOpType) :
    Except Error (CheckedBinaryOp region operator) :=
  match valid : binaryOp region operator with
  | .ok resolved => .ok { resolved, valid }
  | .error error => .error error

private def checkExpr (program : Program) (scopes : List (List (String × Nat))) :
    (raw : CParser.Expr) → Except Error (CheckedExpr program scopes raw)
  | .e ⟨node, region⟩ => do
      match nodeEq : node with
      | .constant ⟨.numConst info, _⟩ =>
          match literalEq : ProgramAnalysis.numericLiteralType program.target info with
          | none => .error (.unsupportedExpression region
              "integer literal is not representable by the target")
          | some ctype => do
              let checked ← checkedScalar program.target "literal" ctype
              let type := checked.type
              return {
                ctype
                expression := .literal type info.value
                correct := by
                  intro environment agreement state
                  simp [nodeEq, Raw.evalExpr, literalEq, checked.valid, type, Expr.eval] }
      | .var name _ =>
          match scopeEq : lookupScopes name scopes with
          | none => .error (.unresolvedIdentifier region name)
          | some id =>
              match symbolEq : program.symbolById? id with
              | none => .error (.malformedAnalysis s!"missing symbol {id} for {name}")
              | some symbol =>
                  match checkedScalar program.target name symbol.type with
                  | .error error => .error error
                  | .ok checked => .ok {
                      ctype := symbol.type
                      expression := .variable checked.type id
                      correct := by
                        intro environment agreement state
                        simp only [nodeEq]
                        rw [Raw.evalExpr, agreement.lookup]
                        simp [scopeEq, Raw.bindingFor?, symbolEq, checked.valid, Expr.eval] }
      | .typeCast rawType value =>
          let value ← checkExpr program scopes value
          match rawTypeEq : rawType.value with
          | .signed kind =>
              let ctype : AnalyzedCType := .signed kind
              let checked ← checkedScalar program.target "cast" ctype
              let type := checked.type
              return {
                ctype
                expression := .cast type value.expression
                correct := by
                  intro environment agreement state
                  simp only [nodeEq]
                  rw [Raw.evalExpr, value.correct environment agreement state]
                  simp [rawTypeEq, Raw.scalarCType, checked.valid, ctype, Expr.eval]
                  cases value.expression.eval state <;> rfl }
          | .unsigned kind =>
              let ctype : AnalyzedCType := .unsigned kind
              let checked ← checkedScalar program.target "cast" ctype
              let type := checked.type
              return {
                ctype
                expression := .cast type value.expression
                correct := by
                  intro environment agreement state
                  simp only [nodeEq]
                  rw [Raw.evalExpr, value.correct environment agreement state]
                  simp [rawTypeEq, Raw.scalarCType, checked.valid, ctype, Expr.eval]
                  cases value.expression.eval state <;> rfl }
          | _ => .error (.unsupportedExpression region "non-integer cast")
      | .unOp .negate value =>
          let value ← checkExpr program scopes value
          let promoted := value.ctype.integerPromotions program.target
          let checked ← checkedScalar program.target "unary -" promoted
          let type := checked.type
          return {
            ctype := promoted
            expression := .unary type .negate value.expression
            correct := by
              intro environment agreement state
              simp only [nodeEq]
              rw [Raw.evalExpr, value.correct environment agreement state]
              generalize evalEq : value.expression.eval state = evaluated
              have typeEq : ScalarType.ofCType program.target promoted = some type := by
                simpa [promoted, type] using checked.valid
              cases evaluated with
              | none => simp [evalEq, Expr.eval]
              | some result =>
                  simp [evalEq, promoted, type, Expr.eval]
                  rw [typeEq]
                  simp [type, Raw.checked, Expr.checked] }
      | .unOp .not value =>
          let value ← checkExpr program scopes value
          let ctype : AnalyzedCType := .signed .int
          let checked ← checkedScalar program.target "logical not" ctype
          let type := checked.type
          return {
            ctype
            expression := .unary type .logicalNot value.expression
            correct := by
              intro environment agreement state
              simp only [nodeEq]
              rw [Raw.evalExpr, value.correct environment agreement state]
              simp [ctype, Expr.eval]
              cases value.expression.eval state <;> rfl }
      | .binOp operator left right =>
          let left ← checkExpr program scopes left
          let right ← checkExpr program scopes right
          match conversionEq : CType.arithmeticConversion program.target left.ctype right.ctype with
          | .error error => .error (.unsupportedExpression region (reprStr error))
          | .ok operandCType => do
              let operandChecked ← checkedScalar program.target "operand" operandCType
              let operandType := operandChecked.type
              let operatorChecked ← checkedBinaryOp region operator
              let relational := Raw.isRelational operator
              let resultCType := if relational then .signed .int else operandCType
              let resultType := if relational then
                { signedness := .signed, width := program.target.intWidth } else operandType
              return {
                ctype := resultCType
                expression := .binary resultType operandType operatorChecked.resolved
                  left.expression right.expression
                correct := by
                  intro environment agreement state
                  simp only [nodeEq]
                  rw [Raw.evalExpr, left.correct environment agreement state,
                    right.correct environment agreement state]
                  generalize leftEq : left.expression.eval state = leftResult
                  generalize rightEq : right.expression.eval state = rightResult
                  have operandTypeEq : ScalarType.ofCType program.target operandCType =
                      some operandType := by simpa [operandType] using operandChecked.valid
                  have operatorEq := operatorChecked.valid
                  cases operator <;>
                    simp [binaryOp] at operatorEq <;>
                    cases leftResult <;> cases rightResult
                  all_goals simp [leftEq, rightEq, Except.toOption, conversionEq, operandTypeEq,
                    ← operatorEq, resultCType, resultType, relational,
                    Raw.isRelational, Raw.checked, Expr.checked, Raw.truncDiv, Raw.truncMod,
                    Expr.truncDiv, Expr.truncMod, Expr.eval]
                  all_goals
                    split
                    · simp_all
                    · split <;> simp_all }
      | .mkBool value =>
          let value ← checkExpr program scopes value
          let ctype : AnalyzedCType := .signed .int
          let checked ← checkedScalar program.target "boolean conversion" ctype
          let type := checked.type
          return {
            ctype
            expression := .unary type .logicalNot (.unary type .logicalNot value.expression)
            correct := by
              intro environment agreement state
              simp only [nodeEq]
              rw [Raw.evalExpr, value.correct environment agreement state]
              generalize evalEq : value.expression.eval state = evaluated
              cases evaluated with
              | none => simp [evalEq, ctype, Expr.eval]
              | some result =>
                  by_cases zero : result = 0 <;> simp [evalEq, ctype, Expr.eval, zero] }
      | _ => .error (.unsupportedExpression region "expression outside direct scalar slice")
termination_by raw => sizeOf raw
decreasing_by all_goals simp_wf <;> decreasing_trivial

private def lowerExprRuntime (program : Program) (scopes : List (List (String × Nat))) :
    CParser.Expr → Except Error (AnalyzedCType × Expr)
  | .e ⟨node, region⟩ => do
      match node with
      | .constant ⟨.numConst info, _⟩ =>
          let ctype ← requireSome (.unsupportedExpression region
            "integer literal is not representable by the target")
            (ProgramAnalysis.numericLiteralType program.target info)
          return (ctype, .literal (← scalarType program.target "literal" ctype) info.value)
      | .var name _ =>
          let id ← requireSome (.unresolvedIdentifier region name) (lookupScopes name scopes)
          let (ctype, type) ← symbolType program region name id
          return (ctype, .variable type id)
      | .typeCast rawType value =>
          let (_, value) ← lowerExprRuntime program scopes value
          let ctype ← match rawType.value with
            | .signed kind => .ok (CType.signed kind)
            | .unsigned kind => .ok (CType.unsigned kind)
            | _ => .error (.unsupportedExpression region "non-integer cast")
          return (ctype, .cast (← scalarType program.target "cast" ctype) value)
      | .unOp .negate value =>
          let (ctype, value) ← lowerExprRuntime program scopes value
          let promoted := ctype.integerPromotions program.target
          return (promoted, .unary (← scalarType program.target "unary -" promoted) .negate value)
      | .unOp .not value =>
          let (_, value) ← lowerExprRuntime program scopes value
          let ctype : AnalyzedCType := .signed .int
          return (ctype, .unary (← scalarType program.target "logical not" ctype) .logicalNot value)
      | .binOp operator left right =>
          let (leftType, left) ← lowerExprRuntime program scopes left
          let (rightType, right) ← lowerExprRuntime program scopes right
          let operandType ← (CType.arithmeticConversion program.target leftType rightType).mapError
            fun error => .unsupportedExpression region (reprStr error)
          let resolvedOperator ← binaryOp region operator
          let relational := Raw.isRelational operator
          let resultType := if relational then .signed .int else operandType
          return (resultType, .binary (← scalarType program.target "result" resultType)
            (← scalarType program.target "operand" operandType) resolvedOperator left right)
      | .mkBool value =>
          let (_, value) ← lowerExprRuntime program scopes value
          let ctype : AnalyzedCType := .signed .int
          return (ctype, .unary (← scalarType program.target "boolean conversion" ctype)
            .logicalNot (.unary (← scalarType program.target "boolean conversion" ctype)
              .logicalNot value))
      | _ => .error (.unsupportedExpression region "expression outside direct scalar slice")

@[implemented_by lowerExprRuntime]
private noncomputable def lowerExpr (program : Program) (scopes : List (List (String × Nat)))
    (raw : CParser.Expr) : Except Error (AnalyzedCType × Expr) := do
  let checked ← checkExpr program scopes raw
  return (checked.ctype, checked.expression)

private def resolveExpr (program : Program) (raw : CParser.Expr) :
    ResolveM (AnalyzedCType × Expr) := do
  let state ← resolveGet
  resolveExcept (lowerExpr program state.scopes raw)

private theorem lowerExpr_eval (raw : CParser.Expr)
    (agreement : Raw.Env.Agrees program environment scopes)
    (resolved : lowerExpr program scopes raw = .ok (ctype, expression)) :
    ∀ state, Raw.evalExpr program.target environment raw state =
      (expression.eval state).map fun value => (ctype, value) := by
  cases checkedEq : checkExpr program scopes raw with
  | error error =>
      unfold lowerExpr at resolved
      rw [checkedEq] at resolved
      cases resolved
  | ok checked =>
      unfold lowerExpr at resolved
      rw [checkedEq] at resolved
      change Except.ok (checked.ctype, checked.expression) = .ok (ctype, expression) at resolved
      rcases resolved with ⟨rfl, rfl⟩
      exact checked.correct environment agreement

def Raw.embedStatementOutcome : Raw.Outcome → ScalarSimpl.Outcome
  | .normal state => ScalarSimpl.Outcome.normal state
  | .returned state => ScalarSimpl.Outcome.returned state
  | .undefinedBehavior => ScalarSimpl.Outcome.fault

theorem Raw.embedStatementOutcome_injective : Function.Injective Raw.embedStatementOutcome := by
  intro left right
  cases left <;> cases right <;> simp_all [Raw.embedStatementOutcome]

private theorem Raw.normal_eq_of_embed (equality : ScalarSimpl.Outcome.normal state =
    Raw.embedStatementOutcome outcome) : Raw.Outcome.normal state = outcome :=
  Raw.embedStatementOutcome_injective (by
    change ScalarSimpl.Outcome.normal state = Raw.embedStatementOutcome outcome
    exact equality)

private theorem Raw.returned_eq_of_embed (equality : ScalarSimpl.Outcome.returned state =
    Raw.embedStatementOutcome outcome) : Raw.Outcome.returned state = outcome :=
  Raw.embedStatementOutcome_injective (by
    change ScalarSimpl.Outcome.returned state = Raw.embedStatementOutcome outcome
    exact equality)

private theorem Raw.fault_eq_of_embed (equality : ScalarSimpl.Outcome.fault =
    Raw.embedStatementOutcome outcome) : Raw.Outcome.undefinedBehavior = outcome :=
  Raw.embedStatementOutcome_injective (by
    change ScalarSimpl.Outcome.fault = Raw.embedStatementOutcome outcome
    exact equality)

private theorem option_map_pair_some (values : Option Int) (expected actual : AnalyzedCType)
    (result : Int) (equality : values.map (fun value => (expected, value)) = some (actual, result)) :
    values = some result := by
  cases values <;> simp_all

private theorem option_map_pair_none (values : Option Int) (expected : AnalyzedCType)
    (equality : values.map (fun value => (expected, value)) = none) : values = none := by
  cases values <;> simp_all

mutual
  /-- Proof-producing resolution of one exact raw statement under exact lexical bindings. -/
  inductive CheckedStatement (program : Program) (functionId : Nat) (returnType : ScalarType) :
      Statement → List (List (String × Nat)) → Stmt → Prop where
    | assign
        (binding : Raw.Binding)
        (bound : ∀ environment, Raw.Env.Agrees program environment scopes →
          environment.lookup name = some binding)
        (value : CheckedExpr program scopes rawValue) :
        CheckedStatement program functionId returnType
          (.stmt ⟨.assign (.e ⟨.var name info, leftRegion⟩) rawValue, region⟩) scopes
          (.assign binding.symbolId binding.type value.expression)
    | block (body : CheckedBody program functionId returnType items ([] :: scopes) resolved) :
        CheckedStatement program functionId returnType (.stmt ⟨.block items, region⟩) scopes
          (.seq resolved .skip)
    | trap (body : CheckedStatement program functionId returnType raw scopes resolved) :
        CheckedStatement program functionId returnType (.stmt ⟨.trap kind raw, region⟩) scopes
          (.seq resolved .skip)
    | ret (value : CheckedExpr program scopes rawValue) :
        CheckedStatement program functionId returnType
          (.stmt ⟨.returnStmt (some rawValue), region⟩) scopes (.return returnType value.expression)
    | cond (condition : CheckedExpr program scopes rawCondition)
        (thenBranch : CheckedStatement program functionId returnType rawThen scopes resolvedThen)
        (elseBranch : CheckedStatement program functionId returnType rawElse scopes resolvedElse) :
        CheckedStatement program functionId returnType
          (.stmt ⟨.ifStmt rawCondition rawThen rawElse, region⟩) scopes
          (.cond condition.expression resolvedThen resolvedElse)
    | while (condition : CheckedExpr program scopes rawCondition)
        (body : CheckedStatement program functionId returnType rawBody scopes resolvedBody) :
        CheckedStatement program functionId returnType
          (.stmt ⟨.whileStmt rawCondition invariant rawBody, region⟩) scopes
          (.while condition.expression resolvedBody)
    | empty : CheckedStatement program functionId returnType
        (.stmt ⟨.emptyStmt, region⟩) scopes .skip

  /-- Proof-producing resolution of exact block items, including each lexical extension. -/
  inductive CheckedBody (program : Program) (functionId : Nat) (returnType : ScalarType) :
      List BlockItem → List (List (String × Nat)) → Stmt → Prop where
    | nil : CheckedBody program functionId returnType [] scopes .skip
    | statement
        (first : CheckedStatement program functionId returnType raw scopes resolved)
        (rest : CheckedBody program functionId returnType items scopes resolvedRest) :
        CheckedBody program functionId returnType (.statement raw :: items) scopes
          (.seq resolved resolvedRest)
    | declaration
        (binding : Raw.Binding)
        (localEq : Raw.localBinding? program functionId declarationRegion name.value rawType = some binding)
        (valid : Raw.Binding.Agrees program binding (name.value, binding.symbolId))
        (rest : CheckedBody program functionId returnType items
          (bindScopes (name.value, binding.symbolId) scopes) resolvedRest) :
        CheckedBody program functionId returnType
          (.declaration ⟨.varDecl rawType name [] none attributes, declarationRegion⟩ :: items)
          scopes (.seq (.declare binding.symbolId binding.type none) resolvedRest)
    | init
        (binding : Raw.Binding)
        (localEq : Raw.localBinding? program functionId declarationRegion name.value rawType = some binding)
        (valid : Raw.Binding.Agrees program binding (name.value, binding.symbolId))
        (value : CheckedExpr program
          (bindScopes (name.value, binding.symbolId) scopes) rawValue)
        (rest : CheckedBody program functionId returnType items
          (bindScopes (name.value, binding.symbolId) scopes) resolvedRest) :
        CheckedBody program functionId returnType
          (.declaration ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes,
            declarationRegion⟩ :: items) scopes
          (.seq (.declare binding.symbolId binding.type (some value.expression)) resolvedRest)
end

private theorem Stmt.Exec.thenSkip (execution : Stmt.Exec statement state outcome) :
    Stmt.Exec (.seq statement .skip) state outcome := by
  cases outcome with
  | normal result => exact .seqNormal execution .skip
  | returned result => exact .seqReturned execution
  | fault => exact .seqFault execution

theorem CheckedBody.rawToResolved
    (checked : CheckedBody program functionId returnType raw scopes resolved)
    (agreement : Raw.Env.Agrees program environment scopes)
    (execution : Raw.BodyExec program functionId returnType raw environment state outcome) :
    Stmt.Exec resolved state (Raw.embedStatementOutcome outcome) := by
  refine (Raw.BodyExec.rec (program := program) (functionId := functionId)
    (returnType := returnType)
    (motive_1 := fun raw environment state outcome _ =>
      ∀ {scopes resolved}, CheckedStatement program functionId returnType raw scopes resolved →
        Raw.Env.Agrees program environment scopes →
        Stmt.Exec resolved state (Raw.embedStatementOutcome outcome))
    (motive_2 := fun raw environment state outcome _ =>
      ∀ {scopes resolved}, CheckedBody program functionId returnType raw scopes resolved →
        Raw.Env.Agrees program environment scopes →
        Stmt.Exec resolved state (Raw.embedStatementOutcome outcome))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    execution) checked agreement
  case refine_1 =>
        intro binding environment value state ctype result name info leftRegion region
          bound evaluation scopes resolved checked agreement
        cases checked with
        | assign binding resolvedBound value =>
            rw [resolvedBound _ agreement] at bound
            have same := Option.some.inj bound
            cases same
            apply Stmt.Exec.assign
            rw [value.correct environment agreement] at evaluation
            exact option_map_pair_some _ _ _ _ evaluation
  case refine_2 =>
        intro binding environment value state name info leftRegion region
          bound evaluation scopes resolved checked agreement
        cases checked with
        | assign binding resolvedBound value =>
            rw [resolvedBound _ agreement] at bound
            have same := Option.some.inj bound
            cases same
            apply Stmt.Exec.assignFault
            rw [value.correct environment agreement] at evaluation
            exact option_map_pair_none _ _ evaluation
  case refine_3 =>
        intro items environment state outcome region execution executionIH
          scopes resolved checked agreement
        cases checked with
        | block body =>
            exact (executionIH body agreement.push).thenSkip
  case refine_4 =>
        intro body environment state outcome kind region execution executionIH
          scopes resolved checked agreement
        cases checked with
        | trap body => exact (executionIH body agreement).thenSkip
  case refine_5 =>
        intro environment value state ctype result region evaluation scopes resolved checked agreement
        cases checked with
        | ret value =>
            apply Stmt.Exec.ret
            rw [value.correct environment agreement] at evaluation
            exact option_map_pair_some _ _ _ _ evaluation
  case refine_6 =>
        intro environment value state region evaluation scopes resolved checked agreement
        cases checked with
        | ret value =>
            apply Stmt.Exec.retFault
            rw [value.correct environment agreement] at evaluation
            exact option_map_pair_none _ _ evaluation
  case refine_7 =>
        intro environment condition state ctype value thenBranch outcome elseBranch region
          evaluation nonzero branch branchIH scopes resolved checked agreement
        cases checked with
        | cond condition thenBranch elseBranch =>
            apply Stmt.Exec.condTrue (value := _)
            · rw [condition.correct environment agreement] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact nonzero
            · exact branchIH thenBranch agreement
  case refine_8 =>
        intro environment condition state ctype elseBranch outcome thenBranch region
          evaluation branch branchIH scopes resolved checked agreement
        cases checked with
        | cond condition thenBranch elseBranch =>
            apply Stmt.Exec.condFalse
            · rw [condition.correct environment agreement] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact branchIH elseBranch agreement
  case refine_9 =>
        intro environment condition state thenBranch elseBranch region
          evaluation scopes resolved checked agreement
        cases checked with
        | cond condition thenBranch elseBranch =>
            apply Stmt.Exec.condFault
            rw [condition.correct environment agreement] at evaluation
            exact option_map_pair_none _ _ evaluation
  case refine_10 =>
        intro environment condition state ctype invariant body region
          evaluation scopes resolved checked agreement
        cases checked with
        | «while» condition body =>
            apply Stmt.Exec.whileFalse
            rw [condition.correct environment agreement] at evaluation
            exact option_map_pair_some _ _ _ _ evaluation
  case refine_11 =>
        intro environment condition state ctype value body middle invariant region outcome
          evaluation nonzero iteration rest iterationIH restIH scopes resolved checked agreement
        cases checked with
        | «while» condition body =>
            apply Stmt.Exec.whileTrue (value := _)
            · rw [condition.correct environment agreement] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact nonzero
            · exact iterationIH body agreement
            · exact restIH (CheckedStatement.while condition body) agreement
  case refine_12 =>
        intro environment condition state ctype value body result invariant region
          evaluation nonzero iteration iterationIH scopes resolved checked agreement
        cases checked with
        | «while» condition body =>
            apply Stmt.Exec.whileRet (value := _)
            · rw [condition.correct environment agreement] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact nonzero
            · exact iterationIH body agreement
  case refine_13 =>
        intro environment condition state ctype value body invariant region
          evaluation nonzero iteration iterationIH scopes resolved checked agreement
        cases checked with
        | «while» condition body =>
            apply Stmt.Exec.whileBodyFault (value := _)
            · rw [condition.correct environment agreement] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact nonzero
            · exact iterationIH body agreement
  case refine_14 =>
        intro environment condition state invariant body region
          evaluation scopes resolved checked agreement
        cases checked with
        | «while» condition body =>
            apply Stmt.Exec.whileGuardFault
            rw [condition.correct environment agreement] at evaluation
            exact option_map_pair_none _ _ evaluation
  case refine_15 =>
        intro region environment state scopes resolved checked agreement
        cases checked
        exact Stmt.Exec.skip
  case refine_16 =>
        intro environment state scopes resolved checked agreement
        cases checked
        exact Stmt.Exec.skip
  case refine_17 =>
        intro statement environment state middle items outcome first rest firstIH restIH
          scopes resolved checked agreement
        cases checked with
        | statement firstChecked restChecked =>
            exact Stmt.Exec.seqNormal (firstIH firstChecked agreement)
              (restIH restChecked agreement)
  case refine_18 =>
        intro statement environment state result items first firstIH scopes resolved checked agreement
        cases checked with
        | statement firstChecked restChecked =>
            exact Stmt.Exec.seqReturned (firstIH firstChecked agreement)
  case refine_19 =>
        intro statement environment state items first firstIH scopes resolved checked agreement
        cases checked with
        | statement firstChecked restChecked =>
            exact Stmt.Exec.seqFault (firstIH firstChecked agreement)
  case refine_20 =>
        intro declarationRegion rawType binding items outcome name attributes environment state
          bindingEq rest restIH scopes resolved checked agreement
        cases checked with
        | declaration binding localEq valid restChecked =>
            rw [localEq] at bindingEq
            have same := Option.some.inj bindingEq
            cases same
            apply Stmt.Exec.seqNormal (middle := state.clear binding.symbolId)
            · exact Stmt.Exec.declare _ _
            · exact restIH restChecked (agreement.bind valid)
  case refine_21 =>
        intro declarationRegion rawType binding value ctype result items outcome name attributes
          environment state bindingEq evaluation rest restIH scopes resolved checked agreement
        cases checked with
        | init binding localEq valid value restChecked =>
            rw [localEq] at bindingEq
            have same := Option.some.inj bindingEq
            cases same
            apply Stmt.Exec.seqNormal
            · apply Stmt.Exec.init
              rw [value.correct _ (agreement.bind valid)] at evaluation
              exact option_map_pair_some _ _ _ _ evaluation
            · exact restIH restChecked (agreement.bind valid)
  case refine_22 =>
        intro declarationRegion rawType binding value name attributes items environment state
          bindingEq evaluation scopes resolved checked agreement
        cases checked with
        | init binding localEq valid value restChecked =>
            rw [localEq] at bindingEq
            have same := Option.some.inj bindingEq
            cases same
            apply Stmt.Exec.seqFault
            apply Stmt.Exec.initFault
            rw [value.correct _ (agreement.bind valid)] at evaluation
            exact option_map_pair_none _ _ evaluation

theorem CheckedStatement.rawToResolved
    (checked : CheckedStatement program functionId returnType raw scopes resolved)
    (agreement : Raw.Env.Agrees program environment scopes)
    (execution : Raw.StatementExec program functionId returnType raw environment state outcome) :
    Stmt.Exec resolved state (Raw.embedStatementOutcome outcome) := by
  let bodyChecked : CheckedBody program functionId returnType [.statement raw] scopes
      (.seq resolved .skip) := .statement checked .nil
  have bodyExecution : Raw.BodyExec program functionId returnType [.statement raw] environment state outcome :=
    match outcome with
    | .normal result => .statementNormal execution .nil
    | .returned result => .statementReturned execution
    | .undefinedBehavior => .statementFault execution
  have combined := bodyChecked.rawToResolved agreement bodyExecution
  cases outcome with
  | normal result =>
      cases combined with
      | seqNormal first rest => cases rest; exact first
  | returned result =>
      cases combined with
      | seqNormal first rest => cases rest
      | seqReturned first => exact first
  | undefinedBehavior =>
      cases combined with
      | seqNormal first rest => cases rest
      | seqFault first => exact first

inductive ReverseRequest (program : Program) (functionId : Nat) (returnType : ScalarType) :
    Stmt → Type where
  | statement (raw : Statement) (scopes : List (List (String × Nat))) (environment : Raw.Env)
      (checked : CheckedStatement program functionId returnType raw scopes resolved)
      (agreement : Raw.Env.Agrees program environment scopes) : ReverseRequest program functionId returnType resolved
  | body (raw : List BlockItem) (scopes : List (List (String × Nat))) (environment : Raw.Env)
      (checked : CheckedBody program functionId returnType raw scopes resolved)
      (agreement : Raw.Env.Agrees program environment scopes) : ReverseRequest program functionId returnType resolved

def ReverseResult (state : State) (result : Outcome) :
    ReverseRequest program functionId returnType resolved → Prop
  | .statement raw _ environment _ _ => ∃ outcome, result = Raw.embedStatementOutcome outcome ∧
      Raw.StatementExec program functionId returnType raw environment state outcome
  | .body raw _ environment _ _ => ∃ outcome, result = Raw.embedStatementOutcome outcome ∧
      Raw.BodyExec program functionId returnType raw environment state outcome

theorem reverseChecked (request : ReverseRequest program functionId returnType resolved)
    (execution : Stmt.Exec resolved state result) : ReverseResult state result request := by
  induction execution with
  | skip =>
      cases request with
      | statement _ _ _ checked _ => cases checked; exact ⟨.normal _, rfl, .empty⟩
      | body _ _ _ checked _ => cases checked; exact ⟨.normal _, rfl, .nil⟩
  | assign id type expression evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | assign binding bound value =>
              refine ⟨.normal _, rfl, .assign (ctype := value.ctype) (bound _ agreement) ?_⟩
              rw [value.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | assignFault id type expression evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | assign binding bound value =>
              refine ⟨.undefinedBehavior, rfl, .assignFault (bound _ agreement) ?_⟩
              rw [value.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | declare id type => cases request <;> rename_i checked agreement <;> cases checked
  | init id type expression evaluation => cases request <;> rename_i checked agreement <;> cases checked
  | initFault id type expression evaluation => cases request <;> rename_i checked agreement <;> cases checked
  | ret evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | ret value =>
              refine ⟨.returned _, rfl, .ret (ctype := value.ctype) ?_⟩
              rw [value.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | retFault evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | ret value =>
              refine ⟨.undefinedBehavior, rfl, .retFault ?_⟩
              rw [value.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | seqNormal firstExecution restExecution firstIH restIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | block body =>
              cases restExecution
              obtain ⟨outcome, equality, raw⟩ :=
                firstIH (.body _ _ ([] :: environment) body agreement.push)
              exact ⟨outcome, equality, .block raw⟩
          | trap body =>
              cases restExecution
              obtain ⟨outcome, equality, raw⟩ := firstIH (.statement _ _ environment body agreement)
              exact ⟨outcome, equality, .trap raw⟩
      | body _ _ environment checked agreement =>
          cases checked with
          | statement first rest =>
              obtain ⟨firstOutcome, firstEq, rawFirst⟩ :=
                firstIH (.statement _ _ environment first agreement)
              cases Raw.normal_eq_of_embed firstEq
              obtain ⟨outcome, equality, rawRest⟩ := restIH (.body _ _ environment rest agreement)
              exact ⟨outcome, equality, .statementNormal rawFirst rawRest⟩
          | declaration binding localEq valid rest =>
              cases firstExecution
              obtain ⟨outcome, equality, rawRest⟩ :=
                restIH (.body _ _ (environment.bind binding) rest (agreement.bind valid))
              exact ⟨outcome, equality, .declaration localEq rawRest⟩
          | init binding localEq valid value rest =>
              cases firstExecution with
              | init evaluation =>
                  obtain ⟨outcome, equality, rawRest⟩ := restIH
                    (.body _ _ (environment.bind binding) rest (agreement.bind valid))
                  refine ⟨outcome, equality, .init localEq (ctype := value.ctype) ?_ rawRest⟩
                  rw [value.correct _ (agreement.bind valid)]
                  simp_all
  | seqReturned firstExecution firstIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | block body =>
              obtain ⟨outcome, equality, raw⟩ :=
                firstIH (.body _ _ ([] :: environment) body agreement.push)
              exact ⟨outcome, equality, .block raw⟩
          | trap body =>
              obtain ⟨outcome, equality, raw⟩ := firstIH (.statement _ _ environment body agreement)
              exact ⟨outcome, equality, .trap raw⟩
      | body _ _ environment checked agreement =>
          cases checked with
          | statement first rest =>
              obtain ⟨outcome, equality, rawFirst⟩ := firstIH (.statement _ _ environment first agreement)
              cases Raw.returned_eq_of_embed equality
              exact ⟨.returned _, rfl, .statementReturned rawFirst⟩
          | declaration binding _ _ _ => cases firstExecution
          | init binding _ _ _ _ => cases firstExecution
  | seqFault firstExecution firstIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | block body =>
              obtain ⟨outcome, equality, raw⟩ :=
                firstIH (.body _ _ ([] :: environment) body agreement.push)
              exact ⟨outcome, equality, .block raw⟩
          | trap body =>
              obtain ⟨outcome, equality, raw⟩ := firstIH (.statement _ _ environment body agreement)
              exact ⟨outcome, equality, .trap raw⟩
      | body _ _ environment checked agreement =>
          cases checked with
          | statement first rest =>
              obtain ⟨outcome, equality, rawFirst⟩ := firstIH (.statement _ _ environment first agreement)
              cases Raw.fault_eq_of_embed equality
              exact ⟨.undefinedBehavior, rfl, .statementFault rawFirst⟩
          | declaration binding _ _ _ => cases firstExecution
          | init binding localEq valid value rest =>
              cases firstExecution with
              | initFault evaluation =>
                  refine ⟨.undefinedBehavior, rfl, .initFault localEq ?_⟩
                  rw [value.correct _ (agreement.bind valid)]
                  simp_all
  | condTrue evaluation nonzero branch branchIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | cond condition thenBranch elseBranch =>
              obtain ⟨outcome, equality, raw⟩ := branchIH (.statement _ _ environment thenBranch agreement)
              refine ⟨outcome, equality, .condTrue (ctype := condition.ctype) ?_ nonzero raw⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | condFalse evaluation branch branchIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | cond condition thenBranch elseBranch =>
              obtain ⟨outcome, equality, raw⟩ := branchIH (.statement _ _ environment elseBranch agreement)
              refine ⟨outcome, equality, .condFalse (ctype := condition.ctype) ?_ raw⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | condFault evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | cond condition _ _ =>
              refine ⟨.undefinedBehavior, rfl, .condFault ?_⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | whileFalse evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | «while» condition body =>
              refine ⟨.normal _, rfl, .whileFalse (ctype := condition.ctype) ?_⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | whileTrue evaluation nonzero iteration rest iterationIH restIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | «while» condition body =>
              obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ :=
                iterationIH (.statement _ _ environment body agreement)
              cases Raw.normal_eq_of_embed iterationEq
              obtain ⟨outcome, equality, rawRest⟩ :=
                restIH (.statement _ _ environment (CheckedStatement.while condition body) agreement)
              refine ⟨outcome, equality, .whileTrue (ctype := condition.ctype) ?_ nonzero rawIteration rawRest⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | whileRet evaluation nonzero iteration iterationIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | «while» condition body =>
              obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ :=
                iterationIH (.statement _ _ environment body agreement)
              cases Raw.returned_eq_of_embed iterationEq
              refine ⟨.returned _, rfl, .whileRet (ctype := condition.ctype) ?_ nonzero rawIteration⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | whileBodyFault evaluation nonzero iteration iterationIH =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | «while» condition body =>
              obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ :=
                iterationIH (.statement _ _ environment body agreement)
              cases Raw.fault_eq_of_embed iterationEq
              refine ⟨.undefinedBehavior, rfl, .whileBodyFault (ctype := condition.ctype) ?_ nonzero rawIteration⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked
  | whileGuardFault evaluation =>
      cases request with
      | statement _ _ environment checked agreement =>
          cases checked with
          | «while» condition body =>
              refine ⟨.undefinedBehavior, rfl, .whileGuardFault ?_⟩
              rw [condition.correct environment agreement]
              simp [evaluation]
      | body _ _ _ checked _ => cases checked

theorem CheckedStatement.resolvedToRaw
    (checked : CheckedStatement program functionId returnType raw scopes resolved)
    (agreement : Raw.Env.Agrees program environment scopes)
    (execution : Stmt.Exec resolved state result) :
    ∃ outcome, result = Raw.embedStatementOutcome outcome ∧
      Raw.StatementExec program functionId returnType raw environment state outcome :=
  reverseChecked (.statement raw scopes environment checked agreement) execution

theorem CheckedBody.resolvedToRaw
    (checked : CheckedBody program functionId returnType raw scopes resolved)
    (agreement : Raw.Env.Agrees program environment scopes)
    (execution : Stmt.Exec resolved state result) :
    ∃ outcome, result = Raw.embedStatementOutcome outcome ∧
      Raw.BodyExec program functionId returnType raw environment state outcome :=
  reverseChecked (.body raw scopes environment checked agreement) execution

private def nextLocal (program : Program) (functionId : Nat) (region : Region)
    (name : String) (rawType : CType CParser.Expr) : ResolveM (Nat × ScalarType) := do
  let state ← resolveGet
  let id ← requireSome (.malformedAnalysis s!"missing analyzed local {name}")
    state.remainingLocals.head?
  let binding ← requireSome (.malformedAnalysis s!"invalid analyzed local {name}")
    (Raw.localBinding? program functionId region name rawType)
  if binding.symbolId != id then
    resolveError (.malformedAnalysis s!"expected analyzed local id {id}, found {binding.symbolId}")
  resolveSet { state with remainingLocals := state.remainingLocals.drop 1 }
  resolvePure (id, binding.type)

mutual
  private def resolveStatement (program : Program) (functionId : Nat) (returnType : ScalarType) :
      Statement → ResolveM Stmt
    | .stmt ⟨node, region⟩ =>
        match node with
        | .assign (.e ⟨.var name _, leftRegion⟩) value => do
            let id ← requireSome (.unresolvedIdentifier leftRegion name)
              (lookupScopes name (← resolveGet).scopes)
            let (_, type) ← symbolType program leftRegion name id
            let (_, value) ← resolveExpr program value
            resolvePure (Stmt.assign id type value)
        | .block items => fun outer => do
            let (result, inner) ← resolveBody program functionId returnType items
              { outer with scopes := [] :: outer.scopes }
            .ok (.seq result .skip, { inner with scopes := outer.scopes })
        | .trap _ body => do
            let body ← resolveStatement program functionId returnType body
            resolvePure (.seq body .skip)
        | .returnStmt (some value) => do
            let (_, value) ← resolveExpr program value
            resolvePure (Stmt.return returnType value)
        | .ifStmt condition thenBranch elseBranch => do
            let (_, condition) ← resolveExpr program condition
            let thenBranch ← resolveStatement program functionId returnType thenBranch
            let elseBranch ← resolveStatement program functionId returnType elseBranch
            resolvePure (Stmt.cond condition thenBranch elseBranch)
        | .whileStmt condition _ body => do
            let (_, condition) ← resolveExpr program condition
            let body ← resolveStatement program functionId returnType body
            resolvePure (Stmt.while condition body)
        | .emptyStmt => resolvePure Stmt.skip
        | .break | .continue =>
            resolveError (.unsupportedStatement region "explicit break/continue")
        | _ => resolveError (.unsupportedStatement region "statement outside direct scalar slice")

  private def resolveBody (program : Program) (functionId : Nat) (returnType : ScalarType) :
      List BlockItem → ResolveM Stmt
    | [] => resolvePure Stmt.skip
    | item :: rest => do
        let statement ← match item with
          | .statement statement => resolveStatement program functionId returnType statement
          | .declaration declaration =>
              match declaration.value with
              | .varDecl rawType name storage initializer _ => do
                  if !storage.isEmpty then
                    resolveError (.unsupportedStatement declaration.region
                      "local storage classes are outside the scalar slice")
                  let (id, type) ← nextLocal program functionId declaration.region name.value rawType
                  bind name.value id
                  let initializer ← (match initializer with
                    | none => resolvePure none
                    | some (.initE value) => do
                        let (_, value) ← resolveExpr program value
                        resolvePure (some value)
                    | some (.initList _) => resolveError (.unsupportedStatement declaration.region
                        "initializer lists are outside the scalar slice") : ResolveM (Option Expr))
                  resolvePure (Stmt.declare id type initializer)
              | _ => resolveError (.unsupportedStatement declaration.region
                  "non-object local declaration")
        let rest ← resolveBody program functionId returnType rest
        resolvePure (Stmt.seq statement rest)
end

private structure CheckedParameters (program : Program) (functionId : Nat)
    (raw : List Nat) where
  bindings : List Raw.Binding
  scope : List (String × Nat)
  parameters : List (Nat × ScalarType)
  bindings_eq : Raw.parameterBindings? program functionId raw = some bindings
  evidence : Raw.Scope.Agrees program bindings scope

private def checkParameters (program : Program) (functionId : Nat) :
    (raw : List Nat) → Except Error (CheckedParameters program functionId raw)
  | [] => .ok {
      bindings := []
      scope := []
      parameters := []
      bindings_eq := rfl
      evidence := .nil }
  | id :: ids =>
      match symbolEq : program.symbolById? id with
      | none => .error (.malformedAnalysis s!"missing parameter symbol {id}")
      | some symbol => do
          if symbol.kind != .parameter functionId then
            .error (.malformedAnalysis s!"symbol {id} is not a parameter of function {functionId}")
          match bindingEq : Raw.bindingFor? program id with
          | none => .error (.unsupportedType symbol.sourceName symbol.type)
          | some binding => do
              let rest ← checkParameters program functionId ids
              have idEq := Raw.bindingFor_symbolId bindingEq
              let valid : Raw.Binding.Agrees program binding (binding.name, binding.symbolId) :=
                .mk rfl rfl (idEq ▸ bindingEq)
              return {
                bindings := binding :: rest.bindings
                scope := (binding.name, binding.symbolId) :: rest.scope
                parameters := (binding.symbolId, binding.type) :: rest.parameters
                bindings_eq := by
                  simp [Raw.parameterBindings?, bindingEq, rest.bindings_eq]
                evidence := .cons valid rest.evidence }

private structure CheckedStatementRun (program : Program) (functionId : Nat)
    (returnType : ScalarType) (raw : Statement) (initial : ResolveState) where
  statement : Stmt
  final : ResolveState
  evidence : CheckedStatement program functionId returnType raw initial.scopes statement
  scopes_eq : final.scopes = initial.scopes

private structure CheckedBodyRun (program : Program) (functionId : Nat)
    (returnType : ScalarType) (raw : List BlockItem) (initial : ResolveState) where
  statement : Stmt
  final : ResolveState
  evidence : CheckedBody program functionId returnType raw initial.scopes statement

mutual
  private def checkStatement (program : Program) (functionId : Nat)
      (returnType : ScalarType) : (raw : Statement) → (initial : ResolveState) →
      Except Error (CheckedStatementRun program functionId returnType raw initial)
    | .stmt ⟨node, region⟩, initial =>
        match nodeEq : node with
        | .assign (.e ⟨.var name info, leftRegion⟩) rawValue =>
            match scopeEq : lookupScopes name initial.scopes with
            | none => .error (.unresolvedIdentifier leftRegion name)
            | some id =>
                match bindingEq : Raw.bindingFor? program id with
                | none => .error (.malformedAnalysis s!"missing scalar binding {id} for {name}")
                | some binding => do
                    if binding.name != name then
                      .error (.malformedAnalysis s!"binding {id} has the wrong source name")
                    let value ← checkExpr program initial.scopes rawValue
                    return {
                      statement := .assign binding.symbolId binding.type value.expression
                      final := initial
                      evidence := .assign binding (by
                        intro environment agreement
                        rw [agreement.lookup, scopeEq]
                        simp [bindingEq]) value
                      scopes_eq := rfl }
        | .block items => do
            let body ← checkBody program functionId returnType items
              { initial with scopes := [] :: initial.scopes }
            return {
              statement := .seq body.statement .skip
              final := { body.final with scopes := initial.scopes }
              evidence := .block body.evidence
              scopes_eq := rfl }
        | .trap kind body => do
            let body ← checkStatement program functionId returnType body initial
            return {
              statement := .seq body.statement .skip
              final := body.final
              evidence := .trap body.evidence
              scopes_eq := body.scopes_eq }
        | .returnStmt (some rawValue) => do
            let value ← checkExpr program initial.scopes rawValue
            return {
              statement := .return returnType value.expression
              final := initial
              evidence := .ret value
              scopes_eq := rfl }
        | .ifStmt rawCondition rawThen rawElse => do
            let condition ← checkExpr program initial.scopes rawCondition
            let thenBranch ← checkStatement program functionId returnType rawThen initial
            let elseBranch ← checkStatement program functionId returnType rawElse thenBranch.final
            return {
              statement := .cond condition.expression thenBranch.statement elseBranch.statement
              final := elseBranch.final
              evidence := .cond condition thenBranch.evidence
                (thenBranch.scopes_eq ▸ elseBranch.evidence)
              scopes_eq := elseBranch.scopes_eq.trans thenBranch.scopes_eq }
        | .whileStmt rawCondition invariant rawBody => do
            let condition ← checkExpr program initial.scopes rawCondition
            let body ← checkStatement program functionId returnType rawBody initial
            return {
              statement := .while condition.expression body.statement
              final := body.final
              evidence := .while condition body.evidence
              scopes_eq := body.scopes_eq }
        | .emptyStmt => .ok {
            statement := .skip
            final := initial
            evidence := .empty
            scopes_eq := rfl }
        | .break | .continue => .error (.unsupportedStatement region "explicit break/continue")
        | _ => .error (.unsupportedStatement region "statement outside direct scalar slice")

  private def checkBody (program : Program) (functionId : Nat)
      (returnType : ScalarType) : (raw : List BlockItem) → (initial : ResolveState) →
      Except Error (CheckedBodyRun program functionId returnType raw initial)
    | [], initial => .ok { statement := .skip, final := initial, evidence := .nil }
    | .statement rawStatement :: items, initial => do
        let first ← checkStatement program functionId returnType rawStatement initial
        let rest ← checkBody program functionId returnType items first.final
        return {
          statement := .seq first.statement rest.statement
          final := rest.final
          evidence := .statement first.evidence (first.scopes_eq ▸ rest.evidence) }
    | .declaration declaration :: items, initial =>
        match declarationEq : declaration.value with
        | .varDecl rawType name [] initializer attributes => do
            let id ← requireSome (.malformedAnalysis s!"missing analyzed local {name.value}")
              initial.remainingLocals.head?
            match localEq : Raw.localBinding? program functionId declaration.region name.value rawType with
            | none => .error (.malformedAnalysis s!"invalid analyzed local {name.value}")
            | some binding => do
                    if binding.symbolId != id then
                      .error (.malformedAnalysis s!"analyzed local {name.value} does not match id {id}")
                    let valid := Raw.localBinding_agrees localEq
                    let boundState : ResolveState :=
                      { scopes := bindScopes (name.value, binding.symbolId) initial.scopes
                        remainingLocals := initial.remainingLocals.drop 1 }
                    match initializerEq : initializer with
                    | none => do
                        let rest ← checkBody program functionId returnType items boundState
                        return {
                          statement := .seq (.declare binding.symbolId binding.type none) rest.statement
                          final := rest.final
                          evidence := by
                            cases declaration with
                            | mk declarationValue declarationRegion =>
                                simp only at declarationEq
                                subst declarationValue
                                cases initializerEq
                                exact CheckedBody.declaration (attributes := attributes)
                                  binding localEq valid rest.evidence }
                    | some (.initE rawValue) => do
                        let value ← checkExpr program boundState.scopes rawValue
                        let rest ← checkBody program functionId returnType items boundState
                        return {
                          statement := .seq (.declare binding.symbolId binding.type
                            (some value.expression)) rest.statement
                          final := rest.final
                          evidence := by
                            cases declaration with
                            | mk declarationValue declarationRegion =>
                                simp only at declarationEq
                                subst declarationValue
                                cases initializerEq
                                exact CheckedBody.init (attributes := attributes)
                                  binding localEq valid value rest.evidence }
                    | some (.initList _) => .error (.unsupportedStatement declaration.region
                        "initializer lists are outside the scalar slice")
        | .varDecl _ _ (_ :: _) _ _ => .error (.unsupportedStatement declaration.region
            "local storage classes are outside the scalar slice")
        | _ => .error (.unsupportedStatement declaration.region "non-object local declaration")
end

/-!
## Kernel-reducible scalar frontend

The general StrictC frontend intentionally uses partial recursive-descent
functions.  Certification needs a definition the kernel can evaluate, so this
frontend parses the selected scalar function with explicit fuel into the same
raw AST and analyzed-program structures consumed below.
-/

namespace CertifiedFrontend

private inductive TokenKind where
  | ident (name : String)
  | number (literal : NumericLiteral)
  | lparen | rparen | lcurly | rcurly | semicolon | comma
  | assign | plus | minus | mod | plusEq | minusEq | minusMinus
  | greater | lessEq | notEquals
  | other (character : Char)
deriving Repr, DecidableEq

private abbrev Token := Located TokenKind

private def token (kind : TokenKind) : Token := ⟨kind, .bogus⟩

private def isSpace (character : Char) : Bool :=
  character = ' ' || character = '\t' || character = '\n' || character = '\r' ||
    character = '\x0b' || character = '\x0c'

private def isAlpha (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z')

private def isDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isHexDigit (character : Char) : Bool :=
  isDigit character || ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentStart (character : Char) : Bool :=
  isAlpha character || character = '_'

private def isIdentRest (character : Char) : Bool :=
  isIdentStart character || isDigit character

private def span (predicate : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | character :: rest =>
      if predicate character then
        let (taken, remaining) := span predicate rest
        (character :: taken, remaining)
      else ([], character :: rest)

private def skipLineComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => skipLineComment rest

private def skipBlockComment : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: rest => some rest
  | _ :: rest => skipBlockComment rest

private def digitValue (character : Char) : Nat :=
  if isDigit character then character.toNat - '0'.toNat
  else if 'a' ≤ character && character ≤ 'f' then 10 + character.toNat - 'a'.toNat
  else 10 + character.toNat - 'A'.toNat

private def digitsValue (radix : Nat) (digits : List Char) : Nat :=
  digits.foldl (fun value character => value * radix + digitValue character) 0

private def validSuffix (suffix : String) : Bool :=
  ["", "u", "U", "l", "L", "ll", "LL", "ul", "uL", "Ul", "UL",
    "lu", "lU", "Lu", "LU", "ull", "uLL", "Ull", "ULL",
    "llu", "llU", "LLu", "LLU"].contains suffix

private def numericLiteral (characters : List Char) : Except Error NumericLiteral :=
  let finish (radix : Radix) (radixNat : Nat) (digits suffix : List Char) :=
    let suffix := String.ofList suffix
    if digits.isEmpty then .error (.malformedAnalysis "integer literal has no digits")
    else if !validSuffix suffix then .error (.malformedAnalysis "invalid integer suffix")
    else .ok { value := digitsValue radixNat digits, radix, suffix }
  match characters with
  | '0' :: 'x' :: rest =>
      let (digits, suffix) := span isHexDigit rest
      finish .hexadecimal 16 digits suffix
  | '0' :: 'X' :: rest =>
      let (digits, suffix) := span isHexDigit rest
      finish .hexadecimal 16 digits suffix
  | '0' :: 'b' :: rest =>
      let (digits, suffix) := span isDigit rest
      if digits.any (fun character => character ≠ '0' && character ≠ '1') then
        .error (.malformedAnalysis "invalid binary digit")
      else finish .binary 2 digits suffix
  | '0' :: 'B' :: rest =>
      let (digits, suffix) := span isDigit rest
      if digits.any (fun character => character ≠ '0' && character ≠ '1') then
        .error (.malformedAnalysis "invalid binary digit")
      else finish .binary 2 digits suffix
  | '0' :: second :: rest =>
      if isDigit second then
        let (digits, suffix) := span isDigit (second :: rest)
        if digits.any (fun character => '7' < character) then
          .error (.malformedAnalysis "invalid octal digit")
        else finish .octal 8 ('0' :: digits) suffix
      else finish .decimal 10 ['0'] (second :: rest)
  | digits =>
      let (digits, suffix) := span isDigit digits
      finish .decimal 10 digits suffix

private def lexGo : Nat → List Char → Except Error (List Token)
  | 0, [] => .ok []
  | 0, _ => .error (.malformedAnalysis "scalar frontend lexer exhausted fuel")
  | fuel + 1, characters =>
      match characters with
      | [] => .ok []
      | '/' :: '/' :: rest => lexGo fuel (skipLineComment rest)
      | '/' :: '*' :: rest =>
          match skipBlockComment rest with
          | none => .error (.malformedAnalysis "unclosed comment")
          | some remaining => lexGo fuel remaining
      | character :: rest =>
          if isSpace character then lexGo fuel rest
          else if isIdentStart character then
            let (tail, remaining) := span isIdentRest rest
            return token (.ident (String.ofList (character :: tail))) ::
              (← lexGo fuel remaining)
          else if isDigit character then
            let (tail, remaining) := span isIdentRest rest
            return token (.number (← numericLiteral (character :: tail))) ::
              (← lexGo fuel remaining)
          else
            let (kind, remaining) := match character, rest with
              | '<', '=' :: tail => (.lessEq, tail)
              | '!', '=' :: tail => (.notEquals, tail)
              | '+', '=' :: tail => (.plusEq, tail)
              | '-', '=' :: tail => (.minusEq, tail)
              | '-', '-' :: tail => (.minusMinus, tail)
              | '(', _ => (.lparen, rest) | ')', _ => (.rparen, rest)
              | '{', _ => (.lcurly, rest) | '}', _ => (.rcurly, rest)
              | ';', _ => (.semicolon, rest) | ',', _ => (.comma, rest)
              | '=', _ => (.assign, rest) | '+', _ => (.plus, rest)
              | '-', _ => (.minus, rest) | '%', _ => (.mod, rest)
              | '>', _ => (.greater, rest)
              | _, _ => (.other character, rest)
            return token kind :: (← lexGo fuel remaining)

private def lex (source : String) : Except Error (List Token) :=
  lexGo (source.length + 1) source.toList

private def parseType : List Token → Option (CType CParser.Expr × AnalyzedCType × List Token)
  | ⟨.ident "unsigned", _⟩ :: ⟨.ident "int", _⟩ :: rest =>
      some (.unsigned .int, .unsigned .int, rest)
  | ⟨.ident "unsigned", _⟩ :: rest => some (.unsigned .int, .unsigned .int, rest)
  | ⟨.ident "int", _⟩ :: rest => some (.signed .int, .signed .int, rest)
  | _ => none

private structure Parameters where
  raw : List (CType CParser.Expr × Located String)
  analyzed : List AnalyzedCType
  symbols : List SymbolInfo
  rest : List Token

private def parseParameters : Nat → Nat → List Token → Option Parameters
  | 0, _, _ => none
  | _ + 1, _, ⟨.rparen, _⟩ :: rest => some ⟨[], [], [], rest⟩
  | _ + 1, _, ⟨.ident "void", _⟩ :: ⟨.rparen, _⟩ :: rest => some ⟨[], [], [], rest⟩
  | fuel + 1, nextId, tokens => do
      let (rawType, analyzedType, tokens) ← parseType tokens
      let ⟨.ident name, region⟩ :: tokens := tokens | none
      let delimiter :: tokens := tokens | none
      let tail ← match delimiter.value with
        | .rparen => some ⟨[], [], [], tokens⟩
        | .comma => parseParameters fuel (nextId + 1) tokens
        | _ => none
      let symbol : SymbolInfo :=
        { id := nextId, sourceName := name, type := analyzedType
          kind := .parameter 0, region }
      return {
        raw := (rawType, ⟨name, region⟩) :: tail.raw
        analyzed := analyzedType :: tail.analyzed
        symbols := symbol :: tail.symbols
        rest := tail.rest }

private structure Header where
  rawReturn : CType CParser.Expr
  returnType : AnalyzedCType
  name : Located String
  parameters : Parameters

private def parseHeaderAt (tokens : List Token) : Option Header := do
  let (rawReturn, returnType, tokens) ← parseType tokens
  let ⟨.ident name, region⟩ :: ⟨.lparen, _⟩ :: tokens := tokens | none
  let parameters ← parseParameters (tokens.length + 1) 1 tokens
  let ⟨.lcurly, _⟩ :: _ := parameters.rest | none
  return { rawReturn, returnType, name := ⟨name, region⟩, parameters }

private def findHeader : Nat → String → List Token → Option Header
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, name, tokens@(_ :: rest) =>
      match parseHeaderAt tokens with
      | some header => if header.name.value = name then some header else findHeader fuel name rest
      | none => findHeader fuel name rest

private def rawVariable (name : String) : CParser.Expr :=
  .e ⟨.var name none, .bogus⟩

private def rawNumber (literal : NumericLiteral) : CParser.Expr :=
  .e ⟨.constant ⟨.numConst {
    value := Int.ofNat literal.value, suffix := literal.suffix, base := literal.radix }, .bogus⟩,
    .bogus⟩

mutual
  private def parseAtom : Nat → List Token → Except Error (CParser.Expr × List Token)
    | 0, _ => .error (.malformedAnalysis "scalar expression parser exhausted fuel")
    | _ + 1, ⟨.ident name, _⟩ :: rest => .ok (rawVariable name, rest)
    | _ + 1, ⟨.number literal, _⟩ :: rest => .ok (rawNumber literal, rest)
    | fuel + 1, ⟨.lparen, _⟩ :: rest => do
        let (expression, rest) ← parseExpression fuel rest
        let ⟨.rparen, _⟩ :: rest := rest |
          .error (.malformedAnalysis "expected ')' in scalar expression")
        .ok (expression, rest)
    | _ + 1, _ => .error (.malformedAnalysis "expected scalar expression")

  private def parseExpression : Nat → List Token → Except Error (CParser.Expr × List Token)
    | 0, _ => .error (.malformedAnalysis "scalar expression parser exhausted fuel")
    | fuel + 1, tokens => do
        let (left, tokens) ← parseAtom fuel tokens
        match tokens with
        | ⟨.plus, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .plus left right, .bogus⟩, rest)
        | ⟨.minus, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .minus left right, .bogus⟩, rest)
        | ⟨.mod, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .modulus left right, .bogus⟩, rest)
        | ⟨.notEquals, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .notEquals left right, .bogus⟩, rest)
        | ⟨.greater, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .gt left right, .bogus⟩, rest)
        | ⟨.lessEq, _⟩ :: rest =>
            let (right, rest) ← parseExpression fuel rest
            .ok (.e ⟨.binOp .leq left right, .bogus⟩, rest)
        | _ => .ok (left, tokens)
end

private structure ParseState where
  tokens : List Token
  nextId : Nat
  locals : List Nat := []
  localSymbols : List SymbolInfo := []

mutual
  private def parseBody : Nat → ParseState → Except Error (Body × ParseState)
    | 0, _ => .error (.malformedAnalysis "scalar statement parser exhausted fuel")
    | fuel + 1, state =>
        match state.tokens with
        | ⟨.lcurly, _⟩ :: rest => parseItems fuel { state with tokens := rest }
        | _ => .error (.malformedAnalysis "expected scalar function body")

  private def parseItems : Nat → ParseState → Except Error (Body × ParseState)
    | 0, _ => .error (.malformedAnalysis "scalar statement parser exhausted fuel")
    | fuel + 1, state =>
        match state.tokens with
        | ⟨.rcurly, _⟩ :: rest => .ok (⟨[], .bogus⟩, { state with tokens := rest })
        | tokens =>
            match parseType tokens with
            | some (rawType, analyzedType, ⟨.ident name, nameRegion⟩ :: rest) => do
                let id := state.nextId
                let (initializer, rest) ← (match rest with
                  | ⟨.assign, _⟩ :: expressionTokens => do
                      let (expression, rest) ← parseExpression fuel expressionTokens
                      .ok (some (Initializer.initE expression), rest)
                  | _ => .ok (none, rest) :
                    Except Error (Option Initializer × List Token))
                let ⟨.semicolon, _⟩ :: rest := rest |
                  .error (.malformedAnalysis "expected ';' after scalar declaration")
                let declaration : Located Declaration := ⟨
                  .varDecl rawType ⟨name, nameRegion⟩ [] initializer [], .bogus⟩
                let symbol : SymbolInfo :=
                  { id, sourceName := name, type := analyzedType, kind := .local 0, region := .bogus }
                let next : ParseState :=
                  { tokens := rest, nextId := id + 1
                    locals := state.locals ++ [id]
                    localSymbols := state.localSymbols ++ [symbol] }
                let (body, final) ← parseItems fuel next
                .ok (⟨.declaration declaration :: body.value, .bogus⟩, final)
            | _ => do
                let (statement, next) ← parseStatement fuel state
                let (body, final) ← parseItems fuel next
                .ok (⟨.statement statement :: body.value, .bogus⟩, final)

  private def parseStatement : Nat → ParseState → Except Error (Statement × ParseState)
    | 0, _ => .error (.malformedAnalysis "scalar statement parser exhausted fuel")
    | fuel + 1, state =>
        match state.tokens with
        | ⟨.ident "return", _⟩ :: rest => do
            let (expression, rest) ← parseExpression fuel rest
            let ⟨.semicolon, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ';' after return")
            .ok (.stmt ⟨.returnStmt (some expression), .bogus⟩, { state with tokens := rest })
        | ⟨.ident "if", _⟩ :: ⟨.lparen, _⟩ :: rest => do
            let (condition, rest) ← parseExpression fuel rest
            let ⟨.rparen, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ')' after condition")
            let (thenBranch, afterThen) ← parseStatement fuel { state with tokens := rest }
            match afterThen.tokens with
            | ⟨.ident "else", _⟩ :: rest => do
                let (elseBranch, final) ← parseStatement fuel { afterThen with tokens := rest }
                .ok (.stmt ⟨.ifStmt condition thenBranch elseBranch, .bogus⟩, final)
            | _ =>
                let empty : Statement := .stmt ⟨.emptyStmt, .bogus⟩
                .ok (.stmt ⟨.ifStmt condition thenBranch empty, .bogus⟩, afterThen)
        | ⟨.ident "while", _⟩ :: ⟨.lparen, _⟩ :: rest => do
            let (condition, rest) ← parseExpression fuel rest
            let ⟨.rparen, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ')' after while condition")
            let (body, final) ← parseStatement fuel { state with tokens := rest }
            .ok (.stmt ⟨.whileStmt condition none body, .bogus⟩, final)
        | ⟨.ident name, _⟩ :: ⟨.plusEq, _⟩ :: rest => do
            let (right, rest) ← parseExpression fuel rest
            let ⟨.semicolon, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ';' after compound assignment")
            let left := rawVariable name
            let value : CParser.Expr := .e ⟨.binOp .plus left right, .bogus⟩
            .ok (.stmt ⟨.assign left value, .bogus⟩, { state with tokens := rest })
        | ⟨.ident name, _⟩ :: ⟨.minusEq, _⟩ :: rest => do
            let (right, rest) ← parseExpression fuel rest
            let ⟨.semicolon, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ';' after compound assignment")
            let left := rawVariable name
            let value : CParser.Expr := .e ⟨.binOp .minus left right, .bogus⟩
            .ok (.stmt ⟨.assign left value, .bogus⟩, { state with tokens := rest })
        | ⟨.ident name, _⟩ :: ⟨.minusMinus, _⟩ :: ⟨.semicolon, _⟩ :: rest =>
            let left := rawVariable name
            let one := rawNumber { value := 1, radix := .decimal, suffix := "" }
            let value : CParser.Expr := .e ⟨.binOp .minus left one, .bogus⟩
            .ok (.stmt ⟨.assign left value, .bogus⟩, { state with tokens := rest })
        | ⟨.ident name, _⟩ :: ⟨.assign, _⟩ :: rest => do
            let (right, rest) ← parseExpression fuel rest
            let ⟨.semicolon, _⟩ :: rest := rest |
              .error (.malformedAnalysis "expected ';' after assignment")
            .ok (.stmt ⟨.assign (rawVariable name) right, .bogus⟩,
              { state with tokens := rest })
        | ⟨.lcurly, _⟩ :: _ => do
            let (body, final) ← parseBody fuel state
            .ok (.stmt ⟨.block body.value, .bogus⟩, final)
        | _ => .error (.malformedAnalysis
            s!"statement outside certified scalar subset: {repr (state.tokens.take 4)}")
end

private def buildProgram (target : Target) (header : Header) : Except Error Program := do
  let initial : ParseState :=
    { tokens := header.parameters.rest, nextId := header.parameters.symbols.length + 1 }
  let (body, final) ← parseBody (initial.tokens.length + 1) initial
  let functionType : AnalyzedCType := .function header.returnType header.parameters.analyzed
  let functionSymbol : SymbolInfo :=
    { id := 0, sourceName := header.name.value, type := functionType
      kind := .function, region := header.name.region }
  let info : FunctionInfo :=
    { symbolId := 0, returnType := header.returnType
      parameters := header.parameters.symbols.map (·.id)
      locals := final.locals, specifications := [], body, region := .bogus }
  let external : ExternalDeclaration := .functionDefinition
    (header.rawReturn, header.name) header.parameters.raw [] [] body
  .ok {
    target, translationUnit := [external], typedefs := [], typeAbbrevs := Zag.TypeAbbrevCtx.empty
    structs := [], symbols := functionSymbol :: header.parameters.symbols ++ final.localSymbols
    functions := [info], globals := [], expressionTypes := [], calls := [], staticObjects := [] }

/-- Total source-to-program frontend for the currently certified scalar subset. -/
def analyze (target : Target) (files : Preprocessor.FileMap) (entry name : String) :
    Except Error Program := do
  let file ← match files.find? (·.name = entry) with
    | some file => .ok file
    | none => .error (.malformedAnalysis s!"source file not found: {entry}")
  let tokens ← lex file.source
  let header ← match findHeader (tokens.length + 1) name tokens with
    | some header => .ok header
    | none => .error (.functionNotFound name)
  buildProgram target header

end CertifiedFrontend

def selectedFunctions (program : Program) (name : String) : List FunctionInfo :=
  program.functions.filter fun function =>
    (program.symbolById? function.symbolId).any (·.sourceName = name)

inductive CheckedResolution (program : Program) (name : String) (info : FunctionInfo)
    (rawBody : Body) : Function → Prop where
  | checked (selected : selectedFunctions program name = [info])
      (raw : rawBody = info.body) (returnType : ScalarType)
      (parameters : CheckedParameters program info.symbolId info.parameters)
      (body : CheckedBody program info.symbolId returnType info.body.value
        [parameters.scope] resolvedBody) :
      CheckedResolution program name info rawBody
        { name
          returnType
          parameters := parameters.parameters
          locals := info.locals
          body := resolvedBody }

private structure CheckedFunctionRun (program : Program) (name : String) where
  function : Function
  info : FunctionInfo
  resolution : CheckedResolution program name info info.body function

private def checkFunction (program : Program) (name : String) :
    Except Error (CheckedFunctionRun program name) :=
  match selection : selectedFunctions program name with
  | [] => .error (.functionNotFound name)
  | [info] => do
      if name = "main" && (info.returnType != .signed .int || !info.parameters.isEmpty) then
        .error (.malformedAnalysis "the scalar slice accepts only int main(void)")
      let returnType ← scalarType program.target name info.returnType
      let parameters ← checkParameters program info.symbolId info.parameters
      let initial : ResolveState :=
        { scopes := [parameters.scope], remainingLocals := info.locals }
      let body ← checkBody program info.symbolId returnType info.body.value initial
      if body.statement.declaredIds != info.locals then
        .error (.malformedAnalysis
          s!"resolved declarations {body.statement.declaredIds} do not match {info.locals}")
      let function : Function :=
        { name
          returnType
          parameters := parameters.parameters
          locals := info.locals
          body := body.statement }
      return {
        function
        info
        resolution := .checked selection rfl returnType parameters body.evidence }
  | _ => .error (.ambiguousFunction name)

/-- Resolve and lower one analyzed function by lexical scope and allocated symbol ID. -/
private def resolveFunctionRuntime (program : Program) (name : String) : Except Error Function := do
  let functions := selectedFunctions program name
  let info ← (match functions with
    | [] => .error (.functionNotFound name)
    | [function] => return function
    | _ => .error (.ambiguousFunction name) : Except Error FunctionInfo)
  if name = "main" && (info.returnType != .signed .int || !info.parameters.isEmpty) then
    .error (.malformedAnalysis "the scalar slice accepts only int main(void)")
  let returnType ← scalarType program.target name info.returnType
  let parameters ← info.parameters.mapM fun id => do
    let binding ← requireSome (.malformedAnalysis s!"missing parameter symbol {id}")
      (Raw.bindingFor? program id)
    return ((binding.name, binding.symbolId), (binding.symbolId, binding.type))
  let initial : ResolveState :=
    { scopes := [parameters.map (·.1)], remainingLocals := info.locals }
  let (body, _) ← (resolveBody program info.symbolId returnType info.body.value).run initial
  if body.declaredIds != info.locals then
    .error (.malformedAnalysis s!"resolved declarations {body.declaredIds} do not match {info.locals}")
  return { name, returnType, parameters := parameters.map (·.2), locals := info.locals, body }

/-- Executable resolved-IR lowering. This carries no frontend raw-C certificate. -/
def resolveIR (program : Program) (name : String) : Except Error Function :=
  resolveFunctionRuntime program name

@[implemented_by resolveFunctionRuntime]
def resolveFunction (program : Program) (name : String) : Except Error Function :=
  (checkFunction program name).map (·.function)

structure ResolvedCertificate (program : Program) (name : String) (function : Function) where
  functionInfo : FunctionInfo
  rawBody : Body
  resolution : CheckedResolution program name functionInfo rawBody function
  exactResolution : resolveFunction program name = .ok function
  source : Command
  source_eq : source = function.command
  supported : SimplConv.Kernel.Supported source
  equivalence : function.Equivalent source

structure ResolvedCertified (program : Program) (name : String) where
  function : Function
  certificate : ResolvedCertificate program name function

/- Resolve and certify in one dependent operation; no certificate can be made from a bare function. -/
def certifyResolved (program : Program) (name : String) :
    Except Error (ResolvedCertified program name) :=
  match checkedEq : checkFunction program name with
  | .error error => .error error
  | .ok checked => .ok {
      function := checked.function
      certificate := {
        functionInfo := checked.info
        rawBody := checked.info.body
        resolution := checked.resolution
        exactResolution := by
          unfold resolveFunction
          rw [checkedEq]
          rfl
        source := checked.function.command
        source_eq := rfl
        supported := checked.function.supported
        equivalence := checked.function.command_equivalent } }

/-- Bidirectional finite correspondence between raw C execution and resolved IR execution. -/
structure StructuralResolution (program : Program) (name : String) (info : FunctionInfo)
    (rawBody : Body) (function : Function) : Prop where
  checked : CheckedResolution program name info rawBody function

private theorem CheckedParameters.environment_eq
    (parameters : CheckedParameters program functionId raw) :
    Raw.parameterEnv? program functionId raw = some [parameters.bindings] := by
  simp [Raw.parameterEnv?, parameters.bindings_eq]

theorem CheckedResolution.rawToResolved
    (resolution : CheckedResolution program name info rawBody function)
    (execution : Raw.FunctionExec program name info rawBody function.returnType state outcome) :
    function.Exec state (Raw.embedOutcome outcome) := by
  cases resolution with
  | checked selected raw returnType parameters body =>
      cases raw
      have environmentEq := parameters.environment_eq
      cases execution with
      | returned found rawExecution =>
          rw [environmentEq] at found
          have same := Option.some.inj found
          cases same
          exact Function.Exec.returned
            (body.rawToResolved (.cons parameters.evidence .nil) rawExecution)
      | fault found rawExecution =>
          rw [environmentEq] at found
          have same := Option.some.inj found
          cases same
          exact Function.Exec.fault
            (body.rawToResolved (.cons parameters.evidence .nil) rawExecution)
      | fellOff found rawExecution =>
          rw [environmentEq] at found
          have same := Option.some.inj found
          cases same
          have resolvedExecution := Function.Exec.fellOff (function := {
            name
            returnType
            parameters := parameters.parameters
            locals := info.locals
            body := _ })
            (body.rawToResolved (.cons parameters.evidence .nil) rawExecution)
          by_cases isMain : name = "main" <;>
            simpa [Raw.embedOutcome, isMain] using resolvedExecution

theorem CheckedResolution.resolvedToRaw
    (resolution : CheckedResolution program name info rawBody function)
    (execution : function.Exec state result) :
    ∃ outcome, result = Raw.embedOutcome outcome ∧
      Raw.FunctionExec program name info rawBody function.returnType state outcome := by
  cases resolution with
  | checked selected raw returnType parameters body =>
      cases raw
      have environmentEq := parameters.environment_eq
      cases execution with
      | returned resolvedExecution =>
          obtain ⟨outcome, equality, rawExecution⟩ :=
            body.resolvedToRaw (.cons parameters.evidence .nil) resolvedExecution
          cases Raw.returned_eq_of_embed equality
          exact ⟨.success _, rfl, Raw.FunctionExec.returned environmentEq rawExecution⟩
      | fault resolvedExecution =>
          obtain ⟨outcome, equality, rawExecution⟩ :=
            body.resolvedToRaw (.cons parameters.evidence .nil) resolvedExecution
          cases Raw.fault_eq_of_embed equality
          exact ⟨.undefinedBehavior, rfl, Raw.FunctionExec.fault environmentEq rawExecution⟩
      | fellOff resolvedExecution =>
          obtain ⟨outcome, equality, rawExecution⟩ :=
            body.resolvedToRaw (.cons parameters.evidence .nil) resolvedExecution
          cases Raw.normal_eq_of_embed equality
          refine ⟨if name = "main" then .success _ else .undefinedBehavior, ?_,
            Raw.FunctionExec.fellOff environmentEq rawExecution⟩
          by_cases isMain : name = "main" <;> simp [isMain, Raw.embedOutcome]

theorem StructuralResolution.rawToResolved
    (resolution : StructuralResolution program name info rawBody function) :
    ∀ state outcome,
      Raw.FunctionExec program name info rawBody function.returnType state outcome →
        function.Exec state (Raw.embedOutcome outcome) :=
  by
    intro state outcome execution
    exact resolution.checked.rawToResolved execution

theorem StructuralResolution.resolvedToRaw
    (resolution : StructuralResolution program name info rawBody function) :
    ∀ state result, function.Exec state result →
      ∃ outcome, result = Raw.embedOutcome outcome ∧
        Raw.FunctionExec program name info rawBody function.returnType state outcome :=
  by
    intro state result execution
    exact resolution.checked.resolvedToRaw execution

def Raw.Equivalent (program : Program) (name : String) (info : FunctionInfo)
    (rawBody : Body) (returnType : ScalarType) (command : Command) : Prop :=
  (∀ state outcome, Raw.FunctionExec program name info rawBody returnType state outcome →
    Simpl.Exec emptyEnvironment command (.normal state) (Raw.embedOutcome outcome)) ∧
  (∀ state result, Simpl.Exec emptyEnvironment command (.normal state) result →
    ∃ outcome, result = Raw.embedOutcome outcome ∧
      Raw.FunctionExec program name info rawBody returnType state outcome)

theorem StructuralResolution.compose (resolution :
    StructuralResolution program name info rawBody function) :
    Raw.Equivalent program name info rawBody function.returnType function.command := by
  constructor
  · intro state outcome execution
    exact function.command_correct state _ (resolution.rawToResolved state outcome execution)
  · intro state result execution
    exact resolution.resolvedToRaw state result (function.command_complete execution)

/--
The advertised analyzed-C certificate is indexed by the complete certified scalar frontend
invocation. The `analyzed` equality is checked by the kernel, so a caller-constructed mutation
of `Program` cannot inhabit this type without proving it is the source parser's actual result.
-/
structure Certificate (target : Target) (files : Preprocessor.FileMap) (entry name : String)
    (function : Function) where
  private mk ::
  program : Program
  analyzed : CertifiedFrontend.analyze target files entry name = .ok program
  functionInfo : FunctionInfo
  rawBody : Body
  resolution : StructuralResolution program name functionInfo rawBody function
  supported : SimplConv.Kernel.Supported function.command

structure Certified (target : Target) (files : Preprocessor.FileMap) (entry name : String) where
  function : Function
  certificate : Certificate target files entry name function

theorem Certificate.finite_iff (certificate : Certificate target files entry name function) :
    ∀ state outcome,
      Raw.FunctionExec certificate.program name certificate.functionInfo certificate.rawBody
          function.returnType state outcome ↔
        Simpl.Exec emptyEnvironment function.command (.normal state) (Raw.embedOutcome outcome) := by
  intro state outcome
  have equivalence := certificate.resolution.compose
  constructor
  · exact equivalence.1 state outcome
  · intro execution
    obtain ⟨found, equality, raw⟩ := equivalence.2 state _ execution
    have same : found = outcome := Raw.embedOutcome_injective equality.symm
    cases same
    exact raw

/- Construct the raw-C certificate only from this exact frontend invocation. -/
def certifyFrontend (target : Target) (files : Preprocessor.FileMap)
    (entry name : String) : Except Error (Certified target files entry name) :=
  match analyzed : CertifiedFrontend.analyze target files entry name with
  | .error error => .error error
  | .ok program =>
      match checkFunction program name with
      | .error error => .error error
      | .ok checked =>
          let resolution : StructuralResolution program name checked.info checked.info.body
              checked.function := ⟨checked.resolution⟩
          .ok {
            function := checked.function
            certificate := {
              program
              analyzed := analyzed
              functionInfo := checked.info
              rawBody := checked.info.body
              resolution
              supported := checked.function.supported } }

end Zag.Lang.AutoCorres.CParser.ScalarSimpl
