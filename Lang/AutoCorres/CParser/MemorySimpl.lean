import Lang.AutoCorres.CParser.MemoryModel
import Lang.AutoCorres.SimplConv

/-!
# Certified analyzed-C memory lowering

This module is deliberately a closed ARM fragment.  Its source semantics runs
the parser AST, while its resolved semantics runs a symbol- and layout-resolved
IR.  Resolution produces the structural evidence used to relate the two; the
layout and frontend objects are not supplied by a caller.
-/

namespace Zag.Lang.AutoCorres.CParser.MemorySimpl

open ProgramAnalysis MemoryLayout MemoryModel

inductive Error where
  | frontendFailure
  | functionNotFound (name : String)
  | ambiguousFunction (name : String)
  | layout (error : MemoryLayout.Error)
  | unsupportedTarget
  | unsupportedType (region : Region) (type : AnalyzedCType)
  | unresolvedIdentifier (region : Region) (name : String)
  | unallocatedExternal (region : Region) (name : String)
  | malformedAnalysis (description : String)
  | unsupportedExpression (region : Region) (description : String)
  | unsupportedStatement (region : Region) (description : String)
  | directCall (region : Region)
  | localAddress (region : Region)
  | initialization (error : MemoryModel.InitializationError)
deriving Repr, Inhabited

inductive Value where
  | integer (value : Int)
  | pointer (value : Pointer)
  | void
deriving Repr, DecidableEq, Inhabited

structure State where
  heap : ByteHeap := zeroHeap
  external : ExternalMemory := []
  value : Nat → Value := fun _ => .void
  initialized : Nat → Bool := fun _ => false
  returned : Bool := false
  result : Value := .void

namespace State

def read? (state : State) (symbolId : Nat) : Option Value :=
  if state.initialized symbolId then some (state.value symbolId) else none

def write (state : State) (symbolId : Nat) (value : Value) : State :=
  { state with
    value := fun id => if id = symbolId then value else state.value id
    initialized := fun id => if id = symbolId then true else state.initialized id }

def clear (state : State) (symbolId : Nat) : State :=
  { state with initialized := fun id => if id = symbolId then false else state.initialized id }

def withHeap (state : State) (heap : ByteHeap) : State := { state with heap }

def returnValue (state : State) (value : Value) : State :=
  { state with returned := true, result := value }

def resetReturn (state : State) : State :=
  { state with returned := false, result := .void }

end State

private def scalarType (target : Target) : AnalyzedCType → Option ScalarSimpl.ScalarType
  | .signed kind => some ⟨.signed, target.intWidthOf kind⟩
  | .unsigned kind => some ⟨.unsigned, target.intWidthOf kind⟩
  | .plainChar => some ⟨if target.charSigned then .signed else .unsigned, target.charWidth⟩
  | .bool => some ⟨.unsigned, target.boolWidth⟩
  | .enumTy _ => some ⟨.signed, target.intWidth⟩
  | _ => none

private def castInteger (target : Target) (type : AnalyzedCType) (value : Int) : Option Int := do
  let scalar ← scalarType target type
  return match type with
    | .bool => if value = 0 then 0 else 1
    | _ => scalar.cast value

def castValue (target : Target) (type : AnalyzedCType) : Value → Option Value
  | .integer value => return .integer (← castInteger target type value)
  | .pointer pointer => if type.ptrType then some (.pointer pointer) else none
  | .void => if type == .void then some .void else none

private def structSize (program : Program) (name : String) : Int :=
  (program.structs.find? (·.canonicalName = name)).map (Int.ofNat ·.size) |>.getD (-1)

def sizeOf? (program : Program) (type : AnalyzedCType) : Option Nat := do
  let size ← (CType.sizeof program.target (structSize program) type).toOption
  if size ≤ 0 then none else some size.toNat

private def expressionType? (program : Program) : CParser.Expr → Option AnalyzedCType
  | .e located => match program.expressionTypesAt located.region with
      | [type] => some type
      | _ => none

private def implementedIntegerOperator : BinOpType → Bool
  | .plus | .minus | .times | .divides | .modulus |
      .equals | .notEquals | .lt | .gt | .leq | .geq => true
  | _ => false

private def representationCompatible (target : Target)
    (destinationType expressionType : AnalyzedCType) : Bool :=
  ((scalarType target destinationType).isSome && (scalarType target expressionType).isSome) ||
    (destinationType.ptrType && (expressionType.ptrType || expressionType.arrayType))

private def globalSymbol? (program : Program) (name : String) : Option SymbolInfo :=
  match program.symbols.filter fun symbol =>
      symbol.sourceName = name && symbol.kind = .global with
  | [symbol] => some symbol
  | _ => none

private def missingGlobalStorageError (program : Program) (region : Region)
    (symbol : SymbolInfo) : Error :=
  if program.staticObjects.any (·.symbolId == symbol.id) then
    .malformedAnalysis s!"global {symbol.sourceName} has no layout pointer"
  else
    .unallocatedExternal region symbol.sourceName

private def field? (program : Program) (type : AnalyzedCType) (name : String) : Option FieldInfo := do
  let .structTy canonicalName := type | none
  let info ← program.structs.find? (·.canonicalName = canonicalName)
  info.fields.find? (·.sourceName = name)

private def offsetPointer? (layout : Layout) (pointer : Pointer) (offset : Nat) : Option Pointer := do
  if layout.pointerWidth != 32 then none
  let symbolId ← pointer.provenance
  let object ← layout.objectBySymbolId? symbolId
  let address := pointer.address.toNat
  if address < object.base || object.limit < address + offset then none
  if 2 ^ 32 ≤ address + offset then none
  return { address := BitVec.ofNat 32 (address + offset), provenance := some symbolId }

private def integerBinary (target : Target) (resultType operandType : AnalyzedCType)
    (operator : BinOpType) (left right : Int) : Option Int := do
  let operand ← scalarType target operandType
  let result ← scalarType target resultType
  let left := operand.cast left
  let right := operand.cast right
  let checked (value : Int) := match operand.signedness with
    | .unsigned => some (operand.cast value)
    | .signed => if operand.inRange value then some value else none
  match operator with
  | .plus => checked (left + right)
  | .minus => checked (left - right)
  | .times => checked (left * right)
  | .divides =>
      if right = 0 then none
      else if operand.signedness = .signed &&
          left = -((2 : Int) ^ (operand.width - 1)) && right = -1 then none
      else some (result.cast (ScalarSimpl.Expr.truncDiv left right))
  | .modulus =>
      if right = 0 then none
      else if operand.signedness = .signed &&
          left = -((2 : Int) ^ (operand.width - 1)) && right = -1 then none
      else some (result.cast (ScalarSimpl.Expr.truncMod left right))
  | .equals => some (if left = right then 1 else 0)
  | .notEquals => some (if left ≠ right then 1 else 0)
  | .lt => some (if left < right then 1 else 0)
  | .gt => some (if left > right then 1 else 0)
  | .leq => some (if left ≤ right then 1 else 0)
  | .geq => some (if left ≥ right then 1 else 0)
  | _ => none

inductive Location where
  | slot (symbolId : Nat) (type : AnalyzedCType)
  | memory (pointer : Pointer) (type : AnalyzedCType)
deriving Repr, DecidableEq, Inhabited

def readLocation {program : Program} (layout : MemoryLayout.Certificate program)
    (location : Location) (state : State) : Option Value :=
  match location with
  | .slot symbolId type => do
      let value ← state.read? symbolId
      castValue program.target type value
  | .memory pointer type =>
      return .integer (← loadIntegerIn? layout state.external type pointer state.heap)

def writeLocation {program : Program} (layout : MemoryLayout.Certificate program)
    (location : Location) (value : Value) (state : State) : Option State := do
  let value ← castValue program.target (match location with | .slot _ type | .memory _ type => type) value
  match location, value with
  | .slot symbolId _, value => some (state.write symbolId value)
  | .memory pointer type, .integer value =>
      return state.withHeap
        (← storeIntegerIn? layout state.external type pointer value state.heap)
  | .memory .., _ => none

namespace Raw

structure Binding where
  name : String
  symbolId : Nat
  type : AnalyzedCType
deriving Repr, DecidableEq, Inhabited

abbrev Env := List (List Binding)

namespace Env

private def lookupScope (name : String) : List Binding → Option Binding
  | [] => none
  | binding :: bindings => if binding.name = name then some binding else lookupScope name bindings

def lookup (name : String) : Env → Option Binding
  | [] => none
  | scope :: scopes => (lookupScope name scope).orElse fun _ => lookup name scopes

def bind (binding : Binding) : Env → Env
  | [] => [[binding]]
  | scope :: scopes => (binding :: scope) :: scopes

end Env

private def evalLocalOrGlobal {program : Program}
    (layout : MemoryLayout.Certificate program) (environment : Env) (name : String)
    (state : State) : Option (AnalyzedCType × Value) :=
  match environment.lookup name with
  | some binding => return (binding.type, ← state.read? binding.symbolId)
  | none => do
      let symbol ← globalSymbol? program name
      match symbol.type with
      | type@(.array _ _) =>
          return (type, .pointer (← Pointer.ofGlobal? layout.layout symbol.id))
      | type =>
          let pointer ← Pointer.ofGlobal? layout.layout symbol.id
          return (type, ← readLocation layout (.memory pointer type) state)

mutual
  /-- Direct finite expression semantics over the parser AST. -/
  def evalExpr {program : Program} (layout : MemoryLayout.Certificate program)
      (environment : Env) : CParser.Expr → State → Option (AnalyzedCType × Value)
    | .e ⟨node, region⟩, state => do
        let resultType ← expressionType? program (.e ⟨node, region⟩)
        match node with
        | .constant ⟨.numConst info, _⟩ =>
            return (resultType, .integer (← castInteger program.target resultType info.value))
        | .var name _ =>
            match environment.lookup name with
            | some binding =>
                let value ← state.read? binding.symbolId
                match binding.type with
                | .array _ _ => return (resultType, value)
                | _ => return (resultType, ← castValue program.target resultType value)
            | none =>
                let symbol ← globalSymbol? program name
                match symbol.type with
                | .array _ _ =>
                    return (resultType, .pointer (← Pointer.ofGlobal? layout.layout symbol.id))
                | type =>
                    let pointer ← Pointer.ofGlobal? layout.layout symbol.id
                    let value ← readLocation layout (.memory pointer type) state
                    return (resultType, ← castValue program.target resultType value)
        | .unOp .addr value =>
            let (_, location) ← evalLValue layout environment value state
            let pointer ← match location with | .memory pointer _ => some pointer | .slot .. => none
            return (resultType, .pointer pointer)
        | .unOp .not value =>
            let (_, .integer value) ← evalExpr layout environment value state | none
            return (resultType, .integer (if value = 0 then 1 else 0))
        | .unOp .negate value =>
            let (_, .integer value) ← evalExpr layout environment value state | none
            return (resultType, .integer (← integerBinary program.target resultType resultType
              .minus 0 value))
        | .binOp operator left right =>
            let (leftType, leftValue) ← evalExpr layout environment left state
            let (rightType, rightValue) ← evalExpr layout environment right state
            match leftValue, rightValue with
            | .integer left, .integer right =>
                let operandType ← (CType.arithmeticConversion program.target leftType rightType).toOption
                return (resultType, .integer (← integerBinary program.target resultType operandType
                  operator left right))
            | .pointer pointer, .integer index =>
                if operator != .plus && operator != .minus then none
                let .ptr elementType := leftType | none
                let size ← sizeOf? program elementType
                let index := if operator = .minus then -index else index
                return (resultType, .pointer (← pointer.add? layout.layout size index))
            | .integer index, .pointer pointer =>
                if operator != .plus then none
                let .ptr elementType := rightType | none
                return (resultType, .pointer
                  (← pointer.add? layout.layout (← sizeOf? program elementType) index))
            | _, _ => none
        | .arrayDeref array index =>
            let (type, location) ← evalLValue layout environment
              (.e ⟨.arrayDeref array index, region⟩) state
            let value ← readLocation layout location state
            return (resultType, ← castValue program.target resultType value)
        | .deref value =>
            let (type, location) ← evalLValue layout environment
              (.e ⟨.deref value, region⟩) state
            let value ← readLocation layout location state
            return (resultType, ← castValue program.target resultType value)
        | .structDot value field =>
            let (type, location) ← evalLValue layout environment
              (.e ⟨.structDot value field, region⟩) state
            let value ← readLocation layout location state
            return (resultType, ← castValue program.target resultType value)
        | .typeCast _ value =>
            let (_, value) ← evalExpr layout environment value state
            return (resultType, ← castValue program.target resultType value)
        | .mkBool value =>
            let (_, value) ← evalExpr layout environment value state
            let truth : Bool := match value with
              | .integer value => decide (value ≠ 0)
              | .pointer pointer => decide (pointer ≠ Pointer.null)
              | .void => false
            return (resultType, .integer (if truth then 1 else 0))
        | .eFnCall .. => none
        | _ => none
  termination_by expression _ => (sizeOf expression, 1)
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  /-- Direct lvalue semantics over parser lvalue forms. -/
  def evalLValue {program : Program} (layout : MemoryLayout.Certificate program)
      (environment : Env) : CParser.Expr → State → Option (AnalyzedCType × Location)
    | .e ⟨node, region⟩, state => do
        let type ← expressionType? program (.e ⟨node, region⟩)
        match node with
        | .var name _ =>
            match environment.lookup name with
            | some binding => return (type, .slot binding.symbolId binding.type)
            | none =>
                let symbol ← globalSymbol? program name
                let pointer ← Pointer.ofGlobal? layout.layout symbol.id
                return (type, .memory pointer symbol.type)
        | .structDot base name =>
            let (baseType, location) ← evalLValue layout environment base state
            let .memory pointer _ := location | none
            let field ← field? program baseType name
            return (type, .memory (← offsetPointer? layout.layout pointer field.offset) field.type)
        | .arrayDeref array index =>
            let (arrayType, .pointer pointer) ← evalExpr layout environment array state | none
            let (_, .integer index) ← evalExpr layout environment index state | none
            let elementType ← match arrayType with
              | .array element _ | .ptr element => some element
              | _ => none
            let size ← sizeOf? program elementType
            return (type, .memory (← pointer.add? layout.layout size index) elementType)
        | .deref value =>
            let (pointerType, .pointer pointer) ← evalExpr layout environment value state | none
            let .ptr elementType := pointerType | none
            return (type, .memory pointer elementType)
        | _ => none
  termination_by expression _ => (sizeOf expression, 0)
  decreasing_by all_goals simp_wf <;> omega
end

def localBinding? (program : Program) (functionId : Nat)
    (declaration : Located Declaration) : Option Binding := do
  let .varDecl _ name [] _ _ := declaration.value | none
  let symbols := program.symbols.filter fun symbol =>
    symbol.sourceName = name.value && symbol.region = name.region &&
      symbol.kind = .local functionId
  let [symbol] := symbols | none
  if (scalarType program.target symbol.type).isSome || symbol.type.ptrType then
    some { name := name.value, symbolId := symbol.id, type := symbol.type }
  else none

inductive Outcome where
  | normal (state : State)
  | returned (state : State)
  | undefinedBehavior

mutual
  inductive StatementExec {program : Program} (layout : MemoryLayout.Certificate program)
      (functionId : Nat) (returnType : AnalyzedCType) :
      Statement → Env → State → Outcome → Prop where
    | assign
        (evaluation : evalExpr layout environment right state = some (rightType, value))
        (location : evalLValue layout environment left state = some (leftType, place))
        (stored : writeLocation layout place value state = some result) :
        StatementExec layout functionId returnType
          (.stmt ⟨.assign left right, region⟩) environment state (.normal result)
    | assignFault
        (failed : (do
          let (_, value) ← evalExpr layout environment right state
          let (_, place) ← evalLValue layout environment left state
          writeLocation layout place value state) = none) :
        StatementExec layout functionId returnType
          (.stmt ⟨.assign left right, region⟩) environment state .undefinedBehavior
    | block (execution : BodyExec layout functionId returnType items ([] :: environment) state outcome) :
        StatementExec layout functionId returnType (.stmt ⟨.block items, region⟩)
          environment state outcome
    | trap (execution : StatementExec layout functionId returnType body environment state outcome) :
        StatementExec layout functionId returnType (.stmt ⟨.trap kind body, region⟩)
          environment state outcome
    | ret
        (evaluation : evalExpr layout environment value state = some (type, result))
        (cast : castValue program.target returnType result = some returned) :
        StatementExec layout functionId returnType (.stmt ⟨.returnStmt (some value), region⟩)
          environment state (.returned (state.returnValue returned))
    | retVoid (typeEq : returnType = .void) :
        StatementExec layout functionId returnType (.stmt ⟨.returnStmt none, region⟩)
          environment state (.returned (state.returnValue .void))
    | retFault
        (failed : (evalExpr layout environment value state).bind
          (fun result => castValue program.target returnType result.2) = none) :
        StatementExec layout functionId returnType (.stmt ⟨.returnStmt (some value), region⟩)
          environment state .undefinedBehavior
    | condTrue
        (evaluation : evalExpr layout environment condition state = some (type, .integer value))
        (nonzero : value ≠ 0)
        (branch : StatementExec layout functionId returnType thenBranch environment state outcome) :
        StatementExec layout functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state outcome
    | condFalse
        (evaluation : evalExpr layout environment condition state = some (type, .integer 0))
        (branch : StatementExec layout functionId returnType elseBranch environment state outcome) :
        StatementExec layout functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state outcome
    | condFault
        (failed : (evalExpr layout environment condition state).bind (fun result =>
          match result.2 with | .integer value => some value | _ => none) = none) :
        StatementExec layout functionId returnType
          (.stmt ⟨.ifStmt condition thenBranch elseBranch, region⟩) environment state
          .undefinedBehavior
    | whileFalse
        (evaluation : evalExpr layout environment condition state = some (type, .integer 0)) :
        StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state (.normal state)
    | whileTrue
        (evaluation : evalExpr layout environment condition state = some (type, .integer value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec layout functionId returnType body environment state (.normal middle))
        (rest : StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment middle outcome) :
        StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state outcome
    | whileReturned
        (evaluation : evalExpr layout environment condition state = some (type, .integer value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec layout functionId returnType body environment state (.returned result)) :
        StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state (.returned result)
    | whileFault
        (evaluation : evalExpr layout environment condition state = some (type, .integer value))
        (nonzero : value ≠ 0)
        (iteration : StatementExec layout functionId returnType body environment state .undefinedBehavior) :
        StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state .undefinedBehavior
    | whileGuardFault
        (failed : (evalExpr layout environment condition state).bind (fun result =>
          match result.2 with | .integer value => some value | _ => none) = none) :
        StatementExec layout functionId returnType
          (.stmt ⟨.whileStmt condition invariant body, region⟩) environment state .undefinedBehavior
    | empty : StatementExec layout functionId returnType (.stmt ⟨.emptyStmt, region⟩)
        environment state (.normal state)

  inductive BodyExec {program : Program} (layout : MemoryLayout.Certificate program)
      (functionId : Nat) (returnType : AnalyzedCType) :
      List BlockItem → Env → State → Outcome → Prop where
    | nil : BodyExec layout functionId returnType [] environment state (.normal state)
    | statementNormal
        (first : StatementExec layout functionId returnType statement environment state (.normal middle))
        (rest : BodyExec layout functionId returnType items environment middle outcome) :
        BodyExec layout functionId returnType (.statement statement :: items) environment state outcome
    | statementReturned
        (first : StatementExec layout functionId returnType statement environment state (.returned result)) :
        BodyExec layout functionId returnType (.statement statement :: items) environment state
          (.returned result)
    | statementFault
        (first : StatementExec layout functionId returnType statement environment state .undefinedBehavior) :
        BodyExec layout functionId returnType (.statement statement :: items) environment state
          .undefinedBehavior
    | declaration
        (bindingEq : localBinding? program functionId
          ⟨.varDecl rawType name [] none attributes, region⟩ = some binding)
        (rest : BodyExec layout functionId returnType items (environment.bind binding)
          (state.clear binding.symbolId) outcome) :
        BodyExec layout functionId returnType
          (.declaration ⟨.varDecl rawType name [] none attributes, region⟩ :: items)
          environment state outcome
    | initialization
        (bindingEq : localBinding? program functionId
          ⟨.varDecl rawType name [] (some (.initE value)) attributes, region⟩ = some binding)
        (evaluation : evalExpr layout (environment.bind binding) value
          (state.clear binding.symbolId) = some (type, result))
        (cast : castValue program.target binding.type result = some stored)
        (rest : BodyExec layout functionId returnType items (environment.bind binding)
          ((state.clear binding.symbolId).write binding.symbolId stored) outcome) :
        BodyExec layout functionId returnType
          (.declaration ⟨.varDecl rawType name [] (some (.initE value)) attributes, region⟩ :: items)
          environment state outcome
    | initializationFault
        (bindingEq : localBinding? program functionId
          ⟨.varDecl rawType name [] (some (.initE value)) attributes, region⟩ = some binding)
        (failed : (evalExpr layout (environment.bind binding) value
          (state.clear binding.symbolId)).bind
            (fun result => castValue program.target binding.type result.2) = none) :
        BodyExec layout functionId returnType
          (.declaration ⟨.varDecl rawType name [] (some (.initE value)) attributes, region⟩ :: items)
          environment state .undefinedBehavior

end

def parameterEnv? (program : Program) (functionId : Nat) (ids : List Nat) : Option Env := do
  let bindings ← ids.mapM fun id => do
    let symbol ← program.symbolById? id
    if symbol.kind != .parameter functionId then none
    if !((scalarType program.target symbol.type).isSome || symbol.type.ptrType) then none
    return { name := symbol.sourceName, symbolId := id, type := symbol.type }
  return [bindings]

inductive FunctionOutcome where
  | success (state : State)
  | undefinedBehavior

inductive FunctionExec {program : Program} (layout : MemoryLayout.Certificate program)
    (name : String) (info : FunctionInfo) (rawBody : Body) : State → FunctionOutcome → Prop where
  | returned
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec layout info.symbolId info.returnType rawBody.value environment state.resetReturn
        (.returned result)) :
      FunctionExec layout name info rawBody state (.success result)
  | fault
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec layout info.symbolId info.returnType rawBody.value environment state.resetReturn
        .undefinedBehavior) :
      FunctionExec layout name info rawBody state .undefinedBehavior
  | fellOffVoid
      (typeEq : info.returnType = .void)
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec layout info.symbolId info.returnType rawBody.value environment state.resetReturn
        (.normal result)) :
      FunctionExec layout name info rawBody state (.success (result.returnValue .void))
  | fellOffMain
      (nameEq : name = "main") (typeEq : info.returnType = .signed .int)
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec layout info.symbolId info.returnType rawBody.value environment state.resetReturn
        (.normal result)) :
      FunctionExec layout name info rawBody state
        (.success (result.returnValue (.integer 0)))
  | fellOffFault
      (notVoid : info.returnType ≠ .void)
      (notMain : name ≠ "main" ∨ info.returnType ≠ .signed .int)
      (environmentEq : parameterEnv? program info.symbolId info.parameters = some environment)
      (body : BodyExec layout info.symbolId info.returnType rawBody.value environment state.resetReturn
        (.normal result)) :
      FunctionExec layout name info rawBody state .undefinedBehavior

end Raw

mutual
  inductive Expr where
    | literal (type : AnalyzedCType) (value : Int)
    | local (type : AnalyzedCType) (symbolId : Nat)
    | globalArray (type : AnalyzedCType) (pointer : Pointer)
    | load (type : AnalyzedCType) (location : LValue)
    | address (type : AnalyzedCType) (location : LValue)
    | cast (type : AnalyzedCType) (value : Expr)
    | unaryNot (type : AnalyzedCType) (value : Expr)
    | unaryNegate (type : AnalyzedCType) (value : Expr)
    | integerBinary (type operandType : AnalyzedCType) (operator : BinOpType)
        (left right : Expr)
    | pointerAdd (type elementType : AnalyzedCType) (subtract : Bool)
        (pointer index : Expr)
    | bool (type : AnalyzedCType) (value : Expr)
  deriving Repr, DecidableEq, Inhabited

  inductive LValue where
    | slot (type : AnalyzedCType) (symbolId : Nat)
    | global (type : AnalyzedCType) (pointer : Pointer)
    | field (type : AnalyzedCType) (base : LValue) (offset : Nat)
    | index (type elementType : AnalyzedCType) (array index : Expr)
    | deref (type : AnalyzedCType) (pointer : Expr)
  deriving Repr, DecidableEq, Inhabited
end

namespace Expr

def type : Expr → AnalyzedCType
  | .literal type _ | .local type _ | .globalArray type _ | .load type _ |
      .address type _ | .cast type _ | .unaryNot type _ | .unaryNegate type _ |
      .integerBinary type _ _ _ _ | .pointerAdd type _ _ _ _ | .bool type _ => type

end Expr

mutual
  def Expr.eval {program : Program} : Expr → MemoryLayout.Certificate program → State → Option Value
    | .literal type value, _, _ => return .integer (← castInteger program.target type value)
    | .local type symbolId, layout, state => do
        let value ← state.read? symbolId
        match type with
        | .array _ _ => some value
        | _ => castValue program.target type value
    | .globalArray _ pointer, _, _ => some (.pointer pointer)
    | .load type location, layout, state => do
        let location ← location.eval layout state
        let value ← readLocation layout location state
        castValue program.target type value
    | .address _ location, layout, state => do
        match ← location.eval layout state with
        | .memory pointer _ => some (.pointer pointer)
        | .slot .. => none
    | .cast type value, layout, state => do
        let value ← value.eval layout state
        castValue program.target type value
    | .unaryNot _ value, layout, state => do
        let .integer value ← value.eval layout state | none
        return .integer (if value = 0 then 1 else 0)
    | .unaryNegate type value, layout, state => do
        let .integer value ← value.eval layout state | none
        return .integer (← MemorySimpl.integerBinary program.target type type .minus 0 value)
    | .integerBinary type operandType operator left right, layout, state => do
        let .integer left ← left.eval layout state | none
        let .integer right ← right.eval layout state | none
        return .integer (← MemorySimpl.integerBinary program.target type operandType operator left right)
    | .pointerAdd _ elementType subtract pointer index, layout, state => do
        let .pointer pointer ← pointer.eval layout state | none
        let .integer index ← index.eval layout state | none
        let index := if subtract then -index else index
        return .pointer (← pointer.add? layout.layout (← sizeOf? program elementType) index)
    | .bool _ value, layout, state => do
        let value ← value.eval layout state
        let truth : Bool := match value with
          | .integer value => decide (value ≠ 0)
          | .pointer pointer => decide (pointer ≠ Pointer.null)
          | .void => false
        return .integer (if truth then 1 else 0)
  termination_by expression _ _ => sizeOf expression
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  def LValue.eval {program : Program} :
      LValue → MemoryLayout.Certificate program → State → Option Location
    | .slot type symbolId, _, _ => some (.slot symbolId type)
    | .global type pointer, _, _ => some (.memory pointer type)
    | .field type base offset, layout, state => do
        let .memory pointer _ ← base.eval layout state | none
        return .memory (← offsetPointer? layout.layout pointer offset) type
    | .index type elementType array index, layout, state => do
        let .pointer pointer ← array.eval layout state | none
        let .integer index ← index.eval layout state | none
        return .memory (← pointer.add? layout.layout (← sizeOf? program elementType) index) type
    | .deref type pointer, layout, state => do
        let .pointer pointer ← pointer.eval layout state | none
        return .memory pointer type
  termination_by location _ _ => sizeOf location
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

structure CheckedExpr {program : Program} (layout : MemoryLayout.Certificate program)
    (environment : Raw.Env) (raw : CParser.Expr) where
  ctype : AnalyzedCType
  expression : Expr
  type_eq : expressionType? program raw = some ctype
  correct : ∀ state, Raw.evalExpr layout environment raw state =
    (expression.eval layout state).map fun value => (ctype, value)

structure CheckedLValue {program : Program} (layout : MemoryLayout.Certificate program)
    (environment : Raw.Env) (raw : CParser.Expr) where
  ctype : AnalyzedCType
  location : LValue
  type_eq : expressionType? program raw = some ctype
  correct : ∀ state, Raw.evalLValue layout environment raw state =
    (location.eval layout state).map fun value => (ctype, value)

private def requireSome (error : Error) : Option α → Except Error α
  | some value => .ok value
  | none => .error error

private def checkedType {program : Program} (raw : CParser.Expr) : Except Error AnalyzedCType :=
  match expressionType? program raw with
  | some type => .ok type
  | none => .error (.malformedAnalysis "an expression has no unique analyzed type")

private def unsupportedExpr (raw : CParser.Expr) (description : String) : Except Error α :=
  match raw with | .e located => .error (.unsupportedExpression located.region description)

@[simp] private theorem option_bind_some_eq_map (value : Option α) (f : α → β) :
    value.bind (fun item => some (f item)) = value.map f := by
  cases value <;> rfl

@[simp] private theorem option_map_bind (value : Option α) (f : α → Option β) (g : β → γ) :
    (value.bind f).map g = value.bind fun item => (f item).map g := by
  cases value <;> rfl

private theorem evalExpr_global_scalar {program : Program}
    (layout : MemoryLayout.Certificate program) (environment : Raw.Env)
    (name : String) (info : VarInfo) (region : Region) (symbol : SymbolInfo)
    (pointer : Pointer)
    (typeEq : expressionType? program (.e ⟨.var name info, region⟩) = some symbol.type)
    (localEq : environment.lookup name = none)
    (globalEq : globalSymbol? program name = some symbol)
    (pointerEq : Pointer.ofGlobal? layout.layout symbol.id = some pointer)
    (supported : (scalarType program.target symbol.type).isSome = true) :
    ∀ state, Raw.evalExpr layout environment (.e ⟨.var name info, region⟩) state =
      ((Expr.load symbol.type (.global symbol.type pointer)).eval layout state).map
        fun value => (symbol.type, value) := by
  intro state
  cases typeCase : symbol.type <;>
    simp_all [Raw.evalExpr, scalarType, Function.comp_def, Expr.eval, LValue.eval]

set_option maxHeartbeats 400000 in
mutual
  private def checkExpr {program : Program}
      (layout : MemoryLayout.Certificate program) (environment : Raw.Env) :
      (raw : CParser.Expr) → Except Error (CheckedExpr layout environment raw)
    | .e ⟨node, region⟩ =>
      match typeEq : expressionType? program (.e ⟨node, region⟩) with
      | none => .error (.malformedAnalysis "an expression has no analyzed type")
      | some resultType =>
        match node with
        | .constant ⟨.numConst info, _⟩ =>
            match integerEq : scalarType program.target resultType with
            | none => .error (.unsupportedType region resultType)
            | some _ => .ok {
                ctype := resultType
                expression := .literal resultType info.value
                type_eq := typeEq
                correct := by
                  intro state
                  generalize castEq : castInteger program.target resultType info.value = cast
                  cases cast <;> simp [Raw.evalExpr, typeEq, Expr.eval, castEq] }
        | .var name _ =>
            match localEq : environment.lookup name with
            | some binding =>
                if same : resultType = binding.type then
                  .ok {
                    ctype := resultType
                    expression := .local resultType binding.symbolId
                    type_eq := typeEq
                    correct := by
                      intro state
                      subst resultType
                      generalize readEq : state.read? binding.symbolId = read
                      generalize bindingTypeEq : binding.type = bindingType at *
                      cases read <;> cases bindingType <;>
                        simp_all [Raw.evalExpr, localEq, Function.comp_def, Expr.eval] }
                else .error (.malformedAnalysis s!"local {name} has inconsistent expression type")
            | none =>
                match globalEq : globalSymbol? program name with
                | none => .error (.unresolvedIdentifier region name)
                | some symbol =>
                    if same : resultType = symbol.type then
                      match symbolTypeEq : symbol.type with
                      | .array element count =>
                          match pointerEq : Pointer.ofGlobal? layout.layout symbol.id with
                          | none => .error (missingGlobalStorageError program region symbol)
                          | some pointer => .ok {
                              ctype := resultType
                              expression := .globalArray resultType pointer
                              type_eq := typeEq
                              correct := by
                                intro state
                                subst resultType
                                simp [Raw.evalExpr, typeEq, localEq, globalEq, pointerEq,
                                  symbolTypeEq, Function.comp_def, Expr.eval] }
                      | _ =>
                          match pointerEq : Pointer.ofGlobal? layout.layout symbol.id with
                          | none => .error (missingGlobalStorageError program region symbol)
                          | some pointer =>
                              if supported : scalarType program.target symbol.type |>.isSome then
                                .ok {
                                  ctype := resultType
                                  expression := .load resultType (.global symbol.type pointer)
                                  type_eq := typeEq
                                  correct := by
                                    intro state
                                    subst resultType
                                    exact evalExpr_global_scalar layout environment name _ region
                                      symbol pointer typeEq localEq globalEq pointerEq supported state }
                              else .error (.unsupportedType region symbol.type)
                    else .error (.malformedAnalysis s!"global {name} has inconsistent expression type")
        | .unOp .addr value =>
            match checkedEq : checkLValue layout environment value with
            | .error error => .error error
            | .ok checked@⟨_, .slot .., _, _⟩ =>
                .error (.localAddress region)
            | .ok checked =>
                if typeSame : resultType = .ptr checked.ctype then
                  .ok {
                    ctype := resultType
                    expression := .address resultType checked.location
                    type_eq := typeEq
                    correct := by
                      intro state
                      subst resultType
                      simp only [Raw.evalExpr, typeEq, Option.bind_some]
                      rw [checked.correct]
                      generalize evalEq : checked.location.eval layout state = evaluated
                      cases evaluated with
                      | none => simp [evalEq, Expr.eval]
                      | some location => cases location <;> simp [evalEq, Expr.eval] }
                else .error (.malformedAnalysis "address expression type disagrees with its lvalue")
        | .unOp .not value =>
            match checkedEq : checkExpr layout environment value with
            | .error error => .error error
            | .ok checked =>
              if (scalarType program.target checked.ctype).isNone then
                .error (.unsupportedExpression region "logical not of non-integer value")
              else .ok {
                ctype := resultType
                expression := .unaryNot resultType checked.expression
                type_eq := typeEq
                correct := by
                  intro state
                  simp only [Raw.evalExpr, typeEq, Option.bind_some]
                  rw [checked.correct]
                  generalize evalEq : checked.expression.eval layout state = evaluated
                  cases evaluated with
                  | none => simp [evalEq, Expr.eval]
                  | some value =>
                    cases value with
                    | integer value => simp [evalEq, Expr.eval]
                    | pointer pointer => simp [evalEq, Expr.eval]
                    | void => simp [evalEq, Expr.eval] }
        | .unOp .negate value =>
            match checkedEq : checkExpr layout environment value with
            | .error error => .error error
            | .ok checked =>
                if same : checked.ctype = resultType then .ok {
                  ctype := resultType
                  expression := .unaryNegate resultType checked.expression
                  type_eq := typeEq
                  correct := by
                    intro state
                    simp only [Raw.evalExpr, typeEq, Option.bind_some]
                    rw [checked.correct]
                    generalize evalEq : checked.expression.eval layout state = evaluated
                    cases evaluated with
                    | none => simp [evalEq, Expr.eval]
                    | some value => cases value <;> simp [evalEq, Function.comp_def, Expr.eval] }
                else .error (.unsupportedExpression region "unary promotion outside the exact memory slice")
        | .binOp operator left right =>
            match leftEq : checkExpr layout environment left,
                rightEq : checkExpr layout environment right with
            | .error error, _ | _, .error error => .error error
            | .ok leftChecked, .ok rightChecked =>
                match leftTypeEq : leftChecked.ctype, rightTypeEq : rightChecked.ctype with
                | .ptr elementType, rightType =>
                    if supported : (scalarType program.target rightType).isNone ||
                        (operator != .plus && operator != .minus) then
                      .error (.unsupportedExpression region "unsupported pointer operator")
                    else if bounded : !(match leftChecked.expression with
                        | .globalArray .. => true | _ => false) then
                      .error (.unsupportedExpression region
                        "pointer arithmetic requires certified top-level array bounds")
                    else if same : resultType = .ptr elementType then .ok {
                      ctype := resultType
                      expression := .pointerAdd resultType elementType (operator = .minus)
                        leftChecked.expression rightChecked.expression
                      type_eq := typeEq
                      correct := by
                        intro state
                        simp only [Raw.evalExpr, typeEq, Option.bind_some]
                        rw [leftChecked.correct, rightChecked.correct]
                        subst resultType
                        cases expressionEq : leftChecked.expression <;>
                          simp_all [Function.comp_def, Expr.eval]
                        generalize leftEq : leftChecked.expression.eval layout state = leftResult
                        generalize rightEq : rightChecked.expression.eval layout state = rightResult
                        cases leftResult with
                        | none => simp [expressionEq, Expr.eval] at leftEq
                        | some leftValue =>
                          cases rightResult with
                          | none => simp [expressionEq, leftEq, rightEq, Expr.eval]
                          | some rightValue =>
                            cases leftValue <;> cases rightValue <;>
                              simp_all [leftEq, rightEq, Function.comp_def, Expr.eval]
                            all_goals split <;> simp_all }
                    else .error (.malformedAnalysis "pointer result type mismatch")
                | leftType, .ptr elementType =>
                    if supported : (scalarType program.target leftType).isNone || operator != .plus then
                      .error (.unsupportedExpression region "unsupported reversed pointer operator")
                    else if bounded : !(match rightChecked.expression with
                        | .globalArray .. => true | _ => false) then
                      .error (.unsupportedExpression region
                        "pointer arithmetic requires certified top-level array bounds")
                    else if same : resultType = .ptr elementType then .ok {
                      ctype := resultType
                      expression := .pointerAdd resultType elementType false
                        rightChecked.expression leftChecked.expression
                      type_eq := typeEq
                      correct := by
                        intro state
                        simp only [Raw.evalExpr, typeEq, Option.bind_some]
                        rw [leftChecked.correct, rightChecked.correct]
                        subst resultType
                        cases expressionEq : rightChecked.expression <;>
                          simp_all [Function.comp_def, Expr.eval]
                        generalize leftEq : leftChecked.expression.eval layout state = leftResult
                        generalize rightEq : rightChecked.expression.eval layout state = rightResult
                        cases leftResult with
                        | none => simp [expressionEq, leftEq, Expr.eval]
                        | some leftValue =>
                          cases rightResult with
                          | none => simp [expressionEq, Expr.eval] at rightEq
                          | some rightValue =>
                            cases leftValue <;> cases rightValue <;>
                              simp_all [leftEq, rightEq, Function.comp_def, Expr.eval] }
                    else .error (.malformedAnalysis "pointer result type mismatch")
                | leftType, rightType =>
                    if !implementedIntegerOperator operator then
                      .error (.unsupportedExpression region "integer operator is not implemented")
                    else if pointerTypes : leftType.ptrType || rightType.ptrType then
                      .error (.unsupportedExpression region "non-integer binary operands")
                    else match conversionEq : CType.arithmeticConversion program.target leftType rightType with
                    | .error _ => .error (.unsupportedExpression region "non-integer binary operands")
                    | .ok operandType =>
                        if scalarType program.target resultType |>.isNone then
                          .error (.unsupportedType region resultType)
                        else .ok {
                          ctype := resultType
                          expression := .integerBinary resultType operandType operator
                            leftChecked.expression rightChecked.expression
                          type_eq := typeEq
                          correct := by
                            intro state
                            simp only [Raw.evalExpr, typeEq, Option.bind_some]
                            rw [leftChecked.correct, rightChecked.correct]
                            generalize leftEq : leftChecked.expression.eval layout state = leftResult
                            generalize rightEq : rightChecked.expression.eval layout state = rightResult
                            simp only [Expr.eval]
                            rw [leftEq, rightEq]
                            cases leftResult with
                            | none => simp [leftEq, Expr.eval]
                            | some leftValue =>
                              cases rightResult with
                              | none => cases leftValue <;> simp [leftEq, rightEq, Expr.eval]
                              | some rightValue =>
                                cases leftValue with
                                | integer leftValue =>
                                  cases rightValue with
                                  | integer rightValue =>
                                    simp [leftTypeEq, rightTypeEq, conversionEq,
                                      Except.toOption, Function.comp_def, Expr.eval]
                                  | pointer rightValue =>
                                    cases rightType <;>
                                      simp_all [CType.ptrType, Function.comp_def, Expr.eval]
                                  | void => simp [Expr.eval]
                                | pointer leftValue =>
                                  cases rightValue with
                                  | integer rightValue =>
                                    cases leftType <;>
                                      simp_all [CType.ptrType, Function.comp_def, Expr.eval]
                                  | pointer rightValue => simp [Expr.eval]
                                  | void => simp [Expr.eval]
                                | void => simp [Expr.eval] }
        | .arrayDeref array index =>
            match checkedEq : checkLValue layout environment
                (.e ⟨.arrayDeref array index, region⟩) with
            | .error error => .error error
            | .ok checked =>
                if scalarType program.target resultType |>.isSome then .ok {
                  ctype := resultType
                  expression := .load resultType checked.location
                  type_eq := typeEq
                  correct := by
                    intro state
                    simp only [Raw.evalExpr, typeEq, Option.bind_some]
                    rw [checked.correct]
                    generalize evalEq : checked.location.eval layout state = evaluated
                    cases evaluated with
                    | none => simp [evalEq, Expr.eval]
                    | some location =>
                      cases location <;>
                        simp [evalEq, Function.comp_def, Expr.eval] }
                else .error (.unsupportedType region resultType)
        | .deref value =>
            match checkedEq : checkLValue layout environment (.e ⟨.deref value, region⟩) with
            | .error error => .error error
            | .ok checked =>
                if scalarType program.target resultType |>.isSome then .ok {
                  ctype := resultType
                  expression := .load resultType checked.location
                  type_eq := typeEq
                  correct := by
                    intro state
                    simp only [Raw.evalExpr, typeEq, Option.bind_some]
                    rw [checked.correct]
                    generalize evalEq : checked.location.eval layout state = evaluated
                    cases evaluated with
                    | none => simp [evalEq, Expr.eval]
                    | some location =>
                      cases location <;>
                        simp [evalEq, Function.comp_def, Expr.eval] }
                else .error (.unsupportedType region resultType)
        | .structDot value field =>
            match checkedEq : checkLValue layout environment
                (.e ⟨.structDot value field, region⟩) with
            | .error error => .error error
            | .ok checked =>
                if scalarType program.target resultType |>.isSome then .ok {
                  ctype := resultType
                  expression := .load resultType checked.location
                  type_eq := typeEq
                  correct := by
                    intro state
                    simp only [Raw.evalExpr, typeEq, Option.bind_some]
                    rw [checked.correct]
                    generalize evalEq : checked.location.eval layout state = evaluated
                    cases evaluated with
                    | none => simp [evalEq, Expr.eval]
                    | some location =>
                      cases location <;>
                        simp [evalEq, Function.comp_def, Expr.eval] }
                else .error (.unsupportedType region resultType)
        | .typeCast _ value =>
            match checkedEq : checkExpr layout environment value with
            | .error error => .error error
            | .ok checked =>
              if !(checked.ctype.integerType && resultType.integerType) &&
                  !(checked.ctype.ptrType && resultType.ptrType) then
                .error (.unsupportedExpression region "cross-representation cast is not implemented")
              else .ok {
                ctype := resultType
                expression := .cast resultType checked.expression
                type_eq := typeEq
                correct := by
                  intro state
                  simp only [Raw.evalExpr, typeEq, Option.bind_some]
                  rw [checked.correct]
                  generalize evalEq : checked.expression.eval layout state = evaluated
                  cases evaluated <;> simp_all [evalEq, Expr.eval] }
        | .mkBool value =>
            match checkedEq : checkExpr layout environment value with
            | .error error => .error error
            | .ok checked => .ok {
                ctype := resultType
                expression := .bool resultType checked.expression
                type_eq := typeEq
                correct := by
                  intro state
                  simp only [Raw.evalExpr, typeEq, Option.bind_some]
                  rw [checked.correct]
                  generalize evalEq : checked.expression.eval layout state = evaluated
                  cases evaluated with
                  | none => simp [evalEq, Expr.eval]
                  | some value =>
                    cases value with
                    | integer value => simp [evalEq, Expr.eval]
                    | pointer pointer => simp [evalEq, Expr.eval]
                    | void => simp [evalEq, Expr.eval] }
        | .eFnCall .. => .error (.directCall region)
        | .constant ⟨.stringLit _, _⟩ | .unOp .bitNegate _ | .condExp .. |
            .sizeof _ | .sizeofTy _ | .compLiteral .. | .arbitrary _ =>
          .error (.unsupportedExpression region "expression outside certified memory slice")
  termination_by raw => (sizeOf raw, 1)
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def checkLValue {program : Program}
      (layout : MemoryLayout.Certificate program) (environment : Raw.Env) :
      (raw : CParser.Expr) → Except Error (CheckedLValue layout environment raw)
    | .e ⟨node, region⟩ =>
      match typeEq : expressionType? program (.e ⟨node, region⟩) with
      | none => .error (.malformedAnalysis "an lvalue has no analyzed type")
      | some resultType =>
        match node with
        | .var name _ =>
            match localEq : environment.lookup name with
            | some binding =>
                if same : resultType = binding.type then .ok {
                  ctype := resultType
                  location := .slot binding.type binding.symbolId
                  type_eq := typeEq
                  correct := by
                    intro state
                    subst resultType
                    simp [Raw.evalLValue, typeEq, localEq, LValue.eval] }
                else .error (.malformedAnalysis s!"local lvalue {name} has inconsistent type")
            | none =>
                match globalEq : globalSymbol? program name,
                    pointerEq : (globalSymbol? program name).bind
                      (Pointer.ofGlobal? layout.layout ∘ SymbolInfo.id) with
                | some symbol, some pointer =>
                    if same : resultType = symbol.type then .ok {
                      ctype := resultType
                      location := .global symbol.type pointer
                      type_eq := typeEq
                      correct := by
                        intro state
                        subst resultType
                        simp [Raw.evalLValue, typeEq, localEq, globalEq] at pointerEq ⊢
                        simp [pointerEq, LValue.eval] }
                    else .error (.malformedAnalysis s!"global lvalue {name} has inconsistent type")
                | some symbol, none => .error (missingGlobalStorageError program region symbol)
                | none, _ => .error (.unresolvedIdentifier region name)
        | .structDot base name =>
            match baseEq : checkLValue layout environment base with
            | .error error => .error error
            | .ok checked =>
                match fieldEq : field? program checked.ctype name with
                | none => .error (.unsupportedExpression region s!"unknown field {name}")
                | some field =>
                    if scalarType program.target field.type |>.isNone then
                      .error (.unsupportedType region field.type)
                    else if same : resultType = field.type then .ok {
                      ctype := resultType
                      location := .field field.type checked.location field.offset
                      type_eq := typeEq
                      correct := by
                        intro state
                        subst resultType
                        simp only [Raw.evalLValue, typeEq, Option.bind_some]
                        rw [checked.correct]
                        generalize evalEq : checked.location.eval layout state = evaluated
                        cases evaluated with
                        | none => simp [evalEq, LValue.eval]
                        | some location =>
                          cases location <;>
                            simp [evalEq, fieldEq, Function.comp_def, LValue.eval] }
                    else .error (.malformedAnalysis "field lvalue type mismatch")
        | .arrayDeref array index =>
            match arrayEq : checkExpr layout environment array,
                indexEq : checkExpr layout environment index with
            | .error error, _ | _, .error error => .error error
            | .ok arrayChecked, .ok indexChecked =>
                match arrayTypeEq : arrayChecked.ctype with
                | .array elementType _ =>
                    if scalarType program.target elementType |>.isNone then
                      .error (.unsupportedType region elementType)
                    else if !indexChecked.ctype.integerType then
                      .error (.unsupportedExpression region "non-integer array index")
                    else if same : resultType = elementType then .ok {
                      ctype := resultType
                      location := .index elementType elementType arrayChecked.expression
                        indexChecked.expression
                      type_eq := typeEq
                      correct := by
                        intro state
                        subst resultType
                        simp only [Raw.evalLValue, typeEq, Option.bind_some]
                        rw [arrayChecked.correct, indexChecked.correct]
                        rw [arrayTypeEq]
                        generalize arrayEq : arrayChecked.expression.eval layout state = arrayResult
                        generalize indexEq : indexChecked.expression.eval layout state = indexResult
                        cases arrayResult with
                        | none => simp [arrayEq, LValue.eval]
                        | some arrayValue =>
                          cases indexResult with
                          | none => cases arrayValue <;> simp [arrayEq, indexEq, LValue.eval]
                          | some indexValue =>
                            cases arrayValue <;> cases indexValue <;>
                              simp_all [arrayEq, indexEq, arrayTypeEq,
                                Function.comp_def, LValue.eval] }
                    else .error (.malformedAnalysis "array element type mismatch")
                | .ptr _ =>
                    .error (.unsupportedExpression region
                      "pointer indexing requires certified subobject bounds")
                | _ => .error (.unsupportedExpression region "indexing non-array value")
        | .deref pointer =>
            match pointerEq : checkExpr layout environment pointer with
            | .error error => .error error
            | .ok checked =>
                match pointerTypeEq : checked.ctype with
                | .ptr elementType =>
                    if scalarType program.target elementType |>.isNone then
                      .error (.unsupportedType region elementType)
                    else if same : resultType = elementType then .ok {
                      ctype := resultType
                      location := .deref elementType checked.expression
                      type_eq := typeEq
                      correct := by
                        intro state
                        subst resultType
                        simp only [Raw.evalLValue, typeEq, Option.bind_some]
                        rw [checked.correct]
                        generalize evalEq : checked.expression.eval layout state = evaluated
                        cases evaluated with
                        | none => simp [evalEq, LValue.eval]
                        | some value =>
                          cases value <;> simp [evalEq, pointerTypeEq, LValue.eval] }
                    else .error (.malformedAnalysis "dereference type mismatch")
                | _ => .error (.unsupportedExpression region "dereferencing non-pointer")
        | .binOp .. | .unOp .. | .condExp .. | .constant _ | .typeCast .. |
            .sizeof _ | .sizeofTy _ | .eFnCall .. | .compLiteral .. | .arbitrary _ |
            .mkBool _ =>
          .error (.unsupportedExpression region "expression is not a supported lvalue")
  termination_by raw => (sizeOf raw, 0)
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

inductive Stmt where
  | skip
  | seq (first second : Stmt)
  | assign (location : LValue) (value : Expr)
  | declare (symbolId : Nat) (type : AnalyzedCType) (initializer : Option Expr)
  | return (type : AnalyzedCType) (value : Option Expr)
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
  | .seq first second => first.declaredIds ++ second.declaredIds
  | .declare symbolId _ _ => [symbolId]
  | .cond _ left right => left.declaredIds ++ right.declaredIds
  | .while _ body => body.declaredIds

def assign? {program : Program} (layout : MemoryLayout.Certificate program)
    (location : LValue) (value : Expr) (state : State) : Option State := do
  let value ← value.eval layout state
  let location ← location.eval layout state
  writeLocation layout location value state

def initialize? {program : Program} (layout : MemoryLayout.Certificate program)
    (symbolId : Nat) (type : AnalyzedCType) (value : Expr) (state : State) : Option State := do
  let value ← value.eval layout (state.clear symbolId)
  return (state.clear symbolId).write symbolId (← castValue program.target type value)

def return? {program : Program} (layout : MemoryLayout.Certificate program)
    (type : AnalyzedCType) (value : Option Expr) (state : State) : Option State :=
  match value with
  | none => match type with
      | .void => some (state.returnValue .void)
      | _ => none
  | some value => do
      let value ← value.eval layout state
      return state.returnValue (← castValue program.target type value)

inductive Exec {program : Program} (layout : MemoryLayout.Certificate program) :
    Stmt → State → Outcome → Prop where
  | skip : Exec layout .skip state (.normal state)
  | seqNormal : Exec layout first state (.normal middle) → Exec layout second middle outcome →
      Exec layout (.seq first second) state outcome
  | seqReturned : Exec layout first state (.returned result) →
      Exec layout (.seq first second) state (.returned result)
  | seqFault : Exec layout first state .fault → Exec layout (.seq first second) state .fault
  | assign (evaluation : assign? layout location value state = some result) :
      Exec layout (.assign location value) state (.normal result)
  | assignFault (evaluation : assign? layout location value state = none) :
      Exec layout (.assign location value) state .fault
  | declare : Exec layout (.declare symbolId type none) state (.normal (state.clear symbolId))
  | initialize (evaluation : initialize? layout symbolId type value state = some result) :
      Exec layout (.declare symbolId type (some value)) state (.normal result)
  | initializeFault (evaluation : initialize? layout symbolId type value state = none) :
      Exec layout (.declare symbolId type (some value)) state .fault
  | ret (evaluation : return? layout type value state = some result) :
      Exec layout (.return type value) state (.returned result)
  | retFault (evaluation : return? layout type value state = none) :
      Exec layout (.return type value) state .fault
  | condTrue (evaluation : condition.eval layout state = some (.integer value))
      (nonzero : value ≠ 0) (branch : Exec layout thenStmt state outcome) :
      Exec layout (.cond condition thenStmt elseStmt) state outcome
  | condFalse (evaluation : condition.eval layout state = some (.integer 0))
      (branch : Exec layout elseStmt state outcome) :
      Exec layout (.cond condition thenStmt elseStmt) state outcome
  | condFault (failed : (condition.eval layout state).bind
      (fun value => match value with | .integer value => some value | _ => none) = none) :
      Exec layout (.cond condition thenStmt elseStmt) state .fault
  | whileFalse (evaluation : condition.eval layout state = some (.integer 0)) :
      Exec layout (.while condition body) state (.normal state)
  | whileTrue (evaluation : condition.eval layout state = some (.integer value))
      (nonzero : value ≠ 0) (iteration : Exec layout body state (.normal middle))
      (rest : Exec layout (.while condition body) middle outcome) :
      Exec layout (.while condition body) state outcome
  | whileReturned (evaluation : condition.eval layout state = some (.integer value))
      (nonzero : value ≠ 0) (iteration : Exec layout body state (.returned result)) :
      Exec layout (.while condition body) state (.returned result)
  | whileFault (evaluation : condition.eval layout state = some (.integer value))
      (nonzero : value ≠ 0) (iteration : Exec layout body state .fault) :
      Exec layout (.while condition body) state .fault
  | whileGuardFault (failed : (condition.eval layout state).bind
      (fun value => match value with | .integer value => some value | _ => none) = none) :
      Exec layout (.while condition body) state .fault

end Stmt

mutual
  inductive CheckedStatement {program : Program} (layout : MemoryLayout.Certificate program)
      (functionId : Nat) (returnType : AnalyzedCType) :
      Statement → Raw.Env → Stmt → Prop where
    | assign (left : CheckedLValue layout environment rawLeft)
        (right : CheckedExpr layout environment rawRight) :
        CheckedStatement layout functionId returnType
          (.stmt ⟨.assign rawLeft rawRight, region⟩) environment
          (.assign left.location right.expression)
    | block (body : CheckedBody layout functionId returnType items
        ([] :: environment) resolved) :
        CheckedStatement layout functionId returnType (.stmt ⟨.block items, region⟩)
          environment (.seq resolved .skip)
    | trap (body : CheckedStatement layout functionId returnType raw environment resolved) :
        CheckedStatement layout functionId returnType (.stmt ⟨.trap kind raw, region⟩)
          environment (.seq resolved .skip)
    | ret (value : CheckedExpr layout environment rawValue) :
        CheckedStatement layout functionId returnType
          (.stmt ⟨.returnStmt (some rawValue), region⟩) environment
          (.return returnType (some value.expression))
    | retVoid (typeEq : returnType = .void) :
        CheckedStatement layout functionId returnType (.stmt ⟨.returnStmt none, region⟩)
          environment (.return returnType none)
    | cond (condition : CheckedExpr layout environment rawCondition)
        (thenBranch : CheckedStatement layout functionId returnType rawThen environment thenStmt)
        (elseBranch : CheckedStatement layout functionId returnType rawElse environment elseStmt) :
        CheckedStatement layout functionId returnType
          (.stmt ⟨.ifStmt rawCondition rawThen rawElse, region⟩) environment
          (.cond condition.expression thenStmt elseStmt)
    | while (condition : CheckedExpr layout environment rawCondition)
        (body : CheckedStatement layout functionId returnType rawBody environment resolvedBody) :
        CheckedStatement layout functionId returnType
          (.stmt ⟨.whileStmt rawCondition invariant rawBody, region⟩) environment
          (.while condition.expression resolvedBody)
    | empty : CheckedStatement layout functionId returnType (.stmt ⟨.emptyStmt, region⟩)
        environment .skip

  inductive CheckedBody {program : Program} (layout : MemoryLayout.Certificate program)
      (functionId : Nat) (returnType : AnalyzedCType) :
      List BlockItem → Raw.Env → Stmt → Prop where
    | nil : CheckedBody layout functionId returnType [] environment .skip
    | statement
        (first : CheckedStatement layout functionId returnType raw environment resolved)
        (rest : CheckedBody layout functionId returnType items environment resolvedRest) :
        CheckedBody layout functionId returnType (.statement raw :: items) environment
          (.seq resolved resolvedRest)
    | declaration
        (bindingEq : Raw.localBinding? program functionId
          ⟨.varDecl rawType name [] none attributes, region⟩ = some binding)
        (rest : CheckedBody layout functionId returnType items (environment.bind binding) resolvedRest) :
        CheckedBody layout functionId returnType
          (.declaration ⟨.varDecl rawType name [] none attributes, region⟩ :: items) environment
          (.seq (.declare binding.symbolId binding.type none) resolvedRest)
    | initialization
        (declarationEq : declaration =
          ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩)
        (bindingEq : Raw.localBinding? program functionId declaration = some binding)
        (value : CheckedExpr layout (environment.bind binding) rawValue)
        (rest : CheckedBody layout functionId returnType items
          (environment.bind binding) resolvedRest) :
        CheckedBody layout functionId returnType (.declaration declaration :: items) environment
          (.seq (.declare binding.symbolId binding.type (some value.expression)) resolvedRest)
end

private structure CheckedStatementRun {program : Program}
    (layout : MemoryLayout.Certificate program) (functionId : Nat)
    (returnType : AnalyzedCType) (raw : Statement) (environment : Raw.Env) where
  statement : Stmt
  evidence : CheckedStatement layout functionId returnType raw environment statement

private structure CheckedBodyRun {program : Program}
    (layout : MemoryLayout.Certificate program) (functionId : Nat)
    (returnType : AnalyzedCType) (raw : List BlockItem) (environment : Raw.Env) where
  statement : Stmt
  evidence : CheckedBody layout functionId returnType raw environment statement

mutual
  private def checkStatement {program : Program}
      (layout : MemoryLayout.Certificate program) (functionId : Nat)
      (returnType : AnalyzedCType) (environment : Raw.Env) :
      (raw : Statement) → Except Error (CheckedStatementRun layout functionId returnType raw environment)
    | raw@(.stmt ⟨node, region⟩) =>
        match nodeEq : node with
        | .assign left right => do
            let left ← checkLValue layout environment left
            let right ← checkExpr layout environment right
            if !representationCompatible program.target left.ctype right.ctype then
              .error (.unsupportedExpression region "assignment crosses value representations")
            match left.location with
            | .global type _ =>
                if (scalarType program.target type).isNone then
                  .error (.unsupportedType region type)
                else .ok ()
            | _ => .ok ()
            return {
              statement := .assign left.location right.expression
              evidence := by cases nodeEq; exact .assign left right }
        | .block items => do
            let body ← checkBody layout functionId returnType ([] :: environment) items
            return {
              statement := .seq body.statement .skip
              evidence := by cases nodeEq; exact .block body.evidence }
        | .trap kind body => do
            let body ← checkStatement layout functionId returnType environment body
            return {
              statement := .seq body.statement .skip
              evidence := by cases nodeEq; exact .trap body.evidence }
        | .returnStmt (some value) => do
            let value ← checkExpr layout environment value
            if !representationCompatible program.target returnType value.ctype then
              .error (.unsupportedExpression region "return crosses value representations")
            return {
              statement := .return returnType (some value.expression)
              evidence := by cases nodeEq; exact .ret value }
        | .returnStmt none =>
            if typeEq : returnType = .void then .ok {
              statement := .return returnType none
              evidence := by cases nodeEq; exact .retVoid typeEq }
            else .error (.unsupportedStatement region "empty return in non-void function")
        | .ifStmt condition thenBranch elseBranch => do
            let condition ← checkExpr layout environment condition
            if (scalarType program.target condition.ctype).isNone then
              .error (.unsupportedExpression region "non-integer condition")
            let thenBranch ← checkStatement layout functionId returnType environment thenBranch
            let elseBranch ← checkStatement layout functionId returnType environment elseBranch
            return {
              statement := .cond condition.expression thenBranch.statement elseBranch.statement
              evidence := by
                cases nodeEq
                exact .cond condition thenBranch.evidence elseBranch.evidence }
        | .whileStmt condition invariant body => do
            let condition ← checkExpr layout environment condition
            if (scalarType program.target condition.ctype).isNone then
              .error (.unsupportedExpression region "non-integer loop condition")
            let body ← checkStatement layout functionId returnType environment body
            return {
              statement := .while condition.expression body.statement
              evidence := by cases nodeEq; exact .while condition body.evidence }
        | .emptyStmt => .ok {
            statement := .skip
            evidence := by cases nodeEq; exact .empty }
        | .assignFnCall .. | .embeddedFnCall .. | .returnFnCall .. => .error (.directCall region)
        | _ => .error (.unsupportedStatement region "statement outside certified memory slice")

  private def checkBody {program : Program}
      (layout : MemoryLayout.Certificate program) (functionId : Nat)
      (returnType : AnalyzedCType) (environment : Raw.Env) :
      (raw : List BlockItem) → Except Error (CheckedBodyRun layout functionId returnType raw environment)
    | [] => .ok { statement := .skip, evidence := .nil }
    | .statement raw :: items => do
        let first ← checkStatement layout functionId returnType environment raw
        let rest ← checkBody layout functionId returnType environment items
        return {
          statement := .seq first.statement rest.statement
          evidence := .statement first.evidence rest.evidence }
    | .declaration declaration :: items =>
        match declarationEq : declaration.value with
        | .varDecl rawType name [] none attributes =>
            match bindingEq : Raw.localBinding? program functionId declaration with
            | none => .error (.unsupportedStatement declaration.region "unsupported local object")
            | some binding => do
                let rest ← checkBody layout functionId returnType (environment.bind binding) items
                return {
                  statement := .seq (.declare binding.symbolId binding.type none) rest.statement
                  evidence := by
                    cases declaration with
                    | mk declaration region =>
                        have fullEq : Located.mk declaration region =
                            ⟨.varDecl rawType name [] none attributes, region⟩ :=
                          congrArg (fun value => Located.mk value region) declarationEq
                        cases fullEq
                        exact .declaration bindingEq rest.evidence }
        | .varDecl rawType name [] (some (.initE rawValue)) attributes =>
            match bindingEq : Raw.localBinding? program functionId declaration with
            | none => .error (.unsupportedStatement declaration.region
                "unsupported initialized local object")
            | some binding => do
                let value ← checkExpr layout (environment.bind binding) rawValue
                if !representationCompatible program.target binding.type value.ctype then
                  .error (.unsupportedExpression declaration.region
                    "initializer crosses value representations")
                let rest ← checkBody layout functionId returnType (environment.bind binding) items
                return {
                  statement := .seq
                    (.declare binding.symbolId binding.type (some value.expression)) rest.statement
                  evidence := by
                    cases declaration with
                    | mk declaration region =>
                        have fullEq : Located.mk declaration region =
                            ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩ :=
                          congrArg (fun value => Located.mk value region) declarationEq
                        cases fullEq
                        exact .initialization rfl bindingEq value rest.evidence }
        | .varDecl _ _ (_ :: _) _ _ =>
            .error (.unsupportedStatement declaration.region "local storage classes are unsupported")
        | _ => .error (.unsupportedStatement declaration.region "unsupported local declaration")
end

private def embedStatementOutcome : Raw.Outcome → Outcome
  | .normal state => .normal state
  | .returned state => .returned state
  | .undefinedBehavior => .fault

private theorem embedStatementOutcome_injective : Function.Injective embedStatementOutcome := by
  intro left right
  cases left <;> cases right <;> simp_all [embedStatementOutcome]

private theorem raw_normal_of_embed_eq
    (equality : Outcome.normal state = embedStatementOutcome rawOutcome) :
    rawOutcome = .normal state := by
  cases rawOutcome <;> simp_all [embedStatementOutcome]

private theorem raw_returned_of_embed_eq
    (equality : Outcome.returned state = embedStatementOutcome rawOutcome) :
    rawOutcome = .returned state := by
  cases rawOutcome <;> simp_all [embedStatementOutcome]

private theorem raw_fault_of_embed_eq
    (equality : Outcome.fault = embedStatementOutcome rawOutcome) :
    rawOutcome = .undefinedBehavior := by
  cases rawOutcome <;> simp_all [embedStatementOutcome]

private theorem CheckedExpr.eval_eq_of_raw_eq
    (checked : CheckedExpr layout environment raw)
    (evaluation : Raw.evalExpr layout environment raw state = some (type, value)) :
    checked.expression.eval layout state = some value := by
  rw [checked.correct] at evaluation
  cases found : checked.expression.eval layout state <;> simp_all

private theorem CheckedLValue.eval_eq_of_raw_eq
    (checked : CheckedLValue layout environment raw)
    (evaluation : Raw.evalLValue layout environment raw state = some (type, place)) :
    checked.location.eval layout state = some place := by
  rw [checked.correct] at evaluation
  cases found : checked.location.eval layout state <;> simp_all

private theorem CheckedExpr.raw_eq_of_eval_eq
    (checked : CheckedExpr layout environment raw)
    (evaluation : checked.expression.eval layout state = some value) :
    Raw.evalExpr layout environment raw state = some (checked.ctype, value) := by
  simp [checked.correct, evaluation]

private theorem CheckedLValue.raw_eq_of_eval_eq
    (checked : CheckedLValue layout environment raw)
    (evaluation : checked.location.eval layout state = some place) :
    Raw.evalLValue layout environment raw state = some (checked.ctype, place) := by
  simp [checked.correct, evaluation]

private theorem checkedAssign_rawToResolved
    (left : CheckedLValue layout environment rawLeft)
    (right : CheckedExpr layout environment rawRight)
    (evaluation : Raw.evalExpr layout environment rawRight state = some (rightType, value))
    (location : Raw.evalLValue layout environment rawLeft state = some (leftType, place))
    (stored : writeLocation layout place value state = some result) :
    Stmt.Exec layout (.assign left.location right.expression) state (.normal result) := by
  apply Stmt.Exec.assign
  simp [Stmt.assign?, right.eval_eq_of_raw_eq evaluation,
    left.eval_eq_of_raw_eq location, stored]

private theorem checkedAssignFault_rawToResolved
    (left : CheckedLValue layout environment rawLeft)
    (right : CheckedExpr layout environment rawRight)
    (failed : (do
      let (_, value) ← Raw.evalExpr layout environment rawRight state
      let (_, place) ← Raw.evalLValue layout environment rawLeft state
      writeLocation layout place value state) = none) :
    Stmt.Exec layout (.assign left.location right.expression) state .fault := by
  apply Stmt.Exec.assignFault
  rw [right.correct, left.correct] at failed
  simpa [Stmt.assign?] using failed

private theorem checkedAssignFault_resolvedToRaw
    (left : CheckedLValue layout environment rawLeft)
    (right : CheckedExpr layout environment rawRight)
    (failed : Stmt.assign? layout left.location right.expression state = none) :
    (do
      let (_, value) ← Raw.evalExpr layout environment rawRight state
      let (_, place) ← Raw.evalLValue layout environment rawLeft state
      writeLocation layout place value state) = none := by
  rw [right.correct, left.correct]
  simpa [Stmt.assign?] using failed

private theorem checkedAssign_resolvedToRaw
    (left : CheckedLValue layout environment rawLeft)
    (right : CheckedExpr layout environment rawRight)
    (evaluation : Stmt.assign? layout left.location right.expression state = some result) :
    Raw.StatementExec layout functionId returnType
      (.stmt ⟨.assign rawLeft rawRight, region⟩) environment state (.normal result) := by
  simp only [Stmt.assign?] at evaluation
  cases rightEq : right.expression.eval layout state with
  | none => simp [rightEq] at evaluation
  | some value =>
      cases leftEq : left.location.eval layout state with
      | none => simp [rightEq, leftEq] at evaluation
      | some place =>
          exact .assign (right.raw_eq_of_eval_eq rightEq) (left.raw_eq_of_eval_eq leftEq)
            (by simpa [rightEq, leftEq] using evaluation)

private theorem checkedReturn_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program}
    (value : CheckedExpr layout environment rawValue)
    (evaluation : Raw.evalExpr layout environment rawValue state = some (type, result))
    (cast : castValue program.target returnType result = some returned) :
    Stmt.Exec layout (.return returnType (some value.expression)) state
      (.returned (state.returnValue returned)) := by
  apply Stmt.Exec.ret
  simp [Stmt.return?, value.eval_eq_of_raw_eq evaluation, cast]

private theorem checkedReturnVoid_rawToResolved
    (typeEq : returnType = CType.void) :
    Stmt.Exec layout (.return returnType none) state (.returned (state.returnValue .void)) := by
  subst returnType
  apply Stmt.Exec.ret
  simp [Stmt.return?]

private theorem checkedReturnFault_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program}
    (value : CheckedExpr layout environment rawValue)
    (failed : (Raw.evalExpr layout environment rawValue state).bind
      (fun result => castValue program.target returnType result.2) = none) :
    Stmt.Exec layout (.return returnType (some value.expression)) state .fault := by
  apply Stmt.Exec.retFault
  rw [value.correct] at failed
  simpa [Stmt.return?] using failed

private theorem checkedReturnFault_resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    (value : CheckedExpr layout environment rawValue)
    (failed : Stmt.return? layout returnType (some value.expression) state = none) :
    (Raw.evalExpr layout environment rawValue state).bind
      (fun result => castValue program.target returnType result.2) = none := by
  rw [value.correct]
  simpa [Stmt.return?] using failed

private theorem checkedReturn_resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    (value : CheckedExpr layout environment rawValue)
    (evaluation : Stmt.return? layout returnType (some value.expression) state = some result) :
    Raw.StatementExec layout functionId returnType
      (.stmt ⟨.returnStmt (some rawValue), region⟩) environment state (.returned result) := by
  simp only [Stmt.return?] at evaluation
  cases valueEq : value.expression.eval layout state with
  | none => simp [valueEq] at evaluation
  | some rawResult =>
      cases castEq : castValue program.target returnType rawResult with
      | none => simp [valueEq, castEq] at evaluation
      | some returned =>
          simp [valueEq, castEq] at evaluation
          cases evaluation
          exact .ret (value.raw_eq_of_eval_eq valueEq) castEq

private theorem CheckedExpr.integer_eq_of_raw_eq
    (checked : CheckedExpr layout environment raw)
    (evaluation : Raw.evalExpr layout environment raw state = some (type, .integer value)) :
    checked.expression.eval layout state = some (.integer value) :=
  checked.eval_eq_of_raw_eq evaluation

private theorem CheckedExpr.integerFault_rawToResolved
    (checked : CheckedExpr layout environment raw)
    (failed : (Raw.evalExpr layout environment raw state).bind (fun result =>
      match result.2 with | .integer value => some value | _ => none) = none) :
    (checked.expression.eval layout state).bind (fun value =>
      match value with | .integer value => some value | _ => none) = none := by
  rw [checked.correct] at failed
  simpa using failed

private theorem CheckedExpr.raw_integer_eq_of_eval_eq
    (checked : CheckedExpr layout environment raw)
    (evaluation : checked.expression.eval layout state = some (.integer value)) :
    Raw.evalExpr layout environment raw state = some (checked.ctype, .integer value) :=
  checked.raw_eq_of_eval_eq evaluation

private theorem CheckedExpr.integerFault_resolvedToRaw
    (checked : CheckedExpr layout environment raw)
    (failed : (checked.expression.eval layout state).bind (fun value =>
      match value with | .integer value => some value | _ => none) = none) :
    (Raw.evalExpr layout environment raw state).bind (fun result =>
      match result.2 with | .integer value => some value | _ => none) = none := by
  rw [checked.correct]
  simpa using failed

private theorem checkedInitialize_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program}
    {environment : Raw.Env} {binding : Raw.Binding}
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (evaluation : Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId) = some (type, result))
    (cast : castValue program.target binding.type result = some stored) :
    Stmt.Exec layout (.declare binding.symbolId binding.type (some value.expression)) state
      (.normal ((state.clear binding.symbolId).write binding.symbolId stored)) := by
  apply Stmt.Exec.initialize
  simp [Stmt.initialize?, value.eval_eq_of_raw_eq evaluation, cast]

private theorem checkedInitializeFault_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program}
    {environment : Raw.Env} {binding : Raw.Binding}
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (failed : (Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId)).bind
        (fun result => castValue program.target binding.type result.2) = none) :
    Stmt.Exec layout (.declare binding.symbolId binding.type (some value.expression)) state .fault := by
  apply Stmt.Exec.initializeFault
  rw [value.correct] at failed
  simpa [Stmt.initialize?] using failed

private theorem checkedInitializeFault_resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    {environment : Raw.Env} {binding : Raw.Binding}
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (failed : Stmt.initialize? layout binding.symbolId binding.type value.expression state = none) :
    (Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId)).bind
        (fun result => castValue program.target binding.type result.2) = none := by
  rw [value.correct]
  simpa [Stmt.initialize?] using failed

private theorem checkedInitialization_resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    {environment : Raw.Env} {binding : Raw.Binding}
    (bindingEq : Raw.localBinding? program functionId
      ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩ = some binding)
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (evaluation : Stmt.initialize? layout binding.symbolId binding.type value.expression state =
      some middle)
    (rest : Raw.BodyExec layout functionId returnType items (Raw.Env.bind binding environment)
      middle outcome) :
    Raw.BodyExec layout functionId returnType
      (.declaration ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩ :: items)
      environment state outcome := by
  simp only [Stmt.initialize?] at evaluation
  cases valueEq : value.expression.eval layout (state.clear binding.symbolId) with
  | none => simp [valueEq] at evaluation
  | some result =>
      cases castEq : castValue program.target binding.type result with
      | none => simp [valueEq, castEq] at evaluation
      | some stored =>
          simp [valueEq, castEq] at evaluation
          cases evaluation
          exact .initialization bindingEq (value.raw_eq_of_eval_eq valueEq) castEq rest

private theorem checkedInitializationFault_resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    {environment : Raw.Env} {binding : Raw.Binding}
    (bindingEq : Raw.localBinding? program functionId
      ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩ = some binding)
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (failed : Stmt.initialize? layout binding.symbolId binding.type value.expression state = none) :
    Raw.BodyExec layout functionId returnType
      (.declaration ⟨.varDecl rawType name [] (some (.initE rawValue)) attributes, region⟩ :: items)
      environment state .undefinedBehavior :=
  .initializationFault bindingEq (checkedInitializeFault_resolvedToRaw value failed)

private theorem checkedDeclaration_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program} {binding : Raw.Binding}
    (rest : Stmt.Exec layout resolved (state.clear binding.symbolId) outcome) :
    Stmt.Exec layout (.seq (.declare binding.symbolId binding.type none) resolved) state outcome :=
  .seqNormal .declare rest

private theorem checkedInitialization_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program} {binding : Raw.Binding}
    {environment : Raw.Env}
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (evaluation : Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId) = some (type, result))
    (cast : castValue program.target binding.type result = some stored)
    (rest : Stmt.Exec layout resolved
      ((state.clear binding.symbolId).write binding.symbolId stored) outcome) :
    Stmt.Exec layout (.seq (.declare binding.symbolId binding.type (some value.expression)) resolved)
      state outcome :=
  .seqNormal (checkedInitialize_rawToResolved value evaluation cast) rest

private theorem checkedInitializationFault_rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program} {binding : Raw.Binding}
    {environment : Raw.Env}
    (value : CheckedExpr layout (Raw.Env.bind binding environment) rawValue)
    (failed : (Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId)).bind
        (fun result => castValue program.target binding.type result.2) = none) :
    Stmt.Exec layout (.seq (.declare binding.symbolId binding.type (some value.expression)) resolved)
      state .fault :=
  .seqFault (checkedInitializeFault_rawToResolved value failed)

private theorem initializationBind_none_of_pointwise {program : Program}
    {layout : MemoryLayout.Certificate program} {binding : Raw.Binding}
    {environment : Raw.Env} {rawValue : CParser.Expr} {state : State}
    (failed : ∀ type result,
      Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
        (state.clear binding.symbolId) = some (type, result) →
      castValue program.target binding.type result = none) :
    (Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId)).bind
        (fun result => castValue program.target binding.type result.2) = none := by
  cases evaluation : Raw.evalExpr layout (Raw.Env.bind binding environment) rawValue
      (state.clear binding.symbolId) with
  | none => rfl
  | some result =>
      rcases result with ⟨type, result⟩
      simp [failed type result evaluation]

private theorem Stmt.Exec.seqSkip
    (execution : Stmt.Exec layout statement state outcome) :
    Stmt.Exec layout (.seq statement .skip) state outcome := by
  cases outcome with
  | normal result => exact .seqNormal execution .skip
  | returned result => exact .seqReturned execution
  | fault => exact .seqFault execution

private theorem Stmt.Exec.ofSeqSkip
    (execution : Stmt.Exec layout (.seq statement .skip) state outcome) :
    Stmt.Exec layout statement state outcome := by
  cases execution with
  | seqNormal first rest => cases rest; exact first
  | seqReturned first => exact first
  | seqFault first => exact first

private theorem CheckedBody.rawToResolved
    (checked : CheckedBody layout functionId returnType raw environment resolved)
    (execution : Raw.BodyExec layout functionId returnType raw environment state outcome) :
    Stmt.Exec layout resolved state (embedStatementOutcome outcome) := by
  refine (Raw.BodyExec.rec
    (motive_1 := fun raw environment state outcome _ =>
      ∀ {resolved}, CheckedStatement layout functionId returnType raw environment resolved →
        Stmt.Exec layout resolved state (embedStatementOutcome outcome))
    (motive_2 := fun raw environment state outcome _ =>
      ∀ {resolved}, CheckedBody layout functionId returnType raw environment resolved →
        Stmt.Exec layout resolved state (embedStatementOutcome outcome))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    execution) checked
  all_goals intros
  all_goals rename_i checked
  all_goals cases checked
  all_goals simp only [embedStatementOutcome]
  all_goals first
    | exact Stmt.Exec.skip
    | exact Stmt.Exec.seqSkip (by solve_by_elim)
    | exact Stmt.Exec.seqNormal (by solve_by_elim) (by solve_by_elim)
    | exact Stmt.Exec.seqReturned (by solve_by_elim)
    | exact Stmt.Exec.seqFault (by solve_by_elim)
    | exact Stmt.Exec.seqNormal .declare (by solve_by_elim)
    | apply Stmt.Exec.condTrue <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.condFalse <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.condFault <;> solve_by_elim [CheckedExpr.integerFault_rawToResolved]
    | apply Stmt.Exec.whileFalse <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.whileTrue <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.whileReturned <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.whileFault <;> solve_by_elim [CheckedExpr.integer_eq_of_raw_eq]
    | apply Stmt.Exec.whileGuardFault <;>
        solve_by_elim [CheckedExpr.integerFault_rawToResolved]
    | skip
  all_goals first
    | apply checkedAssign_rawToResolved <;> assumption
    | apply checkedAssignFault_rawToResolved <;> assumption
    | apply checkedReturn_rawToResolved <;> assumption
    | apply checkedReturnVoid_rawToResolved <;> assumption
    | apply checkedReturnFault_rawToResolved <;> assumption
    | skip
  all_goals try cases declarationEq
  all_goals simp_all
  all_goals first
    | apply checkedDeclaration_rawToResolved <;> solve_by_elim
    | apply checkedInitialization_rawToResolved <;> solve_by_elim
    | apply checkedInitializationFault_rawToResolved
      apply initializationBind_none_of_pointwise
      assumption

private theorem CheckedStatement.rawToResolved
    (checked : CheckedStatement layout functionId returnType raw environment resolved)
    (execution : Raw.StatementExec layout functionId returnType raw environment state outcome) :
    Stmt.Exec layout resolved state (embedStatementOutcome outcome) := by
  let combined : CheckedBody layout functionId returnType [.statement raw] environment
      (.seq resolved .skip) := .statement checked .nil
  have rawCombined : Raw.BodyExec layout functionId returnType [.statement raw]
      environment state outcome := match outcome with
    | .normal result => .statementNormal execution .nil
    | .returned result => .statementReturned execution
    | .undefinedBehavior => .statementFault execution
  have result := combined.rawToResolved rawCombined
  exact result.ofSeqSkip

/-!
The reverse proof follows the resolved finite derivation.  Its private rank is
derived from statement syntax; loop execution remains unbounded and uses the
same checked while node.
-/
private def Stmt.depth : Stmt → Nat
  | .skip | .assign .. | .declare .. | .return .. => 1
  | .seq first second => max first.depth second.depth + 1
  | .cond _ thenStmt elseStmt => max thenStmt.depth elseStmt.depth + 1
  | .while _ body => body.depth + 1

mutual
private theorem CheckedStatement.resolvedToRawAux
    (checked : CheckedStatement layout functionId returnType raw environment resolved)
    (execution : Stmt.Exec layout resolved state outcome) (rank : Nat)
    (bounded : resolved.depth < rank) :
    ∃ rawOutcome, outcome = embedStatementOutcome rawOutcome ∧
      Raw.StatementExec layout functionId returnType raw environment state rawOutcome := by
  induction execution generalizing raw environment with
  | skip => cases checked; exact ⟨.normal _, rfl, .empty⟩
  | assign evaluation =>
      cases checked with
      | assign left right =>
          exact ⟨.normal _, rfl, checkedAssign_resolvedToRaw left right evaluation⟩
  | assignFault evaluation =>
      cases checked with
      | assign left right =>
          exact ⟨.undefinedBehavior, rfl,
            .assignFault (checkedAssignFault_resolvedToRaw left right evaluation)⟩
  | ret evaluation =>
      rename_i inputState resultState
      cases checked with
      | ret value =>
          exact ⟨.returned _, rfl, checkedReturn_resolvedToRaw value evaluation⟩
      | retVoid typeEq =>
          have resultEq : resultState = inputState.returnValue .void := by
            simpa [Stmt.return?, typeEq] using evaluation.symm
          subst resultState
          exact ⟨.returned _, rfl, .retVoid typeEq⟩
  | retFault evaluation =>
      cases checked with
      | ret value =>
          exact ⟨.undefinedBehavior, rfl,
            .retFault (checkedReturnFault_resolvedToRaw value evaluation)⟩
      | retVoid typeEq =>
          simp [Stmt.return?, typeEq] at evaluation
  | condTrue evaluation nonzero branch branchIH =>
      cases checked with
      | cond condition thenBranch elseBranch =>
          obtain ⟨rawOutcome, equality, rawBranch⟩ := branchIH thenBranch (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality,
            .condTrue (condition.raw_integer_eq_of_eval_eq evaluation) nonzero rawBranch⟩
  | condFalse evaluation branch branchIH =>
      cases checked with
      | cond condition thenBranch elseBranch =>
          obtain ⟨rawOutcome, equality, rawBranch⟩ := branchIH elseBranch (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality,
            .condFalse (condition.raw_integer_eq_of_eval_eq evaluation) rawBranch⟩
  | condFault failed =>
      cases checked with
      | cond condition thenBranch elseBranch =>
          exact ⟨.undefinedBehavior, rfl,
            .condFault (condition.integerFault_resolvedToRaw failed)⟩
  | whileFalse evaluation =>
      cases checked with
      | «while» condition body =>
          exact ⟨.normal _, rfl,
            .whileFalse (condition.raw_integer_eq_of_eval_eq evaluation)⟩
  | whileTrue evaluation nonzero iteration rest iterationIH restIH =>
      cases checked with
      | «while» condition body =>
          obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ := iterationIH body (by simp_all [Stmt.depth]; omega)
          cases raw_normal_of_embed_eq iterationEq
          obtain ⟨rawOutcome, equality, rawRest⟩ := restIH (.while condition body) bounded
          exact ⟨rawOutcome, equality,
            .whileTrue (condition.raw_integer_eq_of_eval_eq evaluation) nonzero
              rawIteration rawRest⟩
  | whileReturned evaluation nonzero iteration iterationIH =>
      cases checked with
      | «while» condition body =>
          obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ := iterationIH body (by simp_all [Stmt.depth]; omega)
          cases raw_returned_of_embed_eq iterationEq
          exact ⟨.returned _, rfl,
            .whileReturned (condition.raw_integer_eq_of_eval_eq evaluation) nonzero rawIteration⟩
  | whileFault evaluation nonzero iteration iterationIH =>
      cases checked with
      | «while» condition body =>
          obtain ⟨iterationOutcome, iterationEq, rawIteration⟩ := iterationIH body (by simp_all [Stmt.depth]; omega)
          cases raw_fault_of_embed_eq iterationEq
          exact ⟨.undefinedBehavior, rfl,
            .whileFault (condition.raw_integer_eq_of_eval_eq evaluation) nonzero rawIteration⟩
  | whileGuardFault failed =>
      cases checked with
      | «while» condition body =>
          exact ⟨.undefinedBehavior, rfl,
            .whileGuardFault (condition.integerFault_resolvedToRaw failed)⟩
  | seqNormal first rest firstIH restIH =>
      cases checked with
      | block body =>
          cases rest
          obtain ⟨rawOutcome, equality, rawExecution⟩ :=
            CheckedBody.resolvedToRawAux body first (rank - 1) (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .block rawExecution⟩
      | trap body =>
          cases rest
          obtain ⟨rawOutcome, equality, rawExecution⟩ := firstIH body (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .trap rawExecution⟩
  | seqReturned first firstIH =>
      cases checked with
      | block body =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ :=
            CheckedBody.resolvedToRawAux body first (rank - 1) (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .block rawExecution⟩
      | trap body =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := firstIH body (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .trap rawExecution⟩
  | seqFault first firstIH =>
      cases checked with
      | block body =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ :=
            CheckedBody.resolvedToRawAux body first (rank - 1) (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .block rawExecution⟩
      | trap body =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := firstIH body (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .trap rawExecution⟩
  | declare => cases checked
  | «initialize» evaluation => cases checked
  | initializeFault evaluation => cases checked
  termination_by rank
  decreasing_by all_goals omega

private theorem CheckedBody.resolvedToRawAux
    (checked : CheckedBody layout functionId returnType raw environment resolved)
    (execution : Stmt.Exec layout resolved state outcome) (rank : Nat)
    (bounded : resolved.depth < rank) :
    ∃ rawOutcome, outcome = embedStatementOutcome rawOutcome ∧
      Raw.BodyExec layout functionId returnType raw environment state rawOutcome := by
  induction execution generalizing raw environment with
  | skip => cases checked; exact ⟨.normal _, rfl, .nil⟩
  | seqNormal firstExecution restExecution firstIH restIH =>
      cases checked with
      | statement first rest =>
          obtain ⟨firstOutcome, firstEq, rawFirst⟩ :=
            first.resolvedToRawAux firstExecution (rank - 1) (by simp_all [Stmt.depth]; omega)
          cases raw_normal_of_embed_eq firstEq
          obtain ⟨rawOutcome, equality, rawRest⟩ := restIH rest (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .statementNormal rawFirst rawRest⟩
      | declaration bindingEq rest =>
          cases firstExecution
          obtain ⟨rawOutcome, equality, rawRest⟩ := restIH rest (by simp_all [Stmt.depth]; omega)
          exact ⟨rawOutcome, equality, .declaration bindingEq rawRest⟩
      | initialization declarationEq bindingEq value rest =>
          cases firstExecution with
          | «initialize» evaluation =>
              obtain ⟨rawOutcome, equality, rawRest⟩ := restIH rest (by simp_all [Stmt.depth]; omega)
              cases declarationEq
              exact ⟨rawOutcome, equality,
                checkedInitialization_resolvedToRaw bindingEq value evaluation rawRest⟩
  | seqReturned firstExecution firstIH =>
      cases checked with
      | statement first rest =>
          obtain ⟨rawOutcome, equality, rawFirst⟩ :=
            first.resolvedToRawAux firstExecution (rank - 1) (by simp_all [Stmt.depth]; omega)
          cases raw_returned_of_embed_eq equality
          exact ⟨.returned _, rfl, .statementReturned rawFirst⟩
      | declaration bindingEq rest => cases firstExecution
      | initialization declarationEq bindingEq value rest => cases firstExecution
  | seqFault firstExecution firstIH =>
      cases checked with
      | statement first rest =>
          obtain ⟨rawOutcome, equality, rawFirst⟩ :=
            first.resolvedToRawAux firstExecution (rank - 1) (by simp_all [Stmt.depth]; omega)
          cases raw_fault_of_embed_eq equality
          exact ⟨.undefinedBehavior, rfl, .statementFault rawFirst⟩
      | initialization declarationEq bindingEq value rest =>
          cases firstExecution with
          | initializeFault failed =>
              cases declarationEq
              exact ⟨.undefinedBehavior, rfl,
                checkedInitializationFault_resolvedToRaw bindingEq value failed⟩
      | declaration bindingEq rest => cases firstExecution
  | assign => cases checked
  | assignFault => cases checked
  | declare => cases checked
  | «initialize» => cases checked
  | initializeFault => cases checked
  | ret => cases checked
  | retFault => cases checked
  | condTrue => cases checked
  | condFalse => cases checked
  | condFault => cases checked
  | whileFalse => cases checked
  | whileTrue => cases checked
  | whileReturned => cases checked
  | whileFault => cases checked
  | whileGuardFault => cases checked
  termination_by rank
  decreasing_by all_goals omega
end

private theorem CheckedStatement.resolvedToRaw
    (checked : CheckedStatement layout functionId returnType raw environment resolved)
    (execution : Stmt.Exec layout resolved state outcome) :
    ∃ rawOutcome, outcome = embedStatementOutcome rawOutcome ∧
      Raw.StatementExec layout functionId returnType raw environment state rawOutcome :=
  checked.resolvedToRawAux execution (resolved.depth + 1) (by omega)

private theorem CheckedBody.resolvedToRaw
    (checked : CheckedBody layout functionId returnType raw environment resolved)
    (execution : Stmt.Exec layout resolved state outcome) :
    ∃ rawOutcome, outcome = embedStatementOutcome rawOutcome ∧
      Raw.BodyExec layout functionId returnType raw environment state rawOutcome :=
  checked.resolvedToRawAux execution (resolved.depth + 1) (by omega)

structure Function where
  name : String
  returnType : AnalyzedCType
  parameters : List Raw.Binding
  locals : List Nat
  body : Stmt
deriving Repr, DecidableEq, Inhabited

namespace Function

def enter (function : Function) (arguments : List Value) (base : State := {}) : Except Error State := do
  if arguments.length != function.parameters.length then
    .error (.malformedAnalysis "function argument count mismatch")
  let cleared := function.locals.foldl State.clear base.resetReturn
  (function.parameters.zip arguments).foldlM (fun state parameter => do
      let value ← requireSome (.unsupportedType .bogus parameter.1.type)
        (castValue Target.arm parameter.1.type parameter.2)
      return state.write parameter.1.symbolId value) cleared

inductive Exec {program : Program} (layout : MemoryLayout.Certificate program)
    (function : Function) : State → Simpl.XState State Unit → Prop where
  | returned (body : Stmt.Exec layout function.body state.resetReturn (.returned result)) :
      Exec layout function state (.normal result)
  | fault (body : Stmt.Exec layout function.body state.resetReturn .fault) :
      Exec layout function state (.fault ())
  | fellOffVoid (typeEq : function.returnType = .void)
      (body : Stmt.Exec layout function.body state.resetReturn (.normal result)) :
      Exec layout function state (.normal (result.returnValue .void))
  | fellOffMain (nameEq : function.name = "main") (typeEq : function.returnType = .signed .int)
      (body : Stmt.Exec layout function.body state.resetReturn (.normal result)) :
      Exec layout function state (.normal (result.returnValue (.integer 0)))
  | fellOffFault (notVoid : function.returnType ≠ .void)
      (notMain : function.name ≠ "main" ∨ function.returnType ≠ .signed .int)
      (body : Stmt.Exec layout function.body state.resetReturn (.normal result)) :
      Exec layout function state (.fault ())

end Function

abbrev Command := Simpl.Com State Nat Unit
abbrev Environment := Simpl.Body State Nat Unit

def emptyEnvironment : Environment := fun _ => none

private def succeeds (step : State → Option State) (state : State) : Prop :=
  ∃ result, step state = some result

private def stepResult (step : State → Option State) (state : State) : State :=
  (step state).getD state

private def checkedBasic (step : State → Option State) : Command :=
  .Guard () (succeeds step) (.Basic (stepResult step))

private theorem checkedBasic_correct (equality : step state = some result) :
    Simpl.Exec emptyEnvironment (checkedBasic step) (.normal state) (.normal result) := by
  apply Simpl.Exec.guard ⟨result, equality⟩
  simpa [checkedBasic, stepResult, equality] using
    (Simpl.Exec.basic (env := emptyEnvironment) (transform := stepResult step) (s := state))

private theorem checkedBasic_fault (equality : step state = none) :
    Simpl.Exec emptyEnvironment (checkedBasic step) (.normal state) (.fault ()) := by
  exact .guardFault (by rintro ⟨result, found⟩; simp [equality] at found)

private theorem checkedBasic_complete (execution :
    Simpl.Exec emptyEnvironment (checkedBasic step) (.normal state) result) :
    (∃ next, step state = some next ∧ result = .normal next) ∨
      (step state = none ∧ result = .fault ()) := by
  cases execution with
  | guard valid body =>
      cases body
      obtain ⟨next, found⟩ := valid
      exact Or.inl ⟨next, found, by simp [stepResult, found]⟩
  | guardFault invalid =>
      right
      constructor
      · cases found : step state with
        | none => rfl
        | some next => exact False.elim (invalid ⟨next, found⟩)
      · rfl

private def condition? {program : Program} (layout : MemoryLayout.Certificate program)
    (condition : Expr) (state : State) : Option Int := do
  let .integer value ← condition.eval layout state | none
  return value

private theorem condition_eval_eq_of_eq_some
    (evaluation : condition? layout condition state = some value) :
    condition.eval layout state = some (.integer value) := by
  cases found : condition.eval layout state with
  | none => simp [condition?, found] at evaluation
  | some result =>
      cases result with
      | integer foundValue =>
          simp [condition?, found] at evaluation
          cases evaluation
          rfl
      | pointer pointer => simp [condition?, found] at evaluation
      | void => simp [condition?, found] at evaluation

def compile {program : Program} (layout : MemoryLayout.Certificate program) : Stmt → Command
  | .skip => .Skip
  | .seq first second => .Seq (compile layout first) (compile layout second)
  | .assign location value => checkedBasic (Stmt.assign? layout location value)
  | .declare symbolId _ none => .Basic fun state => state.clear symbolId
  | .declare symbolId type (some value) =>
      checkedBasic (Stmt.initialize? layout symbolId type value)
  | .return type value =>
      .Seq (checkedBasic (Stmt.return? layout type value)) .Throw
  | .cond condition thenStmt elseStmt =>
      .Guard () (fun state => (condition? layout condition state).isSome)
        (.Cond (fun state => (condition? layout condition state).getD 0 ≠ 0)
          (compile layout thenStmt) (compile layout elseStmt))
  | .while condition body =>
      .While (fun state => condition? layout condition state ≠ some 0)
        (.Seq (.Guard () (fun state => (condition? layout condition state).isSome) .Skip)
          (compile layout body))

def supported {program : Program} (layout : MemoryLayout.Certificate program) :
    (statement : Stmt) → SimplConv.Kernel.Supported (compile layout statement)
  | .skip => .skip
  | .seq first second => .seq (supported layout first) (supported layout second)
  | .assign location value =>
      .guard () (succeeds (Stmt.assign? layout location value))
        (.basic (stepResult (Stmt.assign? layout location value)))
  | .declare symbolId type none => .basic fun (state : State) => state.clear symbolId
  | .declare symbolId type (some value) =>
      .guard () (succeeds (Stmt.initialize? layout symbolId type value))
        (.basic (stepResult (Stmt.initialize? layout symbolId type value)))
  | .return type value =>
      .seq (.guard () (succeeds (Stmt.return? layout type value))
        (.basic (stepResult (Stmt.return? layout type value)))) .throw
  | .cond condition thenStmt elseStmt =>
      .guard () (fun state => (condition? layout condition state).isSome)
        (.cond (fun state => (condition? layout condition state).getD 0 ≠ 0)
          (supported layout thenStmt) (supported layout elseStmt))
  | .while condition body =>
      .while (fun state => condition? layout condition state ≠ some 0)
        (.seq (.guard () (fun state => (condition? layout condition state).isSome) .skip)
          (supported layout body))

def embedOutcome : Outcome → Simpl.XState State Unit
  | .normal state => .normal state
  | .returned state => .abrupt state
  | .fault => .fault ()

theorem compile_correct {program : Program} (layout : MemoryLayout.Certificate program)
    (execution : Stmt.Exec layout statement state outcome) :
    Simpl.Exec emptyEnvironment (compile layout statement) (.normal state) (embedOutcome outcome) := by
  induction execution with
  | skip => exact .skip
  | seqNormal _ _ firstIH restIH => exact .seq firstIH restIH
  | seqReturned _ firstIH => exact .seq firstIH .abruptProp
  | seqFault _ firstIH => exact .seq firstIH .faultProp
  | assign evaluation => exact checkedBasic_correct evaluation
  | assignFault evaluation => exact checkedBasic_fault evaluation
  | declare => exact .basic
  | «initialize» evaluation => exact checkedBasic_correct evaluation
  | initializeFault evaluation => exact checkedBasic_fault evaluation
  | ret evaluation => exact .seq (checkedBasic_correct evaluation) .throw
  | retFault evaluation => exact .seq (checkedBasic_fault evaluation) .faultProp
  | condTrue evaluation nonzero _ branchIH =>
      apply Simpl.Exec.guard
      · simp [condition?, evaluation]
      · exact .condTrue (by simp [condition?, evaluation, nonzero]) branchIH
  | condFalse evaluation _ branchIH =>
      apply Simpl.Exec.guard
      · simp [condition?, evaluation]
      · exact .condFalse (by simp [condition?, evaluation]) branchIH
  | condFault failed =>
      exact .guardFault (by simpa [condition?, failed])
  | whileFalse evaluation => exact .whileFalse (by simp [condition?, evaluation])
  | whileTrue evaluation nonzero _ _ bodyIH restIH =>
      apply Simpl.Exec.whileTrue
      · simp [condition?, evaluation, nonzero]
      · exact .seq (.guard (by simp [condition?, evaluation]) .skip) bodyIH
      · exact restIH
  | whileReturned evaluation nonzero _ bodyIH =>
      apply Simpl.Exec.whileTrue
      · simp [condition?, evaluation, nonzero]
      · exact .seq (.guard (by simp [condition?, evaluation]) .skip) bodyIH
      · exact .abruptProp
  | whileFault evaluation nonzero _ bodyIH =>
      apply Simpl.Exec.whileTrue
      · simp [condition?, evaluation, nonzero]
      · exact .seq (.guard (by simp [condition?, evaluation]) .skip) bodyIH
      · exact .faultProp
  | whileGuardFault failed =>
      apply Simpl.Exec.whileTrue
      · simp [condition?]
        intro equality
        rw [equality] at failed
        simp at failed
      · apply Simpl.Exec.seq
        · exact .guardFault (by simpa [condition?] using failed)
        · exact .faultProp
      · exact .faultProp

private theorem exec_from_abrupt (execution :
    Simpl.Exec environment command (.abrupt state) result) : result = .abrupt state := by
  cases execution
  rfl

private theorem exec_from_fault (execution :
    Simpl.Exec environment command (.fault label) result) : result = .fault label := by
  cases execution
  rfl

def sourceOutcome : Simpl.XState State Unit → Outcome
  | .normal state => .normal state
  | .abrupt state => .returned state
  | .fault _ | .stuck => .fault

theorem compile_complete {program : Program} (layout : MemoryLayout.Certificate program)
    (execution : Simpl.Exec emptyEnvironment (compile layout statement) (.normal state) result) :
    Stmt.Exec layout statement state (sourceOutcome result) ∧ result ≠ .stuck := by
  induction statement generalizing state result with
  | skip => cases execution; exact ⟨.skip, by simp⟩
  | seq first second firstIH secondIH =>
      cases execution with
      | seq firstExecution secondExecution =>
          obtain ⟨firstSource, firstNotStuck⟩ := firstIH firstExecution
          rename_i middle
          cases middle with
          | normal middle =>
              obtain ⟨secondSource, secondNotStuck⟩ := secondIH secondExecution
              exact ⟨.seqNormal firstSource secondSource, secondNotStuck⟩
          | abrupt middle =>
              rw [exec_from_abrupt secondExecution]
              exact ⟨.seqReturned firstSource, by simp⟩
          | fault label =>
              rw [exec_from_fault secondExecution]
              exact ⟨.seqFault firstSource, by simp⟩
          | stuck => exact False.elim (firstNotStuck rfl)
  | assign location value =>
      obtain (⟨next, found, resultEq⟩ | ⟨failed, resultEq⟩) := checkedBasic_complete execution
      · subst result
        exact ⟨.assign found, by simp⟩
      · subst result
        exact ⟨.assignFault failed, by simp⟩
  | declare symbolId type initializer =>
      cases initializer with
      | none => cases execution; exact ⟨.declare, by simp⟩
      | some value =>
          obtain (⟨next, found, resultEq⟩ | ⟨failed, resultEq⟩) := checkedBasic_complete execution
          · subst result
            exact ⟨.initialize found, by simp⟩
          · subst result
            exact ⟨.initializeFault failed, by simp⟩
  | «return» type value =>
      cases execution with
      | seq firstExecution throwExecution =>
          obtain (⟨next, found, firstEq⟩ | ⟨failed, firstEq⟩) :=
            checkedBasic_complete firstExecution
          · subst_vars
            cases throwExecution
            exact ⟨.ret found, by simp⟩
          · subst_vars
            rw [exec_from_fault throwExecution]
            exact ⟨.retFault failed, by simp⟩
  | cond condition thenStmt elseStmt thenIH elseIH =>
      simp only [compile] at execution
      cases execution with
      | guard valid branchExecution =>
          cases evaluation : condition? layout condition state with
          | none => simp [evaluation] at valid
          | some value =>
              cases branchExecution with
              | condTrue nonzero thenExecution =>
                  obtain ⟨source, notStuck⟩ := thenIH thenExecution
                  have valueNonzero : value ≠ 0 := by simpa [evaluation] using nonzero
                  exact ⟨.condTrue (condition_eval_eq_of_eq_some evaluation) valueNonzero source,
                    notStuck⟩
              | condFalse zero elseExecution =>
                  obtain ⟨source, notStuck⟩ := elseIH elseExecution
                  have valueZero : value = 0 := by
                    apply Classical.byContradiction
                    intro nonzero
                    exact zero (by simp [evaluation, nonzero])
                  subst value
                  exact ⟨.condFalse (condition_eval_eq_of_eq_some evaluation) source, notStuck⟩
      | guardFault invalid =>
          have failed : condition? layout condition state = none := by
            cases found : condition? layout condition state with
            | none => rfl
            | some value => exact False.elim (invalid (by simp [found]))
          exact ⟨.condFault (by simpa [condition?] using failed), by simp⟩
  | «while» condition body bodyIH =>
      simp only [compile] at execution
      generalize commandEq : Simpl.Com.While
        (fun state => condition? layout condition state ≠ some 0)
        (.Seq (.Guard () (fun state => (condition? layout condition state).isSome) .Skip)
          (compile layout body)) = command at execution
      generalize inputEq : Simpl.XState.normal state = input at execution
      revert state
      induction execution with
      | whileFalse stopped =>
          intro state inputEq
          let source := state
          cases commandEq
          cases inputEq
          have evaluation : condition? layout condition source = some 0 :=
            Classical.byContradiction stopped
          exact ⟨.whileFalse (condition_eval_eq_of_eq_some evaluation), by simp⟩
      | whileTrue continues iteration rest iterationIH restIH =>
          intro state inputEq
          let source := state
          cases commandEq
          cases inputEq
          cases iteration with
          | seq guardExecution bodyExecution =>
              cases guardExecution with
              | guard valid guardBody =>
                  cases guardBody
                  cases evaluation : condition? layout condition source with
                  | none => simp [source, evaluation] at valid
                  | some value =>
                      have nonzero : value ≠ 0 := by
                        intro zero
                        subst value
                        exact continues evaluation
                      obtain ⟨bodySource, bodyNotStuck⟩ := bodyIH bodyExecution
                      rename_i middle final
                      cases middle with
                      | normal middle =>
                          obtain ⟨restSource, restNotStuck⟩ := restIH rfl rfl
                          exact ⟨.whileTrue (condition_eval_eq_of_eq_some evaluation) nonzero
                            bodySource restSource, restNotStuck⟩
                      | abrupt middle =>
                          rw [exec_from_abrupt rest]
                          exact ⟨.whileReturned (condition_eval_eq_of_eq_some evaluation) nonzero
                            bodySource, by simp⟩
                      | fault label =>
                          rw [exec_from_fault rest]
                          exact ⟨.whileFault (condition_eval_eq_of_eq_some evaluation) nonzero
                            bodySource, by simp⟩
                      | stuck => exact False.elim (bodyNotStuck rfl)
              | guardFault invalid =>
                  rw [exec_from_fault bodyExecution] at rest
                  rw [exec_from_fault rest]
                  have failed : condition? layout condition source = none := by
                    cases found : condition? layout condition source with
                    | none => rfl
                    | some value => exact False.elim (invalid (by simp [source, found]))
                  exact ⟨.whileGuardFault (by simpa [condition?] using failed), by simp⟩
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

private theorem writeLocation_returned {program : Program}
    {layout : MemoryLayout.Certificate program}
    (evaluation : writeLocation layout location value state = some result) :
    result.returned = state.returned := by
  cases location with
  | slot symbolId type =>
      unfold writeLocation at evaluation
      cases castEq : castValue program.target type value with
      | none => simp [castEq] at evaluation
      | some casted =>
          simp [castEq, State.write] at evaluation
          subst result
          rfl
  | memory pointer type =>
      unfold writeLocation at evaluation
      cases castEq : castValue program.target type value with
      | none => simp [castEq] at evaluation
      | some casted =>
          cases casted with
          | integer integer =>
           cases storeEq : storeIntegerIn? layout state.external type pointer integer state.heap with
              | none => simp [castEq, storeEq] at evaluation
              | some heap =>
                  simp [castEq, storeEq, State.withHeap] at evaluation
                  subst result
                  rfl
          | pointer pointer => simp [castEq] at evaluation
          | void => simp [castEq] at evaluation

private theorem Stmt.assign?_returned {program : Program}
    {layout : MemoryLayout.Certificate program}
    (evaluation : Stmt.assign? layout location value state = some result) :
    result.returned = state.returned := by
  unfold Stmt.assign? at evaluation
  cases valueEq : value.eval layout state with
  | none => simp [valueEq] at evaluation
  | some foundValue =>
      cases locationEq : location.eval layout state with
      | none => simp [valueEq, locationEq] at evaluation
      | some foundLocation =>
          simp [valueEq, locationEq] at evaluation
          exact writeLocation_returned evaluation

private theorem Stmt.initialize?_returned {program : Program}
    {layout : MemoryLayout.Certificate program}
    (evaluation : Stmt.initialize? layout symbolId type value state = some result) :
    result.returned = state.returned := by
  unfold Stmt.initialize? at evaluation
  cases valueEq : value.eval layout (state.clear symbolId) with
  | none => simp [valueEq] at evaluation
  | some foundValue =>
      cases castEq : castValue program.target type foundValue with
      | none => simp [valueEq, castEq] at evaluation
      | some stored =>
          simp [valueEq, castEq] at evaluation
          subst result
          rfl

private theorem Stmt.return?_returned {program : Program}
    {layout : MemoryLayout.Certificate program}
    (evaluation : Stmt.return? layout type value state = some result) :
    result.returned = true := by
  cases value with
  | none =>
      cases type <;> simp [Stmt.return?, State.returnValue] at evaluation
      subst result
      rfl
  | some value =>
      unfold Stmt.return? at evaluation
      cases valueEq : value.eval layout state with
      | none => simp [valueEq] at evaluation
      | some foundValue =>
          cases castEq : castValue program.target type foundValue with
          | none => simp [valueEq, castEq] at evaluation
          | some returned =>
              simp [valueEq, castEq] at evaluation
              subst result
              rfl

private theorem Stmt.Exec.flags (execution : Stmt.Exec layout statement state outcome) :
    (∀ result, outcome = .returned result → result.returned = true) ∧
    (∀ result, outcome = .normal result → result.returned = state.returned) := by
  induction execution <;> constructor <;> intro result equality <;> cases equality
  all_goals try simp_all [State.returnValue, State.write, State.clear]
  all_goals solve_by_elim [Stmt.assign?_returned, Stmt.initialize?_returned,
    Stmt.return?_returned]

private theorem Stmt.Exec.returned_flag
    (execution : Stmt.Exec layout statement state (.returned result)) :
    result.returned = true :=
  execution.flags.1 result rfl

private theorem Stmt.Exec.normal_flag
    (execution : Stmt.Exec layout statement state (.normal result)) :
    result.returned = state.returned :=
  execution.flags.2 result rfl

namespace Function

private def finalize (function : Function) (state : State) : Option State :=
  if state.returned then some state
  else if function.returnType = .void then some (state.returnValue .void)
  else if function.name = "main" && function.returnType = .signed .int then
    some (state.returnValue (.integer 0))
  else none

def command (function : Function) {program : Program}
    (layout : MemoryLayout.Certificate program) : Command :=
  .Seq (.Basic State.resetReturn)
    (.Seq (.Catch (compile layout function.body) .Skip)
      (checkedBasic (finalize function)))

def supported (function : Function) {program : Program}
    (layout : MemoryLayout.Certificate program) :
    SimplConv.Kernel.Supported (function.command layout) :=
  .seq (.basic State.resetReturn)
    (.seq (.catch (MemorySimpl.supported layout function.body) .skip)
      (.guard () (succeeds (finalize function)) (.basic (stepResult (finalize function)))))

theorem command_correct {program : Program} (layout : MemoryLayout.Certificate program)
    (execution : Function.Exec layout function state result) :
    Simpl.Exec emptyEnvironment (Function.command function layout) (.normal state) result := by
  apply Simpl.Exec.seq .basic
  cases execution with
  | returned body =>
      apply Simpl.Exec.seq
      · exact .catchMatch (compile_correct layout body) .skip
      · exact checkedBasic_correct (by simp [finalize, body.returned_flag])
  | fault body =>
      apply Simpl.Exec.seq
      · exact .catchMiss (compile_correct layout body) (by simp [embedOutcome, Simpl.XState.IsAbrupt])
      · exact .faultProp
  | fellOffVoid typeEq body =>
      apply Simpl.Exec.seq
      · exact .catchMiss (compile_correct layout body) (by simp [embedOutcome, Simpl.XState.IsAbrupt])
      · have returnedEq := body.normal_flag
        simp [State.resetReturn] at returnedEq
        exact checkedBasic_correct (by simp [finalize, returnedEq, typeEq])
  | fellOffMain nameEq typeEq body =>
      apply Simpl.Exec.seq
      · exact .catchMiss (compile_correct layout body) (by simp [embedOutcome, Simpl.XState.IsAbrupt])
      · have returnedEq := body.normal_flag
        simp [State.resetReturn] at returnedEq
        exact checkedBasic_correct (by simp [finalize, returnedEq, nameEq, typeEq])
  | fellOffFault notVoid notMain body =>
      apply Simpl.Exec.seq
      · exact .catchMiss (compile_correct layout body) (by simp [embedOutcome, Simpl.XState.IsAbrupt])
      · apply checkedBasic_fault
        have returnedEq := body.normal_flag
        simp [State.resetReturn] at returnedEq
        simp [finalize, returnedEq, notVoid]
        intro nameEq typeEq
        exact notMain.elim (fun notName => notName nameEq) (fun notType => notType typeEq)

theorem command_complete {program : Program} (layout : MemoryLayout.Certificate program)
    (execution : Simpl.Exec emptyEnvironment (Function.command function layout) (.normal state) result) :
    Function.Exec layout function state result := by
  simp only [command] at execution
  cases execution with
  | seq resetExecution remainderExecution =>
      cases resetExecution
      cases remainderExecution with
      | seq catchExecution finishExecution =>
          cases catchExecution with
          | catchMatch bodyExecution handlerExecution =>
              cases handlerExecution
              obtain ⟨source, notStuck⟩ := compile_complete layout bodyExecution
              obtain (⟨next, found, resultEq⟩ | ⟨failed, resultEq⟩) :=
                checkedBasic_complete finishExecution
              · subst result
                have returnedEq := source.returned_flag
                simp [finalize, returnedEq] at found
                cases found
                exact .returned source
              · have returnedEq := source.returned_flag
                simp [finalize, returnedEq] at failed
          | catchMiss bodyExecution notAbrupt =>
              obtain ⟨source, notStuck⟩ := compile_complete layout bodyExecution
              rename_i bodyResult
              cases bodyResult with
              | normal bodyState =>
                  obtain (⟨next, found, resultEq⟩ | ⟨failed, resultEq⟩) :=
                    checkedBasic_complete finishExecution
                  · subst result
                    have returnedEq := source.normal_flag
                    simp [State.resetReturn] at returnedEq
                    by_cases voidEq : function.returnType = .void
                    · have nextEq : bodyState.returnValue .void = next := by
                        simpa [finalize, returnedEq, voidEq] using found
                      cases nextEq
                      exact .fellOffVoid voidEq source
                    · by_cases mainEq : function.name = "main" ∧
                        function.returnType = .signed .int
                      · have nextEq : bodyState.returnValue (.integer 0) = next := by
                          simpa [finalize, returnedEq, voidEq, mainEq] using found
                        cases nextEq
                        exact .fellOffMain mainEq.1 mainEq.2 source
                      · exact False.elim (by simp [finalize, returnedEq, voidEq, mainEq] at found)
                  · subst result
                    have returnedEq := source.normal_flag
                    simp [State.resetReturn] at returnedEq
                    have notVoid : function.returnType ≠ .void := by
                      intro voidEq
                      simp [finalize, returnedEq, voidEq] at failed
                    have notMain : function.name ≠ "main" ∨
                        function.returnType ≠ .signed .int := by
                      by_cases nameEq : function.name = "main"
                      · right
                        intro typeEq
                        simp [finalize, returnedEq, notVoid, nameEq, typeEq] at failed
                      · exact Or.inl nameEq
                    exact .fellOffFault notVoid notMain source
              | abrupt bodyState => exact False.elim (notAbrupt (by simp [Simpl.XState.IsAbrupt]))
              | fault label =>
                  rw [exec_from_fault finishExecution]
                  exact .fault source
              | stuck => exact False.elim (notStuck rfl)

end Function

def selectedFunctions (program : Program) (name : String) : List FunctionInfo :=
  program.functions.filter fun function =>
    (program.symbolById? function.symbolId).any (·.sourceName = name)

private def parameterBindings? (program : Program) (info : FunctionInfo) :
    Option (List Raw.Binding) := do
  let [environment] ← Raw.parameterEnv? program info.symbolId info.parameters | none
  return environment

inductive CheckedResolution {program : Program} (layout : MemoryLayout.Certificate program)
    (name : String) (info : FunctionInfo) (rawBody : Body) : Function → Prop where
  | checked
      (selected : selectedFunctions program name = [info])
      (raw : rawBody = info.body)
      (parametersEq : parameterBindings? program info = some parameters)
      (body : CheckedBody layout info.symbolId info.returnType info.body.value
        [parameters] resolvedBody)
      (locals : resolvedBody.declaredIds = info.locals) :
      CheckedResolution layout name info rawBody {
        name, returnType := info.returnType, parameters, locals := info.locals, body := resolvedBody }

private structure CheckedFunctionRun {program : Program}
    (layout : MemoryLayout.Certificate program) (name : String) where
  function : Function
  info : FunctionInfo
  resolution : CheckedResolution layout name info info.body function

private def checkFunction {program : Program} (layout : MemoryLayout.Certificate program)
    (name : String) : Except Error (CheckedFunctionRun layout name) :=
  match selectedEq : selectedFunctions program name with
  | [] => .error (.functionNotFound name)
  | [info] =>
      match parametersEq : parameterBindings? program info with
      | none => .error (.malformedAnalysis "unsupported function parameters")
      | some parameters => do
          let body ← checkBody layout info.symbolId info.returnType [parameters] info.body.value
          if localsEq : body.statement.declaredIds = info.locals then
            let function : Function := {
              name, returnType := info.returnType, parameters, locals := info.locals,
              body := body.statement }
            .ok ⟨function, info,
              .checked selectedEq rfl parametersEq body.evidence localsEq⟩
          else .error (.malformedAnalysis "resolved local declarations do not match analysis")
  | _ => .error (.ambiguousFunction name)

def resolveIR (program : Program) (layout : MemoryLayout.Certificate program) (name : String) :
    Except Error Function :=
  (checkFunction layout name).map (·.function)

private theorem resolveIR_eq_ok_of_checkFunction_eq_ok {program : Program}
    {layout : MemoryLayout.Certificate program} {name : String}
    {checked : CheckedFunctionRun layout name}
    (checkedEq : checkFunction layout name = .ok checked) :
    resolveIR program layout name = .ok checked.function := by
  unfold resolveIR
  rw [checkedEq]
  rfl

def Raw.embedOutcome : Raw.FunctionOutcome → Simpl.XState State Unit
  | .success state => .normal state
  | .undefinedBehavior => .fault ()

theorem Raw.embedOutcome_injective : Function.Injective Raw.embedOutcome := by
  intro left right
  cases left <;> cases right <;> simp_all [Raw.embedOutcome]

theorem CheckedResolution.rawToResolved {program : Program}
    {layout : MemoryLayout.Certificate program}
    (resolution : CheckedResolution layout name info rawBody function)
    (execution : Raw.FunctionExec layout name info rawBody state outcome) :
    Function.Exec layout function state (Raw.embedOutcome outcome) := by
  cases resolution with
  | @checked parameters resolvedBody selected raw parametersEq body locals =>
      subst rawBody
      have environmentEq : Raw.parameterEnv? program info.symbolId info.parameters =
          some [parameters] := by
        unfold parameterBindings? at parametersEq
        cases found : Raw.parameterEnv? program info.symbolId info.parameters with
        | none => simp [found] at parametersEq
        | some environments =>
            cases environments with
            | nil => simp [found] at parametersEq
            | cons environment environments =>
                cases environments with
                | cons next tail => simp [found] at parametersEq
                | nil => simp [found] at parametersEq; cases parametersEq; rfl
      cases execution with
      | returned found rawExecution =>
          rw [environmentEq] at found
          cases Option.some.inj found
          exact .returned (body.rawToResolved rawExecution)
      | fault found rawExecution =>
          rw [environmentEq] at found
          cases Option.some.inj found
          exact .fault (body.rawToResolved rawExecution)
      | fellOffVoid typeEq found rawExecution =>
          rw [environmentEq] at found
          cases Option.some.inj found
          exact .fellOffVoid typeEq (body.rawToResolved rawExecution)
      | fellOffMain nameEq typeEq found rawExecution =>
          rw [environmentEq] at found
          cases Option.some.inj found
          exact .fellOffMain nameEq typeEq (body.rawToResolved rawExecution)
      | fellOffFault notVoid notMain found rawExecution =>
          rw [environmentEq] at found
          cases Option.some.inj found
          exact .fellOffFault notVoid notMain (body.rawToResolved rawExecution)

theorem CheckedResolution.resolvedToRaw {program : Program}
    {layout : MemoryLayout.Certificate program}
    (resolution : CheckedResolution layout name info rawBody function)
    (execution : Function.Exec layout function state result) :
    ∃ outcome, result = Raw.embedOutcome outcome ∧
      Raw.FunctionExec layout name info rawBody state outcome := by
  cases resolution with
  | @checked parameters resolvedBody selected raw parametersEq body locals =>
      subst rawBody
      have environmentEq : Raw.parameterEnv? program info.symbolId info.parameters =
          some [parameters] := by
        unfold parameterBindings? at parametersEq
        cases found : Raw.parameterEnv? program info.symbolId info.parameters with
        | none => simp [found] at parametersEq
        | some environments =>
            cases environments with
            | nil => simp [found] at parametersEq
            | cons environment environments =>
                cases environments with
                | cons next tail => simp [found] at parametersEq
                | nil => simp [found] at parametersEq; cases parametersEq; rfl
      cases execution with
      | returned resolvedExecution =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := body.resolvedToRaw resolvedExecution
          cases raw_returned_of_embed_eq equality
          exact ⟨.success _, rfl, .returned environmentEq rawExecution⟩
      | fault resolvedExecution =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := body.resolvedToRaw resolvedExecution
          cases raw_fault_of_embed_eq equality
          exact ⟨.undefinedBehavior, rfl, .fault environmentEq rawExecution⟩
      | fellOffVoid typeEq resolvedExecution =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := body.resolvedToRaw resolvedExecution
          cases raw_normal_of_embed_eq equality
          exact ⟨.success _, rfl, .fellOffVoid typeEq environmentEq rawExecution⟩
      | fellOffMain nameEq typeEq resolvedExecution =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := body.resolvedToRaw resolvedExecution
          cases raw_normal_of_embed_eq equality
          exact ⟨.success _, rfl, .fellOffMain nameEq typeEq environmentEq rawExecution⟩
      | fellOffFault notVoid notMain resolvedExecution =>
          obtain ⟨rawOutcome, equality, rawExecution⟩ := body.resolvedToRaw resolvedExecution
          cases raw_normal_of_embed_eq equality
          exact ⟨.undefinedBehavior, rfl,
            .fellOffFault notVoid notMain environmentEq rawExecution⟩

structure StructuralResolution {program : Program} (layout : MemoryLayout.Certificate program)
    (name : String) (info : FunctionInfo) (rawBody : Body) (function : Function) where
  private mk ::
  checked : CheckedResolution layout name info rawBody function

def Raw.Equivalent {program : Program} (layout : MemoryLayout.Certificate program)
    (name : String) (info : FunctionInfo) (rawBody : Body) (function : Function) : Prop :=
  (∀ state outcome, Raw.FunctionExec layout name info rawBody state outcome →
    Simpl.Exec emptyEnvironment (function.command layout) (.normal state)
      (Raw.embedOutcome outcome)) ∧
  (∀ state result, Simpl.Exec emptyEnvironment (function.command layout) (.normal state) result →
    ∃ outcome, result = Raw.embedOutcome outcome ∧
      Raw.FunctionExec layout name info rawBody state outcome)

theorem StructuralResolution.compose
    (resolution : StructuralResolution layout name info rawBody function) :
    Raw.Equivalent layout name info rawBody function := by
  constructor
  · intro state outcome rawExecution
    exact Function.command_correct layout
      (resolution.checked.rawToResolved rawExecution)
  · intro state result simplExecution
    exact resolution.checked.resolvedToRaw
      (Function.command_complete layout simplExecution)

structure ResolvedCertificate (program : Program) (layout : MemoryLayout.Certificate program)
    (name : String) (function : Function) where
  private mk ::
  functionInfo : FunctionInfo
  rawBody : Body
  resolution : StructuralResolution layout name functionInfo rawBody function
  exactResolution : resolveIR program layout name = .ok function
  supported : SimplConv.Kernel.Supported (function.command layout)

structure ResolvedCertified (program : Program) (layout : MemoryLayout.Certificate program)
    (name : String) where
  function : Function
  certificate : ResolvedCertificate program layout name function

def certifyResolved (program : Program) (layout : MemoryLayout.Certificate program)
    (name : String) : Except Error (ResolvedCertified program layout name) :=
  match checkedEq : checkFunction layout name with
  | .error error => .error error
  | .ok checked => .ok {
      function := checked.function
      certificate := {
        functionInfo := checked.info
        rawBody := checked.info.body
        resolution := ⟨checked.resolution⟩
        exactResolution := resolveIR_eq_ok_of_checkFunction_eq_ok checkedEq
        supported := checked.function.supported layout } }

/-!
The complete certificate is indexed by the exact frontend invocation.  Its
program field is tied to the frontend result, and its layout field is the
generated `MemoryLayout.Certificate` for that same program.
-/
structure Certificate (target : Target) (files : Preprocessor.FileMap)
    (entry name : String) (function : Function) where
  private mk ::
  program : Program
  analyzed : (Frontend.preprocessAndAnalyze target files entry).program = some program
  frontendSuccess : (Frontend.preprocessAndAnalyze target files entry).isSuccess = true
  layout : MemoryLayout.Certificate program
  image : MemoryModel.Image program
  functionInfo : FunctionInfo
  rawBody : Body
  resolution : StructuralResolution layout name functionInfo rawBody function
  exactResolution : resolveIR program layout name = .ok function
  supported : SimplConv.Kernel.Supported (function.command layout)

/-- Function-entry state backed by the certified initialized static image. -/
def Certificate.initialState
    (certificate : Certificate target files entry name function) : State :=
  { heap := certificate.image.bytes }

@[simp] theorem Certificate.initialState_heap
    (certificate : Certificate target files entry name function) :
    certificate.initialState.heap = certificate.image.bytes := rfl

@[simp] theorem Certificate.initialState_not_returned
    (certificate : Certificate target files entry name function) :
    certificate.initialState.returned = false := rfl

structure Certified (target : Target) (files : Preprocessor.FileMap)
    (entry name : String) where
  function : Function
  certificate : Certificate target files entry name function

theorem Certificate.finite_iff
    (certificate : Certificate target files entry name function) :
    ∀ state outcome,
      Raw.FunctionExec certificate.layout name certificate.functionInfo
          certificate.rawBody state outcome ↔
        Simpl.Exec emptyEnvironment (function.command certificate.layout) (.normal state)
          (Raw.embedOutcome outcome) := by
  intro state outcome
  have equivalence := certificate.resolution.compose
  constructor
  · exact equivalence.1 state outcome
  · intro execution
    obtain ⟨found, equality, raw⟩ := equivalence.2 state _ execution
    cases Raw.embedOutcome_injective equality.symm
    exact raw

def certifyFrontend (target : Target) (files : Preprocessor.FileMap)
    (entry name : String) : Except Error (Certified target files entry name) :=
  if targetEq : target = Target.arm then
    let frontend := Frontend.preprocessAndAnalyze target files entry
    match programEq : frontend.program with
    | none => .error .frontendFailure
    | some program =>
        if successEq : frontend.isSuccess = true then
          match layoutEq : MemoryLayout.certify program with
          | .error error => .error (.layout error)
          | .ok layout =>
              match imageEq : MemoryModel.initializeWith layout with
              | .error error => .error (.initialization error)
              | .ok image =>
                  match checkedEq : checkFunction layout name with
                  | .error error => .error error
                  | .ok checked => .ok {
                      function := checked.function
                      certificate := {
                        program
                        analyzed := by simpa [frontend] using programEq
                        frontendSuccess := by simpa [frontend] using successEq
                        layout
                        image
                        functionInfo := checked.info
                        rawBody := checked.info.body
                        resolution := ⟨checked.resolution⟩
                        exactResolution := resolveIR_eq_ok_of_checkFunction_eq_ok checkedEq
                        supported := checked.function.supported layout } }
        else .error .frontendFailure
  else .error .unsupportedTarget

end Zag.Lang.AutoCorres.CParser.MemorySimpl
