import Lang.AutoCorres.CParser.SyntaxTransforms
import Zag.Data
import Init.WFTactics

/-!
# StrictC program analysis

Pure foundations of `program_analysis.ML` and `expression_typing.ML` from pinned l4v commit
`bc2599a59c43e673dca021b10b9841e9b8da4430`: typedef elimination,
nominal tag and symbol allocation, expression typing, direct-call discovery,
constant array bounds, and ABI struct layout.
-/

namespace Zag.Lang.AutoCorres.CParser.ProgramAnalysis

open Zag

inductive AnalysisError where
  | syntax (error : CParser.Error)
  | unresolvedTypedef (region : Region) (name : String)
  | duplicateTag (region : Region) (name : String)
  | duplicateField (region : Region) (structName fieldName : String)
  | duplicateSymbol (region : Region) (name : String)
  | incompatibleSymbol (region : Region) (name : String)
  | invalidArrayBound (region : Region) (value : Int)
  | nonConstantExpression (region : Region)
  | divisionByZero (region : Region)
  | incompleteStruct (region : Region) (name : String)
  | invalidLayout (region : Region) (typeName : String)
  | undeclaredIdentifier (region : Region) (name : String)
  | invalidExpression (region : Region) (message : String)
  | incompatibleTypes (region : Region) (expected actual : String)
  | invalidTypeAbbreviations
deriving Repr, Inhabited

inductive SymbolKind where
  | global
  | local (functionId : Nat)
  | staticLocal (functionId : Nat)
  | parameter (functionId : Nat)
  | function
  | enumConstant (value : Int)
deriving Repr, DecidableEq, Inhabited

inductive Linkage where
  | internal
  | external
deriving Repr, DecidableEq, Inhabited

structure SymbolInfo where
  id : Nat
  sourceName : String
  type : AnalyzedCType
  kind : SymbolKind
  region : Region
  linkage : Option Linkage := none
deriving Repr, Inhabited

structure FieldInfo where
  sourceName : String
  type : AnalyzedCType
  offset : Nat
  region : Region
deriving Repr, Inhabited

structure StructInfo where
  id : Nat
  sourceName : String
  canonicalName : String
  fields : List FieldInfo
  size : Nat
  alignment : Nat
  defined : Bool
  complete : Bool
  region : Region
deriving Repr, Inhabited

structure FunctionInfo where
  symbolId : Nat
  returnType : AnalyzedCType
  parameters : List Nat
  locals : List Nat
  specifications : List FunctionSpec
  body : Body
  region : Region
deriving Repr, Inhabited

structure ExpressionInfo where
  region : Region
  type : AnalyzedCType
deriving Repr, Inhabited

structure CallInfo where
  caller : Option Nat
  callee : Option Nat
  region : Region
deriving Repr, Inhabited

inductive StaticInitialization where
  | zero
  | explicit (initializer : Initializer)
deriving Repr, Inhabited

structure StaticObjectInfo where
  symbolId : Nat
  initialization : StaticInitialization
  initializerValues : Option (List Int) := none
  region : Region
deriving Repr, Inhabited

structure Program where
  target : Target
  translationUnit : TranslationUnit
  typedefs : List (String × AnalyzedCType)
  typeAbbrevs : TypeAbbrevCtx
  structs : List StructInfo
  symbols : List SymbolInfo
  functions : List FunctionInfo
  globals : List Nat
  expressionTypes : List ExpressionInfo
  calls : List CallInfo
  staticObjects : List StaticObjectInfo := []

namespace Program

def structById? (program : Program) (id : Nat) : Option StructInfo :=
  program.structs.find? (·.id = id)

def structBySourceName? (program : Program) (name : String) : Option StructInfo :=
  program.structs.find? (·.sourceName = name)

def symbolById? (program : Program) (id : Nat) : Option SymbolInfo :=
  program.symbols.find? (·.id = id)

def symbolsNamed (program : Program) (name : String) : List SymbolInfo :=
  program.symbols.filter (·.sourceName = name)

def expressionTypesAt (program : Program) (region : Region) : List AnalyzedCType :=
  program.expressionTypes.filterMap fun info =>
      if info.region = region then some info.type else none

def staticObjectBySymbolId? (program : Program) (symbolId : Nat) : Option StaticObjectInfo :=
  program.staticObjects.find? (·.symbolId = symbolId)

end Program

private inductive TagBinding where
  | structTag (id : Nat)
  | enumTag (id : Nat)
deriving Repr, DecidableEq, Inhabited

private structure State where
  target : Target
  nextStructId : Nat := 0
  nextEnumId : Nat := 0
  nextSymbolId : Nat := 0
  tagScopes : List (List (String × TagBinding)) := [[]]
  symbolScopes : List (List (String × Nat)) := [[]]
  structs : List StructInfo := []
  symbols : List SymbolInfo := []
  functions : List FunctionInfo := []
  globals : List Nat := []
  definedSymbols : List Nat := []
  definedFunctions : List Nat := []
  expressionTypes : List ExpressionInfo := []
  calls : List CallInfo := []
  staticObjects : List StaticObjectInfo := []

private abbrev AnalyzeM := StateT State (Except AnalysisError)

private def throwAt (error : AnalysisError) : AnalyzeM α :=
  throw error

private def lookupBinding (name : String) : List (String × α) → Option α
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = name then some value else lookupBinding name rest

private def lookupScopes (name : String) : List (List (String × α)) → Option α
  | [] => none
  | scope :: scopes =>
      match lookupBinding name scope with
      | some value => some value
      | none => lookupScopes name scopes

private def lookupScopesDepth (name : String) : List (List (String × α)) → Option (Nat × α)
  | [] => none
  | scope :: scopes =>
      match lookupBinding name scope with
      | some value => some (0, value)
      | none => (lookupScopesDepth name scopes).map fun (depth, value) => (depth + 1, value)

private def lookupCurrentScope (name : String) : List (List (String × α)) → Option α
  | [] => none
  | scope :: _ => lookupBinding name scope

private def lookupLastScope (name : String) : List (List (String × α)) → Option α
  | [] => none
  | [scope] => lookupBinding name scope
  | _ :: scopes => lookupLastScope name scopes

private def insertCurrentScope (name : String) (value : α) :
    List (List (String × α)) → List (List (String × α))
  | [] => [[(name, value)]]
  | scope :: scopes => ((name, value) :: scope) :: scopes

private def insertLastScope (name : String) (value : α) :
    List (List (String × α)) → List (List (String × α))
  | [] => [[(name, value)]]
  | [scope] => [((name, value) :: scope)]
  | scope :: scopes => scope :: insertLastScope name value scopes

private def pushScopes : AnalyzeM Unit :=
  modify fun state => { state with
    tagScopes := [] :: state.tagScopes
    symbolScopes := [] :: state.symbolScopes }

private def popScopes : AnalyzeM Unit := do
  let state ← get
  match state.tagScopes, state.symbolScopes with
  | _ :: tagScopes, _ :: symbolScopes =>
      set { state with tagScopes, symbolScopes }
  | _, _ => pure ()

private def canonicalStructName (name : String) (id : Nat) : String :=
  name ++ "#" ++ toString id

private def canonicalEnumName (name : String) (id : Nat) : String :=
  name ++ "#enum#" ++ toString id

private def tagNamespaceKey (name : String) : String :=
  if name.endsWith "_C" then name else name ++ "_C"

private def allocateStruct (name : Located String) : AnalyzeM Nat := do
  let state ← get
  let id := state.nextStructId
  let info : StructInfo :=
    { id
      sourceName := name.value
      canonicalName := canonicalStructName name.value id
      fields := []
      size := 0
      alignment := 0
      defined := false
      complete := false
      region := name.region }
  set { state with
    nextStructId := id + 1
    tagScopes := insertCurrentScope name.value (.structTag id) state.tagScopes
    structs := state.structs ++ [info] }
  pure id

private def ensureTag (name : String) (region : Region) : AnalyzeM Nat := do
  let state ← get
  match lookupScopes name state.tagScopes with
  | some (.structTag id) => pure id
  | some (.enumTag _) => throwAt (.duplicateTag region name)
  | none => allocateStruct { value := name, region }

private def structById? (state : State) (id : Nat) : Option StructInfo :=
  state.structs.find? (·.id = id)

private def updateStruct (id : Nat) (update : StructInfo → StructInfo) : AnalyzeM Unit :=
  modify fun state =>
    { state with structs := state.structs.map fun info =>
        if info.id = id then update info else info }

private def intByteWidth (target : Target) (kind : IntKind) : Option Nat :=
  if target.charWidth = 0 then none else some (target.intWidthOf kind / target.charWidth)

private def pointerByteWidth (target : Target) : Option Nat :=
  if target.charWidth = 0 then none else some (target.pointerWidth / target.charWidth)

private def boolByteWidth (target : Target) : Option Nat :=
  if target.charWidth = 0 then none else some (target.boolWidth / target.charWidth)

private def roundUp (alignment value : Nat) : Nat :=
  if alignment = 0 || value % alignment = 0 then value
  else (value / alignment + 1) * alignment

private def layoutOf (region : Region) (type : AnalyzedCType) : AnalyzeM (Nat × Nat) := do
  let state ← get
  match type with
  | .signed kind | .unsigned kind =>
      match intByteWidth state.target kind with
      | some width => pure (width, width)
      | none => throwAt (.invalidLayout region (CType.typeName type))
  | .plainChar => pure (1, 1)
  | .bool =>
      match boolByteWidth state.target with
      | some width => pure (width, width)
      | none => throwAt (.invalidLayout region (CType.typeName type))
  | .ptr _ =>
      match pointerByteWidth state.target with
      | some width => pure (width, width)
      | none => throwAt (.invalidLayout region (CType.typeName type))
  | .enumTy _ =>
      match intByteWidth state.target .int with
      | some width => pure (width, width)
      | none => throwAt (.invalidLayout region (CType.typeName type))
  | .array element (some count) =>
      if count < 0 then throwAt (.invalidArrayBound region count)
      else
        let (size, alignment) ← layoutOf region element
        pure (Int.toNat count * size, alignment)
  | .structTy canonicalName =>
      match state.structs.find? (·.canonicalName = canonicalName) with
      | some info =>
          if info.complete then pure (info.size, info.alignment)
          else throwAt (.incompleteStruct region info.sourceName)
      | none => throwAt (.incompleteStruct region canonicalName)
  | .array _ none | .bitfield _ _ | .ident _ | .function _ _ | .void =>
      throwAt (.invalidLayout region (CType.typeName type))

private def tryCompleteStruct (id : Nat) : AnalyzeM Bool := do
  let state ← get
  match structById? state id with
  | none => pure false
  | some info =>
      if !info.defined || info.complete then return info.complete
      let mut offset := 0
      let mut alignment := 0
      let mut fields := []
      for field in info.fields do
        match (layoutOf field.region field.type).run state with
        | .error (.incompleteStruct ..) => return false
        | .error error => throwAt error
        | .ok ((size, fieldAlignment), _) =>
            offset := roundUp fieldAlignment offset
            fields := fields ++ [{ field with offset }]
            offset := offset + size
            alignment := max alignment fieldAlignment
      let size := roundUp alignment offset
      updateStruct id fun current => { current with fields, size, alignment, complete := true }
      pure true

private def retryPendingStructsPass : List StructInfo → AnalyzeM Unit
  | [] => pure ()
  | info :: rest => do
      let _ ← tryCompleteStruct info.id
      retryPendingStructsPass rest

private def retryPendingStructsFor (structs : List StructInfo) : Nat → AnalyzeM Unit
  | 0 => pure ()
  | passes + 1 => do
      retryPendingStructsPass structs
      retryPendingStructsFor structs passes

private def retryPendingStructs : AnalyzeM Unit := do
  let structs := (← get).structs
  retryPendingStructsFor structs structs.length

private def rejectIncompleteStructs : AnalyzeM Unit := do
  retryPendingStructs
  let state ← get
  match state.structs.find? fun info => info.defined && !info.complete with
  | some info => throwAt (.incompleteStruct info.region info.sourceName)
  | none => pure ()

private def truncateUnsigned (width : Nat) (value : Int) : Int :=
  let modulus := Int.ofNat (2 ^ width)
  ((value % modulus) + modulus) % modulus

private def castInteger (target : Target) (type : AnalyzedCType) (value : Int) : Int :=
  let signed (width : Nat) :=
    let value := truncateUnsigned width value
    let sign := Int.ofNat (2 ^ (width - 1))
    if value ≥ sign then value - Int.ofNat (2 ^ width) else value
  match type with
  | .bool => if value = 0 then 0 else 1
  | .unsigned kind => truncateUnsigned (target.intWidthOf kind) value
  | .signed kind => signed (target.intWidthOf kind)
  | .plainChar =>
      if target.charSigned then signed target.charWidth else truncateUnsigned target.charWidth value
  | .enumTy _ => signed target.intWidth
  | _ => value

private def castRawInteger (target : Target) (type : CType Expr) (value : Int) : Int :=
  match type with
  | .bool => castInteger target .bool value
  | .unsigned kind => castInteger target (.unsigned kind) value
  | .signed kind => castInteger target (.signed kind) value
  | .plainChar => castInteger target .plainChar value
  | .enumTy name => castInteger target (.enumTy name) value
  | _ => value

private def requireCompleteObjectType (region : Region) : AnalyzedCType → AnalyzeM Unit
  | .structTy name => do
      let state ← get
      match state.structs.find? (·.canonicalName = name) with
      | some info =>
          if info.complete then pure () else throwAt (.incompleteStruct region info.sourceName)
      | none => throwAt (.incompleteStruct region name)
  | .array _ none => throwAt (.invalidLayout region "incomplete array object type")
  | .array element (some _) => requireCompleteObjectType region element
  | .void | .function .. => throwAt (.invalidLayout region "incomplete object type")
  | _ => pure ()

private def requireDeclarationObjectType (region : Region) : AnalyzedCType → AnalyzeM Unit
  | .structTy _ => pure ()
  | .array element none => requireCompleteObjectType region element
  | type => requireCompleteObjectType region type

private def validateSymbolTypes : AnalyzeM Unit := do
  let symbols := (← get).symbols
  for symbol in symbols do
    match symbol.kind, symbol.type with
    | .function, .function returnType parameters =>
        if returnType != .void then requireCompleteObjectType symbol.region returnType
        for parameter in parameters do
          requireCompleteObjectType symbol.region parameter
    | .enumConstant _, _ => pure ()
    | .global, type =>
        if (← get).staticObjects.any (·.symbolId = symbol.id) then
          requireCompleteObjectType symbol.region type
        else
          requireDeclarationObjectType symbol.region type
    | _, type => requireCompleteObjectType symbol.region type

def numericLiteralType (target : Target) (info : NumLiteralInfo) : Option AnalyzedCType :=
  let suffix := info.suffix.toLower
  let unsigned := suffix.contains 'u'
  let longLong := suffix.contains "ll"
  let long := !longLong && suffix.contains 'l'
  let candidates : List AnalyzedCType :=
    if unsigned && longLong then [.unsigned .longLong]
    else if unsigned && long then [.unsigned .long, .unsigned .longLong]
    else if unsigned then [.unsigned .int, .unsigned .long, .unsigned .longLong]
    else if longLong then [.signed .longLong]
    else if long then
      if info.base = .decimal then [.signed .long, .signed .longLong]
      else [.signed .long, .unsigned .long, .signed .longLong, .unsigned .longLong]
    else if info.base = .decimal then [.signed .int, .signed .long, .signed .longLong]
    else [.signed .int, .unsigned .int, .signed .long, .unsigned .long,
      .signed .longLong, .unsigned .longLong]
  let fits : AnalyzedCType → Bool
    | .signed kind => info.value ≤ Target.signedMax (target.intWidthOf kind)
    | .unsigned kind => info.value ≤ Target.unsignedMax (target.intWidthOf kind)
    | _ => false
  candidates.find? fits

private def integerObjectType : AnalyzedCType → Bool
  | .signed _ | .unsigned _ | .plainChar | .bool | .enumTy _ | .bitfield _ _ => true
  | _ => false

private def rawIntegerObjectType : CType Expr → Bool
  | .signed _ | .unsigned _ | .plainChar | .bool | .enumTy _ => true
  | _ => false

private def integerConstantInfo (target : Target) (type : AnalyzedCType) :
    Option (Bool × Nat) :=
  match type.integerPromotions target with
  | .signed kind => some (true, target.intWidthOf kind)
  | .unsigned kind => some (false, target.intWidthOf kind)
  | _ => none

private def checkedConstant (region : Region) (target : Target)
    (type : AnalyzedCType) (value : Int) : AnalyzeM Int := do
  match integerConstantInfo target type with
  | some (false, _) => pure (castInteger target type value)
  | some (true, width) =>
      if Target.signedMin width ≤ value && value ≤ Target.signedMax width then pure value
      else throwAt (.nonConstantExpression region)
  | none => throwAt (.nonConstantExpression region)

private def truncDiv (left right : Int) : Int :=
  let quotient := Int.ofNat (left.natAbs / right.natAbs)
  if (left < 0) != (right < 0) then -quotient else quotient

private def truncMod (left right : Int) : Int :=
  left - truncDiv left right * right

private def integerBits (width : Nat) (value : Int) : Nat :=
  (((value % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width).toNat

private def constantExpressionType (state : State) : Expr → Except AnalysisError AnalyzedCType
  | .e ⟨node, region⟩ =>
      match node with
      | .constant ⟨.numConst info, _⟩ =>
          match numericLiteralType state.target info with
          | some type => .ok type
          | none => .error (.nonConstantExpression region)
      | .var name _ =>
          match lookupScopes name state.symbolScopes >>= fun id => state.symbols.find? (·.id = id) with
          | some ⟨_, _, type, .enumConstant _, _, _⟩ => .ok type
          | _ => .error (.nonConstantExpression region)
      | .unOp .not value | .mkBool value => do
          if integerObjectType (← constantExpressionType state value) then .ok (.signed .int)
          else .error (.nonConstantExpression region)
      | .unOp .negate value | .unOp .bitNegate value => do
          let type ← constantExpressionType state value
          if integerObjectType type then .ok (type.integerPromotions state.target)
          else .error (.nonConstantExpression region)
      | .unOp .addr _ => .error (.nonConstantExpression region)
      | .condExp condition thenExpr elseExpr => do
          if !integerObjectType (← constantExpressionType state condition) then
            .error (.nonConstantExpression region)
          else
            (CType.arithmeticConversion state.target (← constantExpressionType state thenExpr)
              (← constantExpressionType state elseExpr)).mapError
                fun _ => .nonConstantExpression region
      | .binOp operator left right => do
          let leftType ← constantExpressionType state left
          let rightType ← constantExpressionType state right
          if !integerObjectType leftType || !integerObjectType rightType then
            .error (.nonConstantExpression region)
          else if operator matches .logAnd | .logOr then
            .ok (.signed .int)
          else if operator matches .equals | .notEquals | .lt | .gt | .leq | .geq then
            match CType.arithmeticConversion state.target leftType rightType with
            | .ok _ => .ok (.signed .int)
            | .error _ => .error (.nonConstantExpression region)
          else if operator matches .lShift | .rShift then
            .ok (leftType.integerPromotions state.target)
          else
            (CType.arithmeticConversion state.target leftType rightType).mapError
              fun _ => .nonConstantExpression region
      | .typeCast type value => do
          if !rawIntegerObjectType type.value ||
              !integerObjectType (← constantExpressionType state value) then
            .error (.nonConstantExpression region)
          else
            match type.value with
            | .signed kind => .ok (.signed kind)
            | .unsigned kind => .ok (.unsigned kind)
            | .bool => .ok .bool
            | .plainChar => .ok .plainChar
            | .enumTy name => .ok (.enumTy name)
            | _ => .error (.nonConstantExpression region)
      | .sizeof _ | .sizeofTy _ => .ok CType.ImplementationTypes.sizeT
      | _ => .error (.nonConstantExpression region)
termination_by expression => sizeOf expression
decreasing_by all_goals simp_wf <;> decreasing_trivial

private def sizeofAnalyzedType (region : Region) (type : AnalyzedCType) : AnalyzeM Int := do
  let (size, _) ← layoutOf region type
  pure (Int.ofNat size)

private def sizeofOperandType (state : State) (expression : Expr) :
    Except AnalysisError AnalyzedCType :=
  match constantExpressionType state expression with
  | .ok type => .ok type
  | .error error =>
      match expression with
      | .e ⟨.var name _, _⟩ =>
          match lookupScopes name state.symbolScopes >>= fun id => state.symbols.find? (·.id = id) with
          | some symbol => .ok symbol.type
          | none => .error error
      | _ => .error error

mutual
private def sizeofRawType (region : Region) :
    CType Expr → AnalyzeM Int
  | .signed kind | .unsigned kind => do
      let state ← get
      match intByteWidth state.target kind with
      | some width => pure (Int.ofNat width)
      | none => throwAt (.invalidLayout region (IntKind.name kind))
  | .plainChar => pure 1
  | .bool => do
      let state ← get
      match boolByteWidth state.target with
      | some width => pure (Int.ofNat width)
      | none => throwAt (.invalidLayout region "_Bool")
  | .enumTy _ => do
      let state ← get
      match intByteWidth state.target .int with
      | some width => pure (Int.ofNat width)
      | none => throwAt (.invalidLayout region "enum")
  | .ptr _ => do
      let state ← get
      match pointerByteWidth state.target with
      | some width => pure (Int.ofNat width)
      | none => throwAt (.invalidLayout region "pointer")
  | .structTy name => do
      let state ← get
      match lookupScopes name state.tagScopes with
      | some (.structTag id) =>
          match structById? state id with
          | some info =>
              if info.complete then pure (Int.ofNat info.size)
              else throwAt (.incompleteStruct region info.sourceName)
          | none => throwAt (.incompleteStruct region name)
      | _ => throwAt (.incompleteStruct region name)
  | .array type (some countExpression) => do
      let count ← constantValue countExpression
      if count < 1 then throwAt (.invalidArrayBound region count)
      else return count * (← sizeofRawType region type)
  | type => throwAt (.invalidLayout region (CType.typeNameWith (fun _ => "") type))

private def constantValue (expression : Expr) : AnalyzeM Int := do
  let state ← get
  let expressionType ← match constantExpressionType state expression with
    | .ok type => pure type
    | .error error => throwAt error
  match expression with
  | .e ⟨node, region⟩ =>
      match node with
      | .constant ⟨.numConst info, _⟩ =>
          pure (castInteger state.target expressionType info.value)
      | .var name _ =>
          match lookupScopes name state.symbolScopes with
          | some id =>
              match state.symbols.find? (·.id = id) with
              | some ⟨_, _, _, .enumConstant value, _, _⟩ => pure value
              | _ => throwAt (.nonConstantExpression region)
          | none => throwAt (.nonConstantExpression region)
      | .unOp .negate value => do
          checkedConstant region state.target expressionType
            (-(← constantValue value))
      | .unOp .not value => return if (← constantValue value) = 0 then 1 else 0
      | .unOp .bitNegate value => do
          pure (castInteger state.target expressionType (~~~(← constantValue value)))
      | .condExp condition thenExpr elseExpr =>
          let resultType ← match constantExpressionType state expression with
            | .ok type => pure type
            | .error error => throwAt error
          if (← constantValue condition) = 0 then
            return castInteger state.target resultType (← constantValue elseExpr)
          else return castInteger state.target resultType (← constantValue thenExpr)
      | .binOp .logAnd left right =>
          if (← constantValue left) = 0 then pure 0
          else return if (← constantValue right) = 0 then 0 else 1
      | .binOp .logOr left right =>
          if (← constantValue left) != 0 then pure 1
          else return if (← constantValue right) = 0 then 0 else 1
      | .binOp operator left right =>
          let leftType ← match constantExpressionType state left with
            | .ok type => pure type
            | .error error => throwAt error
          let rightType ← match constantExpressionType state right with
            | .ok type => pure type
            | .error error => throwAt error
          let leftValue ← constantValue left
          let rightValue ← constantValue right
          let convertedType ← match CType.arithmeticConversion state.target leftType rightType with
            | .ok type => pure type
            | .error _ => throwAt (.nonConstantExpression region)
          let left := castInteger state.target convertedType leftValue
          let right := castInteger state.target convertedType rightValue
          match operator with
          | .plus => checkedConstant region state.target convertedType (left + right)
          | .minus => checkedConstant region state.target convertedType (left - right)
          | .times => checkedConstant region state.target convertedType (left * right)
          | .divides =>
              if right = 0 then throwAt (.divisionByZero region)
              else if let some (true, width) := integerConstantInfo state.target convertedType then
                if left = Target.signedMin width && right = -1 then
                  throwAt (.nonConstantExpression region)
                else pure (truncDiv left right)
              else pure (truncDiv left right)
          | .modulus =>
              if right = 0 then throwAt (.divisionByZero region)
              else if let some (true, width) := integerConstantInfo state.target convertedType then
                if left = Target.signedMin width && right = -1 then
                  throwAt (.nonConstantExpression region)
                else pure (truncMod left right)
              else pure (truncMod left right)
          | .equals => pure (if left = right then 1 else 0)
          | .notEquals => pure (if left = right then 0 else 1)
          | .lt => pure (if left < right then 1 else 0)
          | .gt => pure (if left > right then 1 else 0)
          | .leq => pure (if left ≤ right then 1 else 0)
          | .geq => pure (if left ≥ right then 1 else 0)
          | .lShift =>
              let leftType := leftType.integerPromotions state.target
              let rightType := rightType.integerPromotions state.target
              let left := castInteger state.target leftType leftValue
              let right := castInteger state.target rightType rightValue
              match integerConstantInfo state.target leftType with
              | none => throwAt (.nonConstantExpression region)
              | some (signed, width) =>
                  if right < 0 || right ≥ width then throwAt (.nonConstantExpression region)
                  else if signed && left < 0 then throwAt (.nonConstantExpression region)
                  else checkedConstant region state.target leftType (Int.shiftLeft left right.toNat)
          | .rShift =>
              let leftType := leftType.integerPromotions state.target
              let rightType := rightType.integerPromotions state.target
              let left := castInteger state.target leftType leftValue
              let right := castInteger state.target rightType rightValue
              match integerConstantInfo state.target leftType with
              | none => throwAt (.nonConstantExpression region)
              | some (_, width) =>
                  if right < 0 || right ≥ width then throwAt (.nonConstantExpression region)
                  else pure (castInteger state.target leftType (Int.shiftRight left right.toNat))
          | .bitwiseAnd =>
              match integerConstantInfo state.target convertedType with
              | some (_, width) => pure (castInteger state.target convertedType <|
                  Int.ofNat (Nat.land (integerBits width left) (integerBits width right)))
              | none => throwAt (.nonConstantExpression region)
          | .bitwiseOr =>
              match integerConstantInfo state.target convertedType with
              | some (_, width) => pure (castInteger state.target convertedType <|
                  Int.ofNat (Nat.lor (integerBits width left) (integerBits width right)))
              | none => throwAt (.nonConstantExpression region)
          | .bitwiseXor =>
              match integerConstantInfo state.target convertedType with
              | some (_, width) => pure (castInteger state.target convertedType <|
                  Int.ofNat (Nat.xor (integerBits width left) (integerBits width right)))
              | none => throwAt (.nonConstantExpression region)
          | .logAnd | .logOr => unreachable!
      | .typeCast type value =>
          return castRawInteger state.target type.value (← constantValue value)
      | .sizeof value => do
          let type ← match sizeofOperandType state value with
            | .ok type => pure type
            | .error error => throwAt error
          sizeofAnalyzedType region type
      | .sizeofTy type => sizeofRawType type.region type.value
      | .mkBool value => return if (← constantValue value) = 0 then 0 else 1
      | _ => throwAt (.nonConstantExpression region)
end

private def resolveType (region : Region) : CType Expr → AnalyzeM AnalyzedCType
  | .signed kind => pure (.signed kind)
  | .unsigned kind => pure (.unsigned kind)
  | .bool => pure .bool
  | .plainChar => pure .plainChar
  | .structTy name => do
      let id ← ensureTag name region
      let state ← get
      match structById? state id with
      | some info => pure (.structTy info.canonicalName)
      | none => throwAt (.incompleteStruct region name)
  | .enumTy none => pure (.enumTy none)
  | .enumTy (some name) => do
      let state ← get
      match lookupScopes (tagNamespaceKey name) state.tagScopes with
      | some (.enumTag id) => pure (.enumTy (some (canonicalEnumName name id)))
      | some (.structTag _) => throwAt (.duplicateTag region name)
      | none => throwAt (.invalidExpression region s!"unknown enum tag {name}")
  | .ptr type => return .ptr (← resolveType region type)
  | .array type size => do
      let type ← resolveType region type
      match size with
      | none => pure (.array type none)
      | some expression =>
          let count ← constantValue expression
          if count < 1 then throwAt (.invalidArrayBound region count)
          else pure (.array type (some count))
  | .bitfield signed width =>
      return .bitfield signed (← constantValue width)
  | .ident name => throwAt (.unresolvedTypedef region name)
  | .function returnType parameterTypes =>
      return .function (← resolveType region returnType)
        (← parameterTypes.mapM (resolveType region))
  | .void => pure .void

private def declareStruct (name : Located String)
    (rawFields : List (CType Expr × Located String)) : AnalyzeM Unit := do
  let state ← get
  let id ← match lookupCurrentScope name.value state.tagScopes with
    | some (.structTag id) => pure id
    | some (.enumTag _) => throwAt (.duplicateTag name.region name.value)
    | none => allocateStruct name
  let state ← get
  if let some info := structById? state id then
    if info.defined && !rawFields.isEmpty then
      throwAt (.duplicateTag name.region name.value)
  let mut seen : List String := []
  let mut fields : List FieldInfo := []
  for (rawType, fieldName) in rawFields do
    if seen.contains fieldName.value then
      throwAt (.duplicateField fieldName.region name.value fieldName.value)
    seen := fieldName.value :: seen
    let type ← resolveType fieldName.region rawType
    fields := fields ++ [{
      sourceName := fieldName.value
      type
      offset := 0
      region := fieldName.region }]
  if rawFields.isEmpty then return
  updateStruct id fun info =>
    { info with fields, defined := true, complete := false, region := name.region }
  retryPendingStructs

private def symbolById? (state : State) (id : Nat) : Option SymbolInfo :=
  state.symbols.find? (·.id = id)

private def addGlobal (id : Nat) (state : State) : State :=
  if state.globals.contains id then state else { state with globals := state.globals ++ [id] }

private def updateSymbol (id : Nat) (update : SymbolInfo → SymbolInfo) : AnalyzeM Unit :=
  modify fun state => { state with symbols := state.symbols.map (fun symbol =>
    if symbol.id = id then update symbol else symbol) }

private def registerStaticObject (symbolId : Nat) (initializer : Option Initializer)
    (initializerValues : Option (List Int)) (region : Region) : AnalyzeM Unit :=
  modify fun state =>
    let initialization := initializer.map StaticInitialization.explicit |>.getD .zero
    if state.staticObjects.any (·.symbolId = symbolId) then
      { state with staticObjects := state.staticObjects.map fun object =>
          if object.symbolId = symbolId then
            let objectInitialization := match object.initialization, initializer with
              | .explicit previous, none => .explicit previous
              | _, _ => initialization
            let objectValues := match object.initialization, initializer with
              | .explicit _, none => object.initializerValues
              | _, _ => initializerValues
            { object with
              initialization := objectInitialization
              initializerValues := objectValues
              region := if initializer.isSome then region else object.region }
          else object }
    else
      { state with staticObjects := state.staticObjects ++
          [{ symbolId, initialization, initializerValues, region }] }

private def allocateGlobalSymbol (name : Located String) (type : AnalyzedCType) : AnalyzeM Nat := do
  let state ← get
  let id := state.nextSymbolId
  let symbol : SymbolInfo := {
    id
    sourceName := name.value
    type
    kind := .global
    region := name.region }
  set <| addGlobal id ({ state with
    nextSymbolId := id + 1
    symbolScopes := insertLastScope name.value id state.symbolScopes
    symbols := state.symbols ++ [symbol] })
  pure id

private def compatibleGlobalTypes (left right : AnalyzedCType) : Bool :=
  match left, right with
  | .array leftType leftSize, .array rightType rightSize =>
      leftType == rightType && (leftSize == rightSize || leftSize.isNone || rightSize.isNone)
  | _, _ => left == right

private def completeGlobalType (left right : AnalyzedCType) : AnalyzedCType :=
  match left, right with
  | .array _ none, type => type
  | type, .array _ none => type
  | _, _ => left

private def declareGlobalSymbol (name : Located String) (type : AnalyzedCType) : AnalyzeM Nat := do
  let state ← get
  match lookupLastScope name.value state.symbolScopes with
  | none => allocateGlobalSymbol name type
  | some id =>
      match symbolById? state id with
      | some symbol =>
          if symbol.kind == .global && compatibleGlobalTypes symbol.type type then
            updateSymbol id fun current =>
              { current with type := completeGlobalType current.type type }
            pure id
          else throwAt (.incompatibleSymbol name.region name.value)
      | none => allocateGlobalSymbol name type

private def bindBlockExtern (name : Located String) (id : Nat) : AnalyzeM Unit := do
  let state ← get
  match lookupCurrentScope name.value state.symbolScopes with
  | none => modify fun state =>
      { state with symbolScopes := insertCurrentScope name.value id state.symbolScopes }
  | some current =>
      if current = id then pure ()
      else throwAt (.incompatibleSymbol name.region name.value)

private def allocateSymbol (name : Located String) (type : AnalyzedCType)
    (kind : SymbolKind) : AnalyzeM Nat := do
  let state ← get
  let id := state.nextSymbolId
  let symbol : SymbolInfo := { id, sourceName := name.value, type, kind, region := name.region }
  let state := { state with
    nextSymbolId := id + 1
    symbolScopes := insertCurrentScope name.value id state.symbolScopes
    symbols := state.symbols ++ [symbol] }
  let state := match kind with
    | .global => addGlobal id state
    | _ => state
  set state
  pure id

private def declareSymbol (name : Located String) (type : AnalyzedCType)
    (kind : SymbolKind) : AnalyzeM Nat := do
  let state ← get
  let existing := match kind with
    | .global | .function =>
        (lookupCurrentScope name.value state.symbolScopes).map fun id => (0, id)
    | .local _ | .staticLocal _ | .parameter _ | .enumConstant _ =>
        lookupScopesDepth name.value state.symbolScopes
  match existing with
  | none => allocateSymbol name type kind
  | some (depth, id) =>
      if (kind matches .local _ | .staticLocal _ | .parameter _) && depth > 0 then
        allocateSymbol name type kind
      else
      match symbolById? state id with
      | none => allocateSymbol name type kind
      | some symbol =>
          match kind, symbol.kind with
          | .global, .global | .function, .function =>
              if symbol.type == type then pure id
              else throwAt (.incompatibleSymbol name.region name.value)
          | _, _ => throwAt (.duplicateSymbol name.region name.value)

private def declareFunction (returnType : CType Expr) (name : Located String)
    (parameters : List (CType Expr × Option String)) (linkage : Linkage) :
    AnalyzeM (Nat × AnalyzedCType) := do
  let returnType ← resolveType name.region returnType
  let parameterTypes ← parameters.mapM fun (type, _) =>
    return (← resolveType name.region type).paramNorm
  let functionType := CType.function returnType parameterTypes
  let id ← declareSymbol name functionType .function
  match (symbolById? (← get) id).bind (·.linkage) with
  | none => updateSymbol id fun symbol => { symbol with linkage := some linkage }
  | some .internal => pure ()
  | some .external =>
      if linkage == .internal then throwAt (.incompatibleSymbol name.region name.value)
      else pure ()
  pure (id, returnType)

private def declareEnum (name : Located (Option String))
    (enumerators : List (Located String × Option Expr)) : AnalyzeM Unit := do
  let region := name.region
  if let some tagName := name.value then
    let state ← get
    let key := tagNamespaceKey tagName
    if (lookupCurrentScope key state.tagScopes).isSome then
      throwAt (.duplicateTag region tagName)
    let id := state.nextEnumId
    set { state with
      nextEnumId := id + 1
      tagScopes := insertCurrentScope key (.enumTag id) state.tagScopes }
  let mut nextValue : Int := 0
  for (enumerator, explicit) in enumerators do
    let value ← match explicit with
      | some expression => constantValue expression
      | none => pure nextValue
    let _ ← declareSymbol enumerator (.signed .int) (.enumConstant value)
    nextValue := value + 1

private def recordExpression (region : Region) (type : AnalyzedCType) : AnalyzeM Unit :=
  modify fun state =>
    { state with expressionTypes := state.expressionTypes ++ [{ region, type }] }

private def assignmentCompatible (newType oldType : AnalyzedCType)
    (isNullPointerConstant : Bool) : Bool :=
  newType == oldType ||
    (newType.integerType && oldType.integerType) ||
    (newType == .bool && oldType.scalarType) ||
    (oldType.integerType && isNullPointerConstant && newType.ptrType) ||
    (newType.ptrType && oldType == .ptr .void) ||
    (oldType.ptrType && newType == .ptr .void)

private def nullPointerConstant (type : AnalyzedCType) (expression : Expr) : AnalyzeM Bool := do
  if type.integerType then
    let state ← get
    match (constantValue expression).run state with
    | .ok (value, _) => pure (value == 0)
    | .error _ => pure false
  else pure false

private def requireAssignment (region : Region) (expected actual : AnalyzedCType)
    (expression : Expr) : AnalyzeM Unit := do
  let isNullPointerConstant ←
    if expected.ptrType then nullPointerConstant actual expression else pure false
  if assignmentCompatible expected actual isNullPointerConstant then pure ()
  else throwAt (.incompatibleTypes region (CType.typeName expected) (CType.typeName actual))

private def isLValue : Expr → Bool
  | .e ⟨.var _ _, _⟩ | .e ⟨.structDot _ _, _⟩ | .e ⟨.arrayDeref _ _, _⟩ |
      .e ⟨.deref _, _⟩ => true
  | _ => false

private def functionDesignatorType : AnalyzedCType → AnalyzedCType
  | type@(.function ..) => .ptr type
  | .array element _ => .ptr element
  | type => type

private def arithmeticType (region : Region) (operator : BinOpType)
    (left right : AnalyzedCType) (leftExpr rightExpr : Expr) : AnalyzeM AnalyzedCType := do
  let target := (← get).target
  let relational := operator matches .equals | .notEquals | .lt | .gt | .leq | .geq
  let equality := operator matches .equals | .notEquals
  let pointerNull ← if equality then
      if left.ptrType then nullPointerConstant right rightExpr
      else if right.ptrType then nullPointerConstant left leftExpr
      else pure false
    else pure false
  if operator matches .logAnd | .logOr then
    if left.scalarType && right.scalarType then pure (.signed .int)
    else throwAt (.invalidExpression region "logical operator requires scalar operands")
  else if relational then
    if (left == right && left.scalarType) || (left.integerType && right.integerType) ||
        pointerNull || (left.ptrType && right.ptrType && equality &&
          (left == .ptr .void || right == .ptr .void)) then
      pure (.signed .int)
    else throwAt (.invalidExpression region "incompatible relational operands")
  else if left.integerType && right.integerType then
    match CType.arithmeticConversion target left right with
    | .ok type => pure type
    | .error error => throwAt (.invalidExpression region (reprStr error))
  else if left.ptrType && right.integerType && (operator matches .plus | .minus) then pure left
  else if right.ptrType && left.integerType && operator == .plus then pure right
  else if left.ptrType && right.ptrType && left == right && operator == .minus then
    pure CType.ImplementationTypes.ptrdiffT
  else throwAt (.invalidExpression region "invalid arithmetic operands")

mutual
  private def typeExpression (caller : Option Nat) : Expr → AnalyzeM AnalyzedCType
    | .e ⟨node, region⟩ => do
        let type ← match node with
          | .constant ⟨.numConst info, _⟩ =>
              match numericLiteralType (← get).target info with
              | some type => pure type
              | none => throwAt (.invalidExpression region "integer literal has no representable type")
          | .constant ⟨.stringLit _, _⟩ => pure (.ptr .plainChar)
          | .var name _ =>
              let state ← get
              match lookupScopes name state.symbolScopes with
              | some id =>
                  match symbolById? state id with
                  | some symbol => pure symbol.type
                  | none => throwAt (.undeclaredIdentifier region name)
              | none => throwAt (.undeclaredIdentifier region name)
          | .binOp operator left right =>
              arithmeticType region operator (← typeExpression caller left)
                (← typeExpression caller right) left right
          | .unOp operator operand =>
              let operandType ← typeExpression caller operand
              match operator with
              | .negate | .bitNegate =>
                  if operandType.integerType then
                    pure (operandType.integerPromotions (← get).target)
                  else throwAt (.invalidExpression region "integer unary operator on non-integer")
              | .not =>
                  if operandType.scalarType then pure (.signed .int)
                  else throwAt (.invalidExpression region "logical negation on non-scalar")
              | .addr =>
                  if isLValue operand || operandType.functionType then pure (.ptr operandType)
                  else throwAt (.invalidExpression region "address of non-lvalue")
          | .condExp condition thenExpr elseExpr =>
              let conditionType ← typeExpression caller condition
              if !conditionType.scalarType then
                throwAt (.invalidExpression region "conditional guard is not scalar")
              let thenType := functionDesignatorType (← typeExpression caller thenExpr)
              let elseType := functionDesignatorType (← typeExpression caller elseExpr)
              match thenType, elseType with
              | type@(.ptr _), other =>
                  if other.integerType then
                    if ← nullPointerConstant other elseExpr then pure type
                    else throwAt (.invalidExpression region "nonzero integer in pointer conditional")
                  else
                    match CType.unifyTypes (← get).target type other with
                    | .ok type => pure type
                    | .error error => throwAt (.invalidExpression region (reprStr error))
              | other, type@(.ptr _) =>
                  if other.integerType then
                    if ← nullPointerConstant other thenExpr then pure type
                    else throwAt (.invalidExpression region "nonzero integer in pointer conditional")
                  else
                    match CType.unifyTypes (← get).target other type with
                    | .ok type => pure type
                    | .error error => throwAt (.invalidExpression region (reprStr error))
              | _, _ =>
                  match CType.unifyTypes (← get).target thenType elseType with
                  | .ok type => pure type
                  | .error error => throwAt (.invalidExpression region (reprStr error))
          | .structDot value field =>
              match ← typeExpression caller value with
              | .structTy name =>
                  let state ← get
                  match state.structs.find? (·.canonicalName = name) with
                  | some info =>
                      match info.fields.find? (·.sourceName = field) with
                      | some field => pure field.type
                      | none => throwAt (.invalidExpression region s!"unknown field {field}")
                  | none => throwAt (.incompleteStruct region name)
              | _ => throwAt (.invalidExpression region "field access on non-struct")
          | .arrayDeref array index =>
              let arrayType ← typeExpression caller array
              let indexType ← typeExpression caller index
              if !integerObjectType indexType then
                throwAt (.invalidExpression region "array index is not integer")
              match arrayType with
              | .array element _ | .ptr element => pure element
              | _ => throwAt (.invalidExpression region "indexing non-array value")
          | .deref value =>
              match functionDesignatorType (← typeExpression caller value) with
              | .ptr type => pure type
              | .array type _ => pure type
              | _ => throwAt (.invalidExpression region "dereferencing non-pointer value")
          | .typeCast rawType value =>
              let fromType ← typeExpression caller value
              let toType ← resolveType rawType.region rawType.value
              if fromType.scalarType && toType.scalarType then pure toType
              else throwAt (.invalidExpression region "cast between non-scalar types")
          | .sizeof value =>
              let calls := (← get).calls
              let _ ← typeExpression caller value
              modify fun state => { state with calls }
              pure CType.ImplementationTypes.sizeT
          | .sizeofTy rawType =>
              let _ ← resolveType rawType.region rawType.value
              pure CType.ImplementationTypes.sizeT
          | .eFnCall function arguments =>
              let functionType := functionDesignatorType (← typeExpression caller function)
              let (returnType, parameters) ← match functionType with
                | .ptr (.function returnType parameters) => pure (returnType, parameters)
                | _ => throwAt (.invalidExpression region "called value is not a function")
              if arguments.length != parameters.length then
                throwAt (.invalidExpression region "function argument count mismatch")
              checkArguments caller region parameters arguments
              let state ← get
              let callee := match function with
                | .e ⟨.var name _, _⟩ =>
                    (lookupScopes name state.symbolScopes).bind fun id =>
                      (symbolById? state id).bind fun symbol =>
                        if symbol.type.functionType then some id else none
                | _ => none
              modify fun state =>
                { state with calls := state.calls ++ [{ caller, callee, region }] }
              pure returnType
          | .compLiteral rawType initializers =>
              let type ← resolveType region rawType
              let _ ← typeDesignatedInitializers caller initializers
              pure type
          | .arbitrary rawType => resolveType region rawType
          | .mkBool value =>
              if (← typeExpression caller value).scalarType then pure (.signed .int)
              else throwAt (.invalidExpression region "boolean conversion of non-scalar")
        recordExpression region type
        pure type
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def typeInitializerExpressions (caller : Option Nat) : Initializer → AnalyzeM Unit
    | .initE value => do let _ ← typeExpression caller value; pure ()
    | .initList initializers => typeDesignatedInitializers caller initializers
  termination_by initializer => sizeOf initializer
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def typeDesignator (caller : Option Nat) : Designator → AnalyzeM Unit
    | .designE index => do let _ ← typeExpression caller index; pure ()
    | .designFld _ => pure ()
  termination_by designator => sizeOf designator
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def typeDesignators (caller : Option Nat) : List Designator → AnalyzeM Unit
    | [] => pure ()
    | designator :: rest => do
        typeDesignator caller designator
        typeDesignators caller rest
  termination_by designators => sizeOf designators
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def typeDesignatedInitializers (caller : Option Nat) :
      List (List Designator × Initializer) → AnalyzeM Unit
    | [] => pure ()
    | (designators, initializer) :: rest => do
        typeDesignators caller designators
        typeInitializerExpressions caller initializer
        typeDesignatedInitializers caller rest
  termination_by initializers => sizeOf initializers
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def checkArguments (caller : Option Nat) (region : Region) :
      List AnalyzedCType → List Expr → AnalyzeM Unit
    | [], [] => pure ()
    | parameter :: parameters, argument :: arguments => do
        let argumentType := functionDesignatorType (← typeExpression caller argument)
        requireAssignment region parameter argumentType argument
        checkArguments caller region parameters arguments
    | _, _ => throwAt (.invalidExpression region "function argument count mismatch")
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def initializerTarget (caller : Option Nat) (region : Region) :
    AnalyzedCType → List Designator → AnalyzeM AnalyzedCType
  | type, [] => pure type
  | .array element size, .designE index :: rest => do
      if !integerObjectType (← typeExpression caller index) then
        throwAt (.invalidExpression region "array designator is not integer")
      let value ← constantValue index
      if value < 0 then
        throwAt (.invalidExpression region "negative array designator")
      if let some count := size then
        if count ≤ value then
          throwAt (.invalidExpression region "array designator is outside the array")
      initializerTarget caller region element rest
  | .structTy name, .designFld fieldName :: rest => do
      let state ← get
      let info ← match state.structs.find? (·.canonicalName = name) with
        | some info => pure info
        | none => throwAt (.incompleteStruct region name)
      let field ← match info.fields.find? (·.sourceName = fieldName) with
        | some field => pure field
        | none => throwAt (.invalidExpression region s!"unknown field {fieldName}")
      initializerTarget caller region field.type rest
  | _, _ :: _ => throwAt (.invalidExpression region "invalid initializer designator")

private def initializerElement (region : Region) (type : AnalyzedCType) (index : Nat) :
    AnalyzeM AnalyzedCType := do
  match type with
  | .array element size =>
      if let some count := size then
        if index ≥ Int.toNat count then
          throwAt (.invalidExpression region "too many array initializers")
      pure element
  | .structTy name =>
      let state ← get
      match state.structs.find? (·.canonicalName = name) >>= (·.fields[index]?) with
      | some field => pure field.type
      | none => throwAt (.invalidExpression region "too many struct initializers")
  | _ =>
      if index = 0 then pure type
      else throwAt (.invalidExpression region "too many scalar initializers")

mutual
  private def checkInitializer (caller : Option Nat) (expected : AnalyzedCType) :
      Initializer → AnalyzeM Unit
    | .initE expression => do
        let actual := functionDesignatorType (← typeExpression caller expression)
        requireAssignment (match expression with | .e value => value.region) expected actual expression
    | .initList initializers => checkInitializerList caller expected 0 initializers
  termination_by initializer => sizeOf initializer
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def checkInitializerList (caller : Option Nat) (expected : AnalyzedCType) :
      Nat → List (List Designator × Initializer) → AnalyzeM Unit
    | _, [] => pure ()
    | index, (designators, initializer) :: rest => do
        let region := match initializer with
          | .initE (.e value) => value.region
          | .initList _ => .bogus
        let target ← if designators.isEmpty then initializerElement region expected index
          else initializerTarget caller region expected designators
        checkInitializer caller target initializer
        let nextIndex ← match designators with
          | .designE expression :: _ => do
              let value ← constantValue expression
              pure (value.toNat + 1)
          | .designFld fieldName :: _ =>
              match expected with
              | .structTy name =>
                  let info ← match (← get).structs.find? (·.canonicalName = name) with
                    | some info => pure info
                    | none => throwAt (.incompleteStruct region name)
                  let fieldIndex ← match info.fields.findIdx? (·.sourceName = fieldName) with
                    | some fieldIndex => pure fieldIndex
                    | none => throwAt (.invalidExpression region s!"unknown field {fieldName}")
                  pure (fieldIndex + 1)
              | _ => throwAt (.invalidExpression region "field designator for non-struct")
          | _ => pure (index + 1)
        checkInitializerList caller expected nextIndex rest
  termination_by _ initializers => sizeOf initializers
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def inferredArrayLength :
    List (List Designator × Initializer) → Nat → Nat → AnalyzeM Nat
  | [], _, maximum => pure maximum
  | (designators, _) :: rest, cursor, maximum => do
      let index ← match designators with
        | .designE expression :: _ =>
            let value ← constantValue expression
            if value < 0 then
              throwAt (.invalidExpression .bogus "negative array designator")
            pure value.toNat
        | _ => pure cursor
      let next := index + 1
      inferredArrayLength rest next (max maximum next)

private def checkStaticInitializer : Initializer → AnalyzeM Unit
  | .initE expression => do
      let _ ← constantValue expression
      pure ()
  | .initList [] => pure ()
  | .initList ((_, initializer) :: rest) => do
      checkStaticInitializer initializer
      checkStaticInitializer (.initList rest)
termination_by initializer => sizeOf initializer
decreasing_by all_goals simp_wf <;> decreasing_trivial

private def supportedStaticInitializerValues : Initializer → AnalyzeM (Option (List Int))
  | .initE expression => return some [← constantValue expression]
  | .initList initializers => do
      let mut values := []
      for (designators, initializer) in initializers do
        match designators, initializer with
        | [], .initE expression => values := values ++ [← constantValue expression]
        | _, _ => return none
      return some values

private def functionLinkage (region : Region)
    (storageClasses : List StorageClass) : AnalyzeM Linkage := do
  if storageClasses.length > 1 then
    throwAt (.invalidExpression region "multiple function storage classes are unsupported")
  if storageClasses.any (fun | .auto | .register | .threadLocal => true | _ => false) then
    throwAt (.invalidExpression region "invalid function storage class")
  if storageClasses.any fun | .static => true | _ => false then pure .internal
  else pure .external

private def analyzeDeclaration (functionId : Option Nat)
    (declaration : Located Declaration) : AnalyzeM (List Nat) := do
  match declaration.value with
  | .structDecl name fields =>
      declareStruct name fields
      pure []
  | .enumDecl name enumerators =>
      declareEnum name enumerators
      pure []
  | .varDecl rawType name storageClasses initializer _ =>
      let declaredType ← resolveType name.region rawType
      if storageClasses.any (fun | .threadLocal => true | _ => false) then
        throwAt (.invalidExpression name.region "thread-local storage is unsupported")
      if storageClasses.length > 1 then
        throwAt (.invalidExpression name.region "multiple storage classes are unsupported")
      if functionId.isNone && storageClasses.any (fun | .auto | .register => true | _ => false) then
        throwAt (.invalidExpression name.region "automatic storage class at file scope")
      let hasExtern := storageClasses.any fun | .extern => true | _ => false
      let hasStatic := storageClasses.any fun | .static => true | _ => false
      let id ← match functionId with
         | none => declareGlobalSymbol name declaredType
         | some functionId =>
            if hasExtern then do
              let id ← declareGlobalSymbol name declaredType
              bindBlockExtern name id
              pure id
            else if hasStatic then declareSymbol name declaredType (.staticLocal functionId)
            else declareSymbol name declaredType (.local functionId)
      let type ← match symbolById? (← get) id with
        | some symbol => pure symbol.type
        | none => throwAt (.invalidExpression name.region "missing declared symbol")
      let type ← match type, initializer with
        | .array element none, some (.initList initializers) =>
            let count ← inferredArrayLength initializers 0 0
            if count = 0 then
              throwAt (.invalidExpression name.region "empty incomplete array initializer")
            let completed : AnalyzedCType := .array element (some (Int.ofNat count))
            updateSymbol id fun symbol => { symbol with type := completed }
            pure completed
        | type, _ => pure type
      if initializer.isSome then
        let state ← get
        if state.definedSymbols.contains id then
          throwAt (.duplicateSymbol name.region name.value)
        modify fun state => { state with definedSymbols := id :: state.definedSymbols }
      let staticValues ← if let some initializer := initializer then do
          let calls := (← get).calls.length
          checkInitializer functionId type initializer
          if (functionId.isNone || hasStatic) && (← get).calls.length != calls then
            throwAt (.invalidExpression name.region "static initializer calls a function")
          if functionId.isNone || hasStatic then
            checkStaticInitializer initializer
            supportedStaticInitializerValues initializer
          else pure none
        else pure none
      if (functionId.isNone && (!hasExtern || initializer.isSome)) ||
          (functionId.isSome && hasStatic) then
        registerStaticObject id initializer staticValues name.region
      pure <| if functionId.isSome && hasExtern then [] else [id]
  | .extFnDecl returnType name parameters storageClasses _ =>
      let linkage ← functionLinkage name.region storageClasses
      let (id, _) ← declareFunction returnType name parameters linkage
      pure [id]
  | .typeDecl _ => throwAt (.unresolvedTypedef declaration.region "<declaration>")

mutual
  private def analyzeStatement (functionId : Nat) : Statement → AnalyzeM (List Nat)
    | .stmt ⟨node, region⟩ =>
        match node with
        | .assign left right => do
            if !isLValue left then throwAt (.invalidExpression region "assignment to non-lvalue")
            let leftType ← typeExpression (some functionId) left
            let rightType := functionDesignatorType (← typeExpression (some functionId) right)
            requireAssignment region leftType rightType right
            pure []
        | .assignFnCall left function arguments => do
            let call := Expr.e { value := .eFnCall function arguments, region }
            let returnType ← typeExpression (some functionId) call
            if let some left := left then
              let leftType ← typeExpression (some functionId) left
              requireAssignment region leftType returnType call
            pure []
        | .chaos value => do
            let _ ← typeExpression (some functionId) value
            pure []
        | .embeddedFnCall left function arguments => do
            let call := Expr.e { value := .eFnCall function arguments, region }
            let returnType ← typeExpression (some functionId) call
            let leftType ← typeExpression (some functionId) left
            requireAssignment region leftType returnType call
            pure []
        | .block items => do
            pushScopes
            let locals ← analyzeBody functionId items
            popScopes
            pure locals
        | .whileStmt condition _ body => do
            if !(← typeExpression (some functionId) condition).scalarType then
              throwAt (.invalidExpression region "while condition is not scalar")
            analyzeStatement functionId body
        | .trap _ body => analyzeStatement functionId body
        | .returnStmt value => do
            let state ← get
            let returnType ← match symbolById? state functionId with
              | some ⟨_, _, .function returnType _, _, _, _⟩ => pure returnType
              | _ => throwAt (.invalidExpression region "missing current function type")
            match value with
            | none =>
                if returnType == .void then pure []
                else throwAt (.invalidExpression region "missing return value")
            | some value =>
                let actual := functionDesignatorType (← typeExpression (some functionId) value)
                requireAssignment region returnType actual value
                pure []
        | .returnFnCall function arguments => do
            let state ← get
            let returnType ← match symbolById? state functionId with
              | some ⟨_, _, .function returnType _, _, _, _⟩ => pure returnType
              | _ => throwAt (.invalidExpression region "missing current function type")
            let call := Expr.e { value := .eFnCall function arguments, region }
            let actual ← typeExpression (some functionId) call
            requireAssignment region returnType actual call
            pure []
        | .ifStmt condition thenBranch elseBranch => do
            if !(← typeExpression (some functionId) condition).scalarType then
              throwAt (.invalidExpression region "if condition is not scalar")
            return (← analyzeStatement functionId thenBranch) ++
              (← analyzeStatement functionId elseBranch)
        | .switch value cases => do
            if !(← typeExpression (some functionId) value).integerType then
              throwAt (.invalidExpression region "switch value is not integer")
            pushScopes
            let locals ← analyzeCases functionId cases
            popScopes
            pure locals
        | .spec (_, statements, _) => analyzeStatements functionId statements
        | .asmStmt _ asm => do
            for (_, _, expression) in asm.mod1 ++ asm.mod2 do
              let _ ← typeExpression (some functionId) expression
            pure []
        | .localInit value => do
            let _ ← typeExpression (some functionId) value
            pure []
        | .break | .continue | .emptyStmt | .auxUpdate _ | .ghostUpdate _ => pure []
  termination_by statement => sizeOf statement
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def analyzeBody (functionId : Nat) : List BlockItem → AnalyzeM (List Nat)
    | [] => pure []
    | .statement statement :: rest =>
        return (← analyzeStatement functionId statement) ++ (← analyzeBody functionId rest)
    | .declaration declaration :: rest =>
        return (← analyzeDeclaration (some functionId) declaration) ++
          (← analyzeBody functionId rest)
  termination_by items => sizeOf items
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def analyzeStatements (functionId : Nat) : List Statement → AnalyzeM (List Nat)
    | [] => pure []
    | statement :: rest =>
        return (← analyzeStatement functionId statement) ++
          (← analyzeStatements functionId rest)
  termination_by statements => sizeOf statements
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def analyzeCases (functionId : Nat) :
      List (List (Option Expr) × List BlockItem) → AnalyzeM (List Nat)
    | [] => pure []
    | (labels, body) :: rest => do
        analyzeLabels functionId labels
        return (← analyzeBody functionId body) ++ (← analyzeCases functionId rest)
  termination_by cases => sizeOf cases
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def analyzeLabels (functionId : Nat) : List (Option Expr) → AnalyzeM Unit
    | [] => pure ()
    | none :: rest => analyzeLabels functionId rest
    | some expression :: rest => do
        if !(← typeExpression (some functionId) expression).integerType then
          throwAt (.invalidExpression (match expression with | .e value => value.region)
            "case label is not integer")
        let _ ← constantValue expression
        analyzeLabels functionId rest
  termination_by labels => sizeOf labels
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def analyzeFunction (function : CType Expr × Located String)
    (parameters : List (CType Expr × Located String)) (storageClasses : List StorageClass)
    (specifications : List FunctionSpec)
    (body : Body) : AnalyzeM Unit := do
  let linkage ← functionLinkage function.2.region storageClasses
  let prototypeParameters := parameters.map fun (type, name) => (type, some name.value)
  let (functionId, returnType) ←
    declareFunction function.1 function.2 prototypeParameters linkage
  pushScopes
  let mut parameterIds := []
  for (rawType, name) in parameters do
    let type := (← resolveType name.region rawType).paramNorm
    let id ← declareSymbol name type (.parameter functionId)
    parameterIds := parameterIds ++ [id]
  let locals ← analyzeBody functionId body.value
  popScopes
  let state ← get
  if state.definedFunctions.contains functionId then
    throwAt (.duplicateSymbol function.2.region function.2.value)
  let info : FunctionInfo := {
    symbolId := functionId
    returnType
    parameters := parameterIds
    locals
    specifications
    body
    region := function.2.region }
  modify fun state =>
    let state := { state with functions := state.functions ++ [info] }
    { state with definedFunctions := functionId :: state.definedFunctions }

private def analyzeExternals : TranslationUnit → AnalyzeM Unit
  | [] => pure ()
  | .declaration declaration :: rest => do
      let _ ← analyzeDeclaration none declaration
      analyzeExternals rest
  | .functionDefinition function parameters storageClasses specifications body :: rest => do
      analyzeFunction function parameters storageClasses specifications body
      analyzeExternals rest

private def typeToZag (type : AnalyzedCType) : Ty :=
  match type with
  | .signed kind => .prim ("c.signed." ++ kind.name)
  | .unsigned kind => .prim ("c.unsigned." ++ kind.name)
  | .bool => .prim "c.bool"
  | .plainChar => .prim "c.char"
  | .structTy name => .prim ("c.struct." ++ name)
  | .enumTy name => .prim ("c.enum." ++ name.getD "anonymous")
  | .ptr pointee => .prim ("c.ptr." ++ CType.typeName pointee)
  | .array element size =>
      .prim ("c.array." ++ CType.typeName element ++ "." ++ toString size)
  | .bitfield signed width =>
      .prim ("c.bitfield." ++ toString signed ++ "." ++ toString width)
  | .ident name => .prim ("c.unresolved." ++ name)
  | .function returnType parameters =>
      .func (parameters.map typeToZag) (typeToZag returnType)
  | .void => .prim "c.void"

private def analyzeTypedefs (typedefs : List (String × CType Expr)) :
    AnalyzeM (List (String × AnalyzedCType) × TypeAbbrevCtx) := do
  let mut analyzed := []
  let mut raw : TypeAbbrevCtx.Raw := []
  for (name, type) in typedefs do
    let type ← resolveType .bogus type
    analyzed := analyzed ++ [(name, type)]
    raw := raw ++ [(name, { typeArity := 0, body := typeToZag type })]
  match TypeAbbrevCtx.ofRaw? raw with
  | some context => pure (analyzed, context)
  | none => throwAt .invalidTypeAbbreviations

private def completeTentativeArrays : AnalyzeM Unit := do
  let objects := (← get).staticObjects
  for object in objects do
    if object.initialization matches .zero then
      match symbolById? (← get) object.symbolId with
      | some symbol =>
          match symbol.kind, symbol.type with
          | .global, .array element none =>
              updateSymbol symbol.id fun current =>
                { current with type := .array element (some 1) }
          | _, _ => pure ()
      | none => throwAt (.invalidExpression object.region "missing static object symbol")

/-- Analyze a parsed StrictC translation unit without invoking external tools. -/
def analyze (target : Target) (translationUnit : TranslationUnit) :
    Except AnalysisError Program := do
  let rawTypedefs ← (resolvedTopLevelTypedefs translationUnit).mapError .syntax
  let transformed ← (removeTypedefs translationUnit).mapError .syntax
  let initial : State := { target }
  let (_, state) ← (analyzeExternals transformed).run initial
  let ((typedefs, typeAbbrevs), state) ← (analyzeTypedefs rawTypedefs).run state
  let (_, state) ← rejectIncompleteStructs.run state
  let (_, state) ← completeTentativeArrays.run state
  let (_, state) ← validateSymbolTypes.run state
  pure {
    target
    translationUnit := transformed
    typedefs
    typeAbbrevs
    structs := state.structs
    symbols := state.symbols
    functions := state.functions
    globals := state.globals
    expressionTypes := state.expressionTypes
    calls := state.calls
    staticObjects := state.staticObjects }

end Zag.Lang.AutoCorres.CParser.ProgramAnalysis
