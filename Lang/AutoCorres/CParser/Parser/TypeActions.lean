import Lang.AutoCorres.CParser.Parser.Intermediate

/-!
# StrictC type semantic actions

This is the declaration/type portion of the pinned `StrictC.grm` preamble.
Errors are accumulated in parser state and use the pin's recovery values.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

private def locatedTypeSpecifier (specifier : TypeSpecifier) : Located TypeSpecifier :=
  { value := specifier, region := specifier.region }

structure SortedTypeSpecifiers where
  bases : List (Located TypeSpecifier) := []
  signedness : List (Located TypeSpecToken) := []
deriving Repr, Inhabited

def sortTypeSpecifiers (specifiers : List DeclSpecifier) : SortedTypeSpecifiers :=
  specifiers.foldl (fun sorted specifier =>
    match specifier with
    | .typeSpecifier (.token token) =>
        match token.value with
        | .unsigned | .signed => { sorted with signedness := token :: sorted.signedness }
        | _ => { sorted with bases := locatedTypeSpecifier (.token token) :: sorted.bases }
    | .typeSpecifier typeSpecifier =>
        { sorted with bases := locatedTypeSpecifier typeSpecifier :: sorted.bases }
    | _ => sorted) {}

private def isToken (expected : TypeSpecToken) (specifier : Located TypeSpecifier) : Bool :=
  match specifier.value with
  | .token token => token.value == expected
  | _ => false

private def isIntegerModifier (specifier : Located TypeSpecifier) : Bool :=
  isToken .short specifier || isToken .long specifier

private def integralRemainder (hadInt : Bool) :
    List (Located TypeSpecifier) → Parser (Option (Located TypeSpecifier))
  | [] => pure none
  | [specifier] => do
      if hadInt && !isIntegerModifier specifier then
        error specifier.region "Bad combination with 'int'"
      pure (some specifier)
  | [first, second] => do
      if isToken .long first && isToken .long second then
        let region := second.region.append first.region
        let token : Located TypeSpecToken := { value := .longLong, region }
        pure (some { value := .token token, region })
      else
        error (second.region.append first.region) "Two type-specifiers"
        pure (some first)
  | first :: _ => do
      error first.region "Too many type-specifiers"
      pure (some first)

private def chooseBase (bases : List (Located TypeSpecifier)) :
    Parser (Option (Located TypeSpecifier)) := do
  match bases with
  | [] => pure none
  | [base] => pure (some base)
  | _ =>
      let (ints, rest) := bases.partition (isToken .int)
      match ints with
      | [] => integralRemainder false bases
      | [_] => integralRemainder true rest
      | first :: _ =>
          error first.region "Too many 'int' specifiers"
          pure (some first)

private def chooseSignedness (modifiers : List (Located TypeSpecToken)) :
    Parser (Option (Located TypeSpecToken)) := do
  match modifiers with
  | [] => pure none
  | [modifier] => pure (some modifier)
  | first :: _ =>
      error first.region "Multiple type-specifiers"
      pure (some first)

private def integerKind (token : TypeSpecToken) : IntKind :=
  match token with
  | .char => .char
  | .short => .short
  | .long => .long
  | .longLong => .longLong
  | _ => .int

private def typeFromBase (base : Located TypeSpecifier) : CType Expr :=
  match base.value with
  | .token token =>
      match token.value with
      | .void => .void
      | .char => .plainChar
      | .bool => .bool
      | value => .signed (integerKind value)
  | .struct specifier => specifier.type.value
  | .enum specifier => .enumTy specifier.name.value
  | .typeId name => .ident name.value

private def signedType (base : Located TypeSpecifier) (modifier : Located TypeSpecToken) :
    Parser (CType Expr) := do
  match base.value with
  | .token token =>
      match token.value with
      | .void =>
          error modifier.region "Signedness modifier on void"
          pure .void
      | .bool =>
          error modifier.region "Signedness modifier on _Bool"
          pure .bool
      | value =>
          pure <| if modifier.value == .unsigned then
            .unsigned (integerKind value)
          else
            .signed (integerKind value)
  | .typeId name =>
      error modifier.region "Signedness modifier on typedef id"
      pure (.ident name.value)
  | .struct specifier =>
      error modifier.region "Signedness modifier on struct"
      pure specifier.type.value
  | .enum specifier =>
      error modifier.region "Signedness modifier on enum"
      pure (.enumTy specifier.name.value)

def extractType (specifiers : DeclSpecifierList) : Parser (Located (CType Expr)) := do
  let sorted := sortTypeSpecifiers specifiers.value
  let base ← chooseBase sorted.bases
  let signedness ← chooseSignedness sorted.signedness
  match base, signedness with
  | none, none =>
      error specifiers.region "No base type in declaration"
      pure { value := .signed .int, region := Region.bogus }
  | some base, none => pure { value := typeFromBase base, region := base.region }
  | none, some modifier =>
      let type : CType Expr :=
        if modifier.value == .unsigned then .unsigned .int else .signed .int
      pure { value := type, region := modifier.region }
  | some base, some modifier =>
      let type ← signedType base modifier
      let region := match base.value with
        | .token token => match token.value with
          | .void | .bool => base.region
          | _ => modifier.region.append base.region
        | _ => base.region
      pure { value := type, region }

def hasTypedef (specifiers : DeclSpecifierList) : Option Region :=
  specifiers.value.findSome? fun
    | .storage storage => if storage.value == .typeDef then some storage.region else none
    | _ => none

def hasExtern (specifiers : DeclSpecifierList) : Option Region :=
  specifiers.value.findSome? fun
    | .storage storage => if storage.value == .extern then some storage.region else none
    | _ => none

def extractStorageClasses (specifiers : List DeclSpecifier) : List StorageClass :=
  specifiers.filterMap fun
    | .storage storage => storageClass? storage.value
    | _ => none

def extractFunctionSpecifiers (specifiers : List DeclSpecifier) : List FunctionSpec :=
  specifiers.filterMap fun
    | .functionSpecifier functionSpecifier => some functionSpecifier.value
    | _ => none

def extractFunctionAttributes : List FunctionSpec → List GccAttribute
  | [] => []
  | .gccAttributes attributes :: rest => attributes ++ extractFunctionAttributes rest
  | _ :: rest => extractFunctionAttributes rest

def firstStructDeclarations : List DeclSpecifier → List (Located StructIdDecl)
  | [] => []
  | .typeSpecifier (.struct specifier) :: _ => specifier.declarations
  | _ :: rest => firstStructDeclarations rest

def firstEnumDeclaration : List DeclSpecifier → Option EnumSpecifier
  | [] => none
  | .typeSpecifier (.enum specifier) :: rest =>
      if specifier.enumerators.isEmpty then firstEnumDeclaration rest else some specifier
  | _ :: rest => firstEnumDeclaration rest

def checkParameterSpecifiers (specifiers : DeclSpecifierList) : Parser Unit := do
  if let some region := hasTypedef specifiers then
    error region "Typedefs forbidden in parameters"
  if let some region := hasExtern specifiers then
    error region "Extern forbidden in parameters"
  match firstStructDeclarations specifiers.value with
  | declaration :: _ =>
      error declaration.value.name.region "Don't declare structs in parameters"
  | [] => pure ()
  if let some enumSpecifier := firstEnumDeclaration specifiers.value then
    error enumSpecifier.region "Don't declare enumerations in parameters"

def checkParameters (parameters : Located (List Parameter)) : Parser (List Parameter) := do
  match parameters.value with
  | [] =>
      warning parameters.region "Avoid empty parameter lists in C; prefer \"(void)\""
      pure []
  | [parameter] =>
      match parameter.value with
      | (.void, none) => pure []
      | _ => pure [parameter]
  | parameters => pure parameters

def makeParameter (specifiers : DeclSpecifierList)
    (declarator : Option Declarator := none) : Parser Parameter := do
  let base ← extractType specifiers
  checkParameterSpecifiers specifiers
  match declarator with
  | none => pure { value := (base.value, none), region := specifiers.region }
  | some declarator =>
      pure {
        value := (declarator.apply base.value, some declarator.name)
        region := specifiers.region.append declarator.region }

def makeAbstractParameter (specifiers : DeclSpecifierList)
    (declarator : AbstractDeclarator) : Parser Parameter := do
  let base ← extractType specifiers
  checkParameterSpecifiers specifiers
  pure {
    value := (declarator.apply base.value, none)
    region := specifiers.region.append declarator.region }

def checkParameterNames (functionName : String) (parameters : List Parameter) :
    Parser (List (CType Expr × Located String)) :=
  let rec loop (index : Nat) : List Parameter → Parser (List (CType Expr × Located String))
    | [] => pure []
    | parameter :: rest => do
        match parameter.value with
        | (type, some name) =>
            let tail ← loop (index + 1) rest
            pure ((type, name) :: tail)
        | (type, none) =>
            error parameter.region
              s!"Parameter #{index} of function {functionName} has no name"
            let tail ← loop (index + 1) rest
            pure ((type, { value := "__fake", region := Region.bogus }) :: tail)
  loop 1 parameters

def registerDeclaratorName (isTypedef : Bool) (declarator : Declarator) : Parser Unit :=
  if isTypedef then declareTypedef declarator.name.value else declareOrdinary declarator.name.value

def registerDeclaratorNames (isTypedef : Bool) (declarators : List Declarator) : Parser Unit :=
  declarators.forM (registerDeclaratorName isTypedef)

def freshAnonymousStructName : Parser String := do
  let state ← get
  let name := anonymousStructName state.nextAnonymousStruct
  set { state with nextAnonymousStruct := state.nextAnonymousStruct + 1 }
  pure name

def makeStructReference (keywordRegion : Region) (name : Located String) : TypeSpecifier :=
  let munged := cStructName name.value
  .struct {
    type := { value := .structTy munged, region := keywordRegion.append name.region }
    declarations := [] }

def makeNamedStruct (keywordRegion closingRegion : Region) (name : Located String)
    (fields : List StructField) (nested : List (Located StructIdDecl) := []) : TypeSpecifier :=
  let mungedName : Located String := { value := cStructName name.value, region := name.region }
  let declaration : Located StructIdDecl := {
    value := { name := mungedName, fields }
    region := keywordRegion.append closingRegion }
  .struct {
    type := { value := .structTy mungedName.value, region := keywordRegion.append name.region }
    declarations := declaration :: nested }

def makeAnonymousStruct (keywordRegion openingRegion closingRegion : Region)
    (fields : List StructField) (nested : List (Located StructIdDecl) := []) :
    Parser TypeSpecifier := do
  let name ← freshAnonymousStructName
  let nameRegion : Region := { left := keywordRegion.right, right := openingRegion.left }
  let locatedName : Located String := { value := name, region := nameRegion }
  let declaration : Located StructIdDecl := {
    value := { name := locatedName, fields }
    region := keywordRegion.append closingRegion }
  pure <| .struct {
    type := { value := .structTy name, region := keywordRegion.append openingRegion }
    declarations := declaration :: nested }

def integerExpression (value : Int) : Expr :=
  .e {
    value := .constant {
      value := .numConst { value, suffix := "", base := .decimal }
      region := Region.bogus }
    region := Region.bogus }

def applyBitfield (type : CType Expr) (name : Located String) (width : Expr) :
    Parser (CType Expr) := do
  match type with
  | .signed .int => pure (.bitfield true width)
  | .unsigned .int => pure (.bitfield false width)
  | _ =>
      let widthRegion := match width with | .e value => value.region
      error { left := name.region.left, right := widthRegion.right } "Bad base-type for bitfield"
      pure (.bitfield true (integerExpression 1))

end Zag.Lang.AutoCorres.CParser.Parser
