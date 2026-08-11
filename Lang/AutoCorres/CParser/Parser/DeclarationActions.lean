import Lang.AutoCorres.CParser.Parser.Intermediate
import Lang.AutoCorres.CParser.Parser.TypeActions
import Lang.AutoCorres.CParser.Parser.AstActions

/-!
# StrictC declaration semantic actions

Pure declaration actions from the pinned `StrictC.grm`. Token recognition stays
in the grammar layer; this module only combines parser intermediates into AST
declarations and reports the pin's recovering diagnostics.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

private def actionError (region : Region) (message : String) : Diagnostic :=
  { severity := .error, region, message }

private def specifierRegion : List DeclSpecifier → Region
  | [] => .bogus
  | first :: rest => rest.foldl (fun region specifier =>
      region.append specifier.region) first.region

def makeStructIdDecl (declaration : Located StructIdDecl) : Located Declaration :=
  { value := .structDecl declaration.value.name declaration.value.fields
    region := declaration.region }

def makeEnumDecl (specifier : EnumSpecifier) : Located Declaration :=
  { value := .enumDecl specifier.name specifier.enumerators
    region := specifier.region }

def makeVarDecl (declarationType : CType Expr) (declarator : Declarator)
    (storageClasses : List StorageClass) (initializer : Option Initializer)
    (attributes : List GccAttribute) (region : Region) : Located Declaration :=
  { value := .varDecl declarationType declarator.name storageClasses initializer attributes
    region }

def makeTypeDecl (declarationType : CType Expr) (declarator : Declarator)
    (region : Region) : Located Declaration :=
  { value := .typeDecl [(declarationType, declarator.name)], region }

def unwrapParameters (parameters : Option (List Parameter)) :
    List (CType Expr × Option String) :=
  parameters.getD [] |>.map fun parameter =>
    (parameter.value.1, parameter.value.2.map (·.value))

def mergeDeclaratorSpecifications (attributes : List GccAttribute)
    (specifications : List FunctionSpec) : List FunctionSpec :=
  AstActions.mergeSpecs [.gccAttributes attributes] specifications

def makeExtFnDecl (returnType : CType Expr) (declarator : Declarator)
    (storageClasses : List StorageClass) (specifications : List FunctionSpec)
    (region : Region) : Located Declaration :=
  { value := .extFnDecl returnType declarator.name
      (unwrapParameters declarator.parameters)
      storageClasses
      (mergeDeclaratorSpecifications declarator.attributes specifications)
    region }

private def emptyDeclaratorFrom : List DeclSpecifier →
    AstActions.ActionResult (List (Located Declaration))
  | [] => { value := [] }
  | .storage storage :: rest =>
      let result := emptyDeclaratorFrom rest
      { value := result.value
        diagnostics := actionError storage.region
          "Storage class qualifier not accompanied by declarator" :: result.diagnostics }
  | .typeQualifier qualifier :: rest =>
      let result := emptyDeclaratorFrom rest
      { value := result.value
        diagnostics := actionError qualifier.region
          "Type-qualifier not accompanied by declarator" :: result.diagnostics }
  | .functionSpecifier specifier :: rest =>
      let result := emptyDeclaratorFrom rest
      { value := result.value
        diagnostics := actionError specifier.region
          "Function-specifier not accompanied by declarator" :: result.diagnostics }
  | .typeSpecifier (.token token) :: rest =>
      let result := emptyDeclaratorFrom rest
      { value := result.value
        diagnostics := actionError token.region
          "Type not accompanied by declarator" :: result.diagnostics }
  | .typeSpecifier (.typeId name) :: rest =>
      let result := emptyDeclaratorFrom rest
      { value := result.value
        diagnostics := actionError name.region
          s!"Type-id ({name.value}) not accompanied by declarator" :: result.diagnostics }
  | [.typeSpecifier (.struct specifier)] =>
      { value := specifier.declarations.map makeStructIdDecl }
  | .typeSpecifier (.struct specifier) :: rest =>
      { value := specifier.declarations.map makeStructIdDecl
        diagnostics := [actionError (specifierRegion rest)
          "Extraneous crap after struct declaration"] }
  | [.typeSpecifier (.enum specifier)] =>
      { value := [makeEnumDecl specifier] }
  | .typeSpecifier (.enum specifier) :: rest =>
      { value := [makeEnumDecl specifier]
        diagnostics := [actionError (specifierRegion rest)
          "Extraneous crap after enum declaration"] }

def emptyDeclarator (specifiers : DeclSpecifierList) :
    AstActions.ActionResult (List (Located Declaration)) :=
  emptyDeclaratorFrom specifiers.value

abbrev StructDeclarationResult :=
  Located (List StructField) × List (Located StructIdDecl)

def appendStructDeclarations (first second : StructDeclarationResult) :
    StructDeclarationResult :=
  ({ value := first.1.value ++ second.1.value
     region := first.1.region.append second.1.region },
   first.2 ++ second.2)

def makeStructDeclaration (specifiers : DeclSpecifierList)
    (declarators : Located (List StructDeclarator)) : Parser StructDeclarationResult := do
  let baseType ← extractType specifiers
  if let some enumSpecifier := firstEnumDeclaration specifiers.value then
    error enumSpecifier.region "Don't declare enumerations inside structs"
  let fields ← declarators.value.mapM fun structDeclarator => do
    let declarator := structDeclarator.declarator.value
    let fieldName := locatedMap cFieldName declarator.name
    let fieldType := declarator.apply baseType.value
    let fieldType ← match structDeclarator.bitWidth with
      | none => pure fieldType
      | some width => applyBitfield fieldType fieldName width
    pure (fieldType, fieldName)
  pure (
    { value := fields, region := baseType.region.append declarators.region },
    firstStructDeclarations specifiers.value)

private def declarationFor (baseType : CType Expr) (isTypedef isExtern : Bool)
    (storageClasses : List StorageClass) (functionSpecifications : List FunctionSpec)
    (functionAttributes : List GccAttribute) (initializer : Located InitDeclarator) :
    Parser (Located Declaration) := do
  let declarator := initializer.value.declarator.value
  let declarationType := declarator.apply baseType
  if isTypedef then
    if initializer.value.initializer.isSome then
      error initializer.region "Can't initialise a typedef"
    pure (makeTypeDecl declarationType declarator initializer.region)
  else
    match declarationType with
    | .function returnType _ =>
        if initializer.value.initializer.isSome then
          error initializer.region "Can't initialise a function!"
        pure (makeExtFnDecl returnType declarator storageClasses functionSpecifications
          initializer.region)
    | _ =>
        if isExtern && initializer.value.initializer.isSome then
          error initializer.region "Don't initialise externs"
        pure <| makeVarDecl declarationType declarator storageClasses
          initializer.value.initializer (functionAttributes ++ declarator.attributes)
          initializer.region

def makeDeclaration (specifiers : DeclSpecifierList)
    (initializers : List (Located InitDeclarator)) : Parser (List (Located Declaration)) := do
  let baseType ← extractType specifiers
  let isTypedef := (hasTypedef specifiers).isSome
  let isExtern := (hasExtern specifiers).isSome
  let structDeclarations := firstStructDeclarations specifiers.value
  let enumDeclarations := match firstEnumDeclaration specifiers.value with
    | none => []
    | some enumSpecifier => [makeEnumDecl enumSpecifier]
  let functionSpecifications := extractFunctionSpecifiers specifiers.value
  let storageClasses := extractStorageClasses specifiers.value
  let functionAttributes := extractFunctionAttributes functionSpecifications
  let declarations ← initializers.mapM <| declarationFor baseType.value isTypedef isExtern
    storageClasses functionSpecifications functionAttributes
  pure <| enumDeclarations ++ declarations ++ structDeclarations.map makeStructIdDecl

def checkForPrototype (declaration : Located Declaration) :
    AstActions.ActionResult (Located Declaration) :=
  match declaration.value with
  | .extFnDecl .. =>
      { value := declaration
        diagnostics := [actionError declaration.region
          "Don't put function prototypes other than at top level"] }
  | _ => { value := declaration }

private def isDidNotTranslate : FunctionSpec → Bool
  | .didNotTranslate => true
  | _ => false

def makeFunctionDefinition (specifiers : DeclSpecifierList)
    (locatedDeclarator : Located Declarator) (body : Body) : Parser ExternalDeclaration := do
  let baseType ← extractType specifiers
  if let some region := hasTypedef specifiers then
    error region "Typedef illegal in function def"
  let declarator := locatedDeclarator.value
  let parameters ← match declarator.parameters with
    | none =>
        error locatedDeclarator.region "Function def with no params!"
        pure []
    | some parameters => checkParameterNames declarator.name.value parameters
  let returnType ← match declarator.apply baseType.value with
    | .function returnType _ => pure returnType
    | _ =>
        error (locatedDeclarator.region.append body.region)
          "Attempted fn def with bad declarator"
        pure baseType.value
  let specifications := mergeDeclaratorSpecifications declarator.attributes
    (extractFunctionSpecifiers specifiers.value)
  let storageClasses := extractStorageClasses specifiers.value
  if specifications.any isDidNotTranslate then
    pure <| .declaration {
      value := .extFnDecl returnType declarator.name
        (unwrapParameters declarator.parameters) storageClasses specifications
      region := specifiers.region.append locatedDeclarator.region }
  else
    pure <| .functionDefinition (returnType, declarator.name) parameters storageClasses
      specifications body

end Zag.Lang.AutoCorres.CParser.Parser
