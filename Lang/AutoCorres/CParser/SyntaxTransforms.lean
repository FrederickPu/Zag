import Lang.AutoCorres.CParser.Parser
import Init.WFTactics

/-!
# StrictC syntax transforms

Pure port of the `remove_typedefs` portion of `syntax_transforms.ML` from
pinned l4v commit `bc2599a59c43e673dca021b10b9841e9b8da4430`.
-/

namespace Zag.Lang.AutoCorres.CParser

/-- Failure to resolve a typedef at the source construct which used it. -/
structure Error where
  region : Region
  name : String
deriving Repr, DecidableEq, Inhabited

private abbrev TypedefEnv := List (List (String × CType Expr))

private def lookupScope (name : String) : List (String × CType Expr) → Option (CType Expr)
  | [] => none
  | (candidate, type) :: rest =>
      if candidate = name then some type else lookupScope name rest

private def lookupType (environment : TypedefEnv) (name : String) : Option (CType Expr) :=
  environment.findSome? (lookupScope name)

private def extendEnvironment (bindings : List (String × CType Expr)) : TypedefEnv → TypedefEnv
  | [] => [bindings]
  | scope :: scopes => (bindings ++ scope) :: scopes

mutual
  private def updateType (environment : TypedefEnv) (region : Region) :
      CType Expr → Except Error (CType Expr)
    | .ptr type => return .ptr (← updateType environment region type)
    | .array type size => do
        let type ← updateType environment region type
        let size ← (match size with
          | none => pure none
          | some expression => return some (← removeExpressionTypedefs environment expression) :
            Except Error (Option Expr))
        return .array type size
    | .bitfield signed width =>
        return .bitfield signed (← removeExpressionTypedefs environment width)
    | .ident name =>
        match lookupType environment name with
        | some type => pure type
        | none => throw { region, name }
    | .function returnType parameterTypes =>
        return .function (← updateType environment region returnType)
          (← parameterTypes.mapM (updateType environment region))
    | type => pure type
  termination_by type => sizeOf type
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeExpressionTypedefs (environment : TypedefEnv) :
      Expr → Except Error Expr
    | .e ⟨originalNode, region⟩ => do
        let node ← (match originalNode with
          | .binOp operator left right =>
              return ExprNode.binOp operator
                (← removeExpressionTypedefs environment left)
                (← removeExpressionTypedefs environment right)
          | .unOp operator operand =>
              return ExprNode.unOp operator (← removeExpressionTypedefs environment operand)
          | .condExp condition thenExpr elseExpr =>
              return ExprNode.condExp
                (← removeExpressionTypedefs environment condition)
                (← removeExpressionTypedefs environment thenExpr)
                (← removeExpressionTypedefs environment elseExpr)
          | .structDot value field =>
              return ExprNode.structDot (← removeExpressionTypedefs environment value) field
          | .arrayDeref array index =>
              return ExprNode.arrayDeref
                (← removeExpressionTypedefs environment array)
                (← removeExpressionTypedefs environment index)
          | .deref value =>
              return ExprNode.deref (← removeExpressionTypedefs environment value)
          | .typeCast ⟨type, typeRegion⟩ value =>
              return ExprNode.typeCast
                { value := ← updateType environment typeRegion type, region := typeRegion }
                (← removeExpressionTypedefs environment value)
          | .sizeof value =>
              return ExprNode.sizeof (← removeExpressionTypedefs environment value)
          | .sizeofTy ⟨type, typeRegion⟩ =>
              return ExprNode.sizeofTy
                { value := ← updateType environment typeRegion type, region := typeRegion }
          | .eFnCall function arguments =>
              return ExprNode.eFnCall (← removeExpressionTypedefs environment function)
                (← arguments.mapM fun argument =>
                  removeExpressionTypedefs environment argument)
          | .compLiteral type initializers =>
              return ExprNode.compLiteral (← updateType environment region type)
                (← removeDesignatedInitializers environment initializers)
          | .arbitrary type =>
              return ExprNode.arbitrary (← updateType environment region type)
          | .mkBool value =>
              return ExprNode.mkBool (← removeExpressionTypedefs environment value)
          | .constant _ | .var _ _ => pure originalNode : Except Error ExprNode)
        return .e { value := node, region }
  termination_by expression => sizeOf expression
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeInitializerTypedefs (environment : TypedefEnv) :
      Initializer → Except Error Initializer
    | .initE value => return .initE (← removeExpressionTypedefs environment value)
    | .initList initializers =>
        return .initList (← removeDesignatedInitializers environment initializers)
  termination_by initializer => sizeOf initializer
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeDesignatorTypedefs (environment : TypedefEnv) :
      Designator → Except Error Designator
    | .designE index => return .designE (← removeExpressionTypedefs environment index)
    | .designFld field => pure (.designFld field)
  termination_by designator => sizeOf designator
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeDesignators (environment : TypedefEnv) :
      List Designator → Except Error (List Designator)
    | [] => pure []
    | designator :: rest =>
        return (← removeDesignatorTypedefs environment designator) ::
          (← removeDesignators environment rest)
  termination_by designators => sizeOf designators
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeDesignatedInitializers (environment : TypedefEnv) :
      List (List Designator × Initializer) →
        Except Error (List (List Designator × Initializer))
    | [] => pure []
    | (designators, initializer) :: rest => do
        let designators ← removeDesignators environment designators
        let initializer ← removeInitializerTypedefs environment initializer
        let rest ← removeDesignatedInitializers environment rest
        return (designators, initializer) :: rest
  termination_by initializers => sizeOf initializers
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def updateFields (environment : TypedefEnv) (region : Region) :
    List (CType Expr × Located String) → Except Error (List (CType Expr × Located String))
  | [] => pure []
  | (type, name) :: rest => do
      let type ← updateType environment region type
      return (type, name) :: (← updateFields environment region rest)

private def updateParameters (environment : TypedefEnv) (region : Region) :
    List (CType Expr × Option String) → Except Error (List (CType Expr × Option String))
  | [] => pure []
  | (type, name) :: rest => do
      let type ← updateType environment region type
      return (type, name) :: (← updateParameters environment region rest)

private def updateDefinitionParameters (environment : TypedefEnv) :
    List (CType Expr × Located String) → Except Error (List (CType Expr × Located String))
  | [] => pure []
  | (type, name) :: rest => do
      let type ← updateType environment name.region type
      return (type, name) :: (← updateDefinitionParameters environment rest)

private def updateEnumerators (environment : TypedefEnv) :
    List (Located String × Option Expr) → Except Error (List (Located String × Option Expr))
  | [] => pure []
  | (name, value) :: rest => do
      let value ← value.mapM (removeExpressionTypedefs environment)
      return (name, value) :: (← updateEnumerators environment rest)

private def resolveBindings (environment : TypedefEnv) (region : Region) :
    List (CType Expr × Located String) → Except Error (List (String × CType Expr))
  | [] => pure []
  | (type, name) :: rest => do
      let type ← updateType environment region type
      return (name.value, type) :: (← resolveBindings environment region rest)

private def removeDeclarationTypedefs (environment : TypedefEnv)
    (declaration : Located Declaration) :
    Except Error (Option (Located Declaration) × TypedefEnv) := do
  let region := declaration.region
  match declaration.value with
  | .varDecl type name storageClasses initializer attributes =>
      let type ← updateType environment region type
      let initializer ← initializer.mapM fun initializer =>
        removeInitializerTypedefs environment initializer
      let value := Declaration.varDecl type name storageClasses initializer attributes
      return (some { value, region }, environment)
  | .structDecl name fields =>
      let fields ← updateFields environment region fields
      return (some { value := .structDecl name fields, region }, environment)
  | .typeDecl declarators =>
      let bindings ← resolveBindings environment region declarators
      return (none, extendEnvironment bindings environment)
  | .extFnDecl returnType name parameters storageClasses specifications =>
      let returnType ← updateType environment region returnType
      let parameters ← updateParameters environment region parameters
      let value := Declaration.extFnDecl returnType name parameters storageClasses specifications
      return (some { value, region }, environment)
  | .enumDecl name enumerators =>
      let enumerators ← updateEnumerators environment enumerators
      return (some { value := .enumDecl name enumerators, region }, environment)

mutual
  private def removeStatementTypedefs (environment : TypedefEnv) :
      Statement → Except Error Statement
    | .stmt ⟨originalNode, region⟩ => do
        let node ← (match originalNode with
          | .assign left right =>
              return StatementNode.assign
                (← removeExpressionTypedefs environment left)
                (← removeExpressionTypedefs environment right)
          | .assignFnCall left function arguments =>
              return StatementNode.assignFnCall
                (← left.mapM fun value => removeExpressionTypedefs environment value)
                (← removeExpressionTypedefs environment function)
                (← arguments.mapM fun argument =>
                  removeExpressionTypedefs environment argument)
          | .chaos value =>
              return StatementNode.chaos (← removeExpressionTypedefs environment value)
          | .embeddedFnCall left function arguments =>
              return StatementNode.embeddedFnCall
                (← removeExpressionTypedefs environment left)
                (← removeExpressionTypedefs environment function)
                (← arguments.mapM fun argument =>
                  removeExpressionTypedefs environment argument)
          | .block items => do
              let result ← removeBodyTypedefs environment items
              return StatementNode.block result.2
          | .whileStmt condition invariant body =>
              return StatementNode.whileStmt
                (← removeExpressionTypedefs environment condition) invariant
                (← removeStatementTypedefs environment body)
          | .trap kind body =>
              return StatementNode.trap kind (← removeStatementTypedefs environment body)
          | .returnStmt value =>
              return StatementNode.returnStmt
                (← value.mapM fun value => removeExpressionTypedefs environment value)
          | .returnFnCall function arguments =>
              return StatementNode.returnFnCall
                (← removeExpressionTypedefs environment function)
                (← arguments.mapM fun argument =>
                  removeExpressionTypedefs environment argument)
          | .ifStmt condition thenBranch elseBranch =>
              return StatementNode.ifStmt
                (← removeExpressionTypedefs environment condition)
                (← removeStatementTypedefs environment thenBranch)
                (← removeStatementTypedefs environment elseBranch)
          | .switch value cases => do
              let value ← removeExpressionTypedefs environment value
              let result ← removeSwitchCases environment cases
              return StatementNode.switch value result.2
          | .localInit value =>
              return StatementNode.localInit (← removeExpressionTypedefs environment value)
          | .spec (header, statements, closing) =>
              return StatementNode.spec
                (header, ← statements.mapM (removeStatementTypedefs environment), closing)
          | .asmStmt volatile asm =>
              let transform := fun (name, constraint, expression) => do
                return (name, constraint, ← removeExpressionTypedefs environment expression)
              return StatementNode.asmStmt volatile {
                asm with
                mod1 := ← asm.mod1.mapM transform
                mod2 := ← asm.mod2.mapM transform }
          | .break | .continue | .emptyStmt | .auxUpdate _ | .ghostUpdate _ =>
              pure originalNode : Except Error StatementNode)
        return .stmt { value := node, region }
  termination_by statement => sizeOf statement
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeBodyTypedefs (environment : TypedefEnv) :
      List BlockItem → Except Error (TypedefEnv × List BlockItem)
    | [] => pure (environment, [])
    | .statement statement :: rest => do
        let statement ← removeStatementTypedefs environment statement
        let (environment, rest) ← removeBodyTypedefs environment rest
        return (environment, .statement statement :: rest)
    | .declaration declaration :: rest => do
        let (declaration, environment) ← removeDeclarationTypedefs environment declaration
        let (environment, rest) ← removeBodyTypedefs environment rest
        match declaration with
        | none => pure (environment, rest)
        | some declaration => pure (environment, .declaration declaration :: rest)
  termination_by items => sizeOf items
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  private def removeSwitchCases (environment : TypedefEnv) :
      List (List (Option Expr) × List BlockItem) →
        Except Error (TypedefEnv × List (List (Option Expr) × List BlockItem))
    | [] => pure (environment, [])
    | (labels, body) :: rest => do
        let labels ← labels.mapM fun label =>
          label.mapM (removeExpressionTypedefs environment)
        let (environment, body) ← removeBodyTypedefs environment body
        let (environment, rest) ← removeSwitchCases environment rest
        return (environment, (labels, body) :: rest)
  termination_by cases => sizeOf cases
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

private def removeExternalDeclarations (environment : TypedefEnv) :
    TranslationUnit → Except Error TranslationUnit
  | [] => pure []
  | .declaration declaration :: rest => do
      let (declaration, environment) ← removeDeclarationTypedefs environment declaration
      let rest ← removeExternalDeclarations environment rest
      match declaration with
      | none => pure rest
      | some declaration => pure (.declaration declaration :: rest)
  | .functionDefinition function parameters storageClasses specifications body :: rest => do
      let returnType ← updateType environment function.2.region function.1
      let parameters ← updateDefinitionParameters environment parameters
      let transformedBody ← removeBodyTypedefs environment body.value
      let functionDefinition := ExternalDeclaration.functionDefinition
        (returnType, function.2) parameters storageClasses specifications
        { body with value := transformedBody.2 }
      return functionDefinition :: (← removeExternalDeclarations environment rest)

/-- Resolve and remove all lexical typedef declarations in a translation unit. -/
def removeTypedefs (translationUnit : TranslationUnit) : Except Error TranslationUnit :=
  removeExternalDeclarations [] translationUnit

/-- Resolve the top-level typedefs in source order for later type-environment generation. -/
def resolvedTopLevelTypedefs (translationUnit : TranslationUnit) :
    Except Error (List (String × CType Expr)) :=
  let rec loop (environment : TypedefEnv) (declarations : TranslationUnit) := do
    match declarations with
    | [] => pure []
    | .declaration ⟨.typeDecl declarators, region⟩ :: rest =>
        let bindings ← resolveBindings environment region declarators
        return bindings ++ (← loop (extendEnvironment bindings environment) rest)
    | _ :: rest => loop environment rest
  loop [] translationUnit

end Zag.Lang.AutoCorres.CParser
