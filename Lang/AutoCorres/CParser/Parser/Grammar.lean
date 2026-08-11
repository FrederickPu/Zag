import Lang.AutoCorres.CParser.Parser.Declarator

/-!
# StrictC translation-unit grammar

This module completes the pinned grammar above the mutually recursive
expression/declarator layer. Loop syntax is lowered with the same trap/block
rewrites as the grammar actions.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

abbrev TranslationUnit := List ExternalDeclaration

private def statementRegion (statement : Statement) : Region := AstActions.sregion statement

private def wrapStatement (node : StatementNode) (region : Region) : Statement :=
  AstActions.wrapStatement node region

private def expressionRegion (expression : Expr) : Region := AstActions.eregion expression

private def wrapExpression (node : ExprNode) (region : Region) : Expr :=
  AstActions.wrapExpr node region

mutual
  private partial def initializerCallFree : Initializer → Bool
    | .initE expression => expressionCallFree expression
    | .initList initializers => initializers.all fun (designators, initializer) =>
        designators.all designatorCallFree && initializerCallFree initializer

  private partial def designatorCallFree : Designator → Bool
    | .designE expression => expressionCallFree expression
    | .designFld _ => true

  private partial def expressionCallFree : Expr → Bool
    | .e expression =>
        match expression.value with
        | .binOp _ left right => expressionCallFree left && expressionCallFree right
        | .unOp _ operand => expressionCallFree operand
        | .condExp condition thenExpression elseExpression =>
            expressionCallFree condition && expressionCallFree thenExpression &&
              expressionCallFree elseExpression
        | .structDot value _ => expressionCallFree value
        | .arrayDeref array index => expressionCallFree array && expressionCallFree index
        | .deref value => expressionCallFree value
        | .typeCast _ value => expressionCallFree value
        | .eFnCall _ _ => false
        | .compLiteral _ initializers => initializers.all fun (designators, initializer) =>
            designators.all designatorCallFree && initializerCallFree initializer
        | _ => true
end

private def isNumericConstant : Expr → Bool
  | .e ⟨.constant ⟨.numConst _, _⟩, _⟩ => true
  | _ => false

private def emitActionDiagnostics (diagnostics : List Diagnostic) : Parser Unit :=
  diagnostics.forM fun diagnostic =>
    diagnose diagnostic.severity diagnostic.region diagnostic.message

private def currentIs (kind : TokenKind) : Parser Bool := do
  let current ← peek?
  pure (current.any fun token => token.value == kind)

private def annotationString : Parser (Located String) := do
  let current ← anyToken
  match current.value with
  | .stringLiteral value => pure { value, region := current.region }
  | _ => failAt current.region "expected annotation string"

private partial def cStringLiteral : Parser (Located String) := do
  let first ← annotationString
  let rec loop (value : String) (region : Region) : Parser (Located String) := do
    let current ← peek?
    match current with
    | some { value := .stringLiteral next, region := nextRegion } =>
        let _ ← anyToken
        loop (value ++ next) (region.append nextRegion)
    | _ => pure { value, region }
  loop first.value first.region

private def isSpecialFunctionStart : TokenKind → Bool
  | .fnSpec | .relSpec | .modifies | .dontTranslate => true
  | _ => false

private def isDeclarationToken : TokenKind → Bool
  | .typedef | .extern | .static | .auto | .register | .threadLocal
  | .const | .volatile | .restrict | .int | .bool | .char | .long | .short
  | .signed | .unsigned | .void | .struct | .enum | .typeIdent _
  | .inline | .noReturn | .gccAttribute | .ownedBy
  | .fnSpec | .relSpec | .modifies | .dontTranslate => true
  | _ => false

private def atDeclarationStart : Parser Bool := do
  let current ← peek?
  match current with
  | none => pure false
  | some current =>
      pure (isDeclarationToken current.value)

private def joinSpecifierLists (left right : DeclSpecifierList) : DeclSpecifierList :=
  { value := left.value ++ right.value, region := left.region.append right.region }

private partial def parseIdListUntilSpecialEnd : Parser (List String) := do
  let rec loop (names : List String) : Parser (List String) := do
    let current ← peek?
    match current with
    | some { value := .specBlockEnd, .. } => pure names
    | some { value := .fnSpec, .. } | some { value := .relSpec, .. }
    | some { value := .modifies, .. } | some { value := .dontTranslate, .. } => pure names
    | some { value := .lbracket, .. } =>
        let _ ← token .lbracket
        let _ ← token .star
        let _ ← token .rbracket
        loop (names ++ [phantomStateName])
    | some { value := .ident _, .. } | some { value := .typeIdent _, .. } =>
        let name ← rawIdentifier
        loop (names ++ [name.value])
    | some current => failAt current.region "expected identifier in annotation"
    | none => fail "unterminated function annotation"
  loop []

private partial def parseFnSpecText : Parser (Located String) := do
  let firstName ← rawIdentifier
  let _ ← token .colon
  let firstText ← annotationString
  let first := firstName.value ++ ": \"" ++ firstText.value ++ "\""
  let rec loop (text : String) (region : Region) : Parser (Located String) := do
    let current ← peek?
    match current with
    | some { value := .ident _, .. } | some { value := .typeIdent _, .. } =>
        let name ← rawIdentifier
        let _ ← token .colon
        let value ← annotationString
        loop (text ++ "\n" ++ name.value ++ ": \"" ++ value.value ++ "\"")
          (region.append value.region)
    | _ => pure { value := text, region }
  loop first (firstName.region.append firstText.region)

private partial def parseSpecialFunctionBlock : Parser (List DeclSpecifier) := do
  let rec loop (specifiers : List DeclSpecifier) : Parser (List DeclSpecifier) := do
    let current ← peek?
    match current with
    | some { value := .specBlockEnd, .. } =>
        let _ ← token .specBlockEnd
        pure specifiers
    | some { value := .modifies, .. } =>
        let keyword ← anyToken
        let names ← parseIdListUntilSpecialEnd
        let region := match names with
          | [] => keyword.region
          | _ => keyword.region
        let value : Located FunctionSpec := { value := .modifies names, region }
        loop (specifiers ++ [.functionSpecifier value])
    | some { value := .fnSpec, .. } =>
        let keyword ← anyToken
        let text ← parseFnSpecText
        let value : Located FunctionSpec := {
          value := .fnSpec text, region := keyword.region.append text.region }
        loop (specifiers ++ [.functionSpecifier value])
    | some { value := .relSpec, .. } =>
        let keyword ← anyToken
        let text ← annotationString
        let quoted : Located String := { text with value := "\"" ++ text.value ++ "\"" }
        let value : Located FunctionSpec := {
          value := .relSpec quoted, region := keyword.region.append text.region }
        loop (specifiers ++ [.functionSpecifier value])
    | some { value := .dontTranslate, .. } =>
        let keyword ← anyToken
        let value : Located FunctionSpec := {
          value := .didNotTranslate, region := keyword.region }
        loop (specifiers ++ [.functionSpecifier value])
    | some current => failAt current.region "expected function annotation or annotation terminator"
    | none => fail "unterminated function annotation"
  loop []

partial def parseFullDeclarationSpecifiers : Parser DeclSpecifierList := do
  let start ← get
  let rec loop (result : Option DeclSpecifierList) : Parser (Option DeclSpecifierList) := do
    let current ← peek?
    match current with
    | some current =>
        if isSpecialFunctionStart current.value then
          let left := current.region
          let values ← parseSpecialFunctionBlock
          let state ← get
          let right := state.tokens[state.index - 1]?.map (·.region) |>.getD left
          let chunk : DeclSpecifierList := { value := values, region := left.append right }
          loop (some (result.map (joinSpecifierLists · chunk) |>.getD chunk))
        else if isDeclarationToken current.value then
          let chunk ← parseDeclarationSpecifiers
          loop (some (result.map (joinSpecifierLists · chunk) |>.getD chunk))
        else
          pure result
    | none => pure result
  match ← loop none with
  | some result => pure result
  | none => failAt start.currentRegion "expected declaration specifiers"

private def hasDidNotTranslate (specifications : List FunctionSpec) : Bool :=
  specifications.any fun
  | .didNotTranslate => true
  | _ => false

private def parameterValues (parameters : Option (List Parameter)) :
    List (CType Expr × Option String) :=
  parameters.getD [] |>.map fun parameter =>
    (parameter.value.1, parameter.value.2.map (·.value))

private def structDeclarations (allowForward : Bool) :
    List DeclSpecifier → List (Located Declaration)
  | [] => []
  | .typeSpecifier (.struct specifier) :: _ =>
      if specifier.declarations.isEmpty then
        if allowForward then
          match specifier.type.value with
          | .structTy name => [{
              value := .structDecl { value := name, region := specifier.type.region } []
              region := specifier.type.region }]
          | _ => []
        else []
      else
        specifier.declarations.map fun declaration => {
          value := .structDecl declaration.value.name declaration.value.fields
          region := declaration.region }
  | _ :: rest => structDeclarations allowForward rest

private def enumDeclarations (specifiers : List DeclSpecifier) : List (Located Declaration) :=
  match firstEnumDeclaration specifiers with
  | none => []
  | some enumeration => [{
      value := .enumDecl enumeration.name enumeration.enumerators
      region := enumeration.region }]

private def lowerDeclarator (specifiers : DeclSpecifierList) (base : CType Expr)
    (declarator : InitDeclarator) (isLocal : Bool) : Parser (Located Declaration) := do
  let parsed := declarator.declarator.value
  let finalType := parsed.apply base
  let isTypedef := (hasTypedef specifiers).isSome
  let isExtern := (hasExtern specifiers).isSome
  let functionSpecs := extractFunctionSpecifiers specifiers.value
  let functionAttributes := extractFunctionAttributes functionSpecs
  let storageClasses := extractStorageClasses specifiers.value
  let attributes := functionAttributes ++ parsed.attributes
  if isTypedef then
    if declarator.initializer.isSome then
      error declarator.declarator.region "Can't initialise a typedef"
    pure {
      value := .typeDecl [(finalType, parsed.name)]
      region := declarator.declarator.region }
  else
    match finalType with
    | .function returnType _ =>
        if declarator.initializer.isSome then
          error declarator.declarator.region "Can't initialise a function!"
        if isLocal then
          error declarator.declarator.region
            "Don't put function prototypes other than at top level"
        let specifications := AstActions.mergeSpecs [.gccAttributes parsed.attributes] functionSpecs
        pure {
          value := .extFnDecl returnType parsed.name (parameterValues parsed.parameters)
            storageClasses specifications
          region := declarator.declarator.region }
    | _ =>
        if isLocal && isExtern && declarator.initializer.isSome then
          error declarator.declarator.region "Don't initialise externs"
        pure {
          value := .varDecl finalType parsed.name storageClasses declarator.initializer attributes
          region := declarator.declarator.region }

private def lowerDeclaration (specifiers : DeclSpecifierList)
    (declarators : List InitDeclarator) (isLocal : Bool) : Parser (List (Located Declaration)) := do
  let base ← extractType specifiers
  let lowered ← declarators.mapM fun declarator =>
    lowerDeclarator specifiers base.value declarator isLocal
  pure (enumDeclarations specifiers.value ++ structDeclarations false specifiers.value ++ lowered)

private def lowerEmptyDeclaration (specifiers : DeclSpecifierList) :
    Parser (List (Located Declaration)) := do
  let structs := structDeclarations true specifiers.value
  let enums := enumDeclarations specifiers.value
  for specifier in specifiers.value do
    match specifier with
    | .typeSpecifier (.struct _) =>
        if structs.isEmpty then error specifier.region "Type not accompanied by declarator"
    | .typeSpecifier (.enum _) =>
        if enums.isEmpty then error specifier.region "Type not accompanied by declarator"
    | .storage value => error value.region "Storage class qualifier not accompanied by declarator"
    | .typeQualifier value => error value.region "Type-qualifier not accompanied by declarator"
    | .functionSpecifier value => error value.region "Function-specifier not accompanied by declarator"
    | .typeSpecifier (.typeId name) =>
        error name.region s!"Type-id ({name.value}) not accompanied by declarator"
    | .typeSpecifier type => error type.region "Type not accompanied by declarator"
  pure (enums ++ structs)

private def parseInitializerAfterDeclarator (specifiers : DeclSpecifierList)
    (declarator : Declarator) : Parser InitDeclarator := do
  registerDeclaratorName (hasTypedef specifiers).isSome declarator
  let initializer ← if ← currentIs .assign then
    let _ ← token .assign
    some <$> parseInitializer
  else pure none
  pure {
    declarator := { value := declarator, region := declarator.region }
    initializer }

private partial def parseRemainingInitDeclarators (specifiers : DeclSpecifierList)
    (first : InitDeclarator) : Parser (List InitDeclarator) := do
  let rec loop (values : List InitDeclarator) : Parser (List InitDeclarator) := do
    if ← currentIs .comma then
      let _ ← token .comma
      let declarator ← parseDeclarator
      let initialized ← parseInitializerAfterDeclarator specifiers declarator
      loop (values ++ [initialized])
    else pure values
  loop [first]

private partial def synchronize (state : State) (stopAtRightCurly : Bool) : State :=
  let rec loop (index : Nat) : Nat :=
    match state.tokens[index]? with
    | none => index
    | some token =>
        match token.value with
        | .eof => index
        | .semicolon => index + 1
        | .rcurly => if stopAtRightCurly then index else index + 1
        | _ => loop (index + 1)
  { state with index := loop state.index }

private def recover (parser : Parser α) (stopAtRightCurly : Bool) : Parser (Option α) :=
  fun initial =>
    let saved := initial.checkpoint
    match parser initial with
    | .success value state => .success (some value) state
    | .failure failure failed =>
        let restored := failed.restore saved
        let start := max (initial.index + 1) failed.index
        let restored := { restored with index := min start restored.tokens.size }
        let restored := restored.addDiagnostic .error failure.region failure.message
        .success none (synchronize restored stopAtRightCurly)

private def parseInvariant : Parser (Option (Located String)) := do
  if ← currentIs .invariant then
    let _ ← token .invariant
    let invariant ← annotationString
    let _ ← token .specBlockEnd
    pure (some invariant)
  else pure none

private def splitSpecification (text : String) : String × String :=
  let characters := text.toList
  let before := characters.takeWhile (· != '.')
  let after := characters.drop (before.length + 1)
  (String.ofList before, String.ofList after)

private partial def parseIncrementTarget : Parser Expr := do
  let base ← orElse (attempt do
    let star ← token .star
    let operand ← parseIncrementTarget
    pure (wrapExpression (.deref operand)
      { left := star.region.left, right := (expressionRegion operand).right }))
    (orElse (do
      let name ← identifier
      pure (wrapExpression (.var name.value none) name.region)) (attempt do
      let left ← token .lparen
      let expression ← parseExpression
      let right ← token .rparen
      pure (wrapExpression (AstActions.enode expression)
        { left := left.region.left, right := right.region.right })))
  let rec loop (expression : Expr) : Parser Expr := do
    let current ← peek?
    match current with
    | some { value := .lbracket, .. } =>
        let _ ← token .lbracket
        let index ← parseExpression
        let right ← token .rbracket
        loop (wrapExpression (.arrayDeref expression index)
          { left := (expressionRegion expression).left, right := right.region.right })
    | some { value := .dot, .. } =>
        let _ ← token .dot
        let field ← rawIdentifier
        loop (wrapExpression (.structDot expression (cFieldName field.value))
          { left := (expressionRegion expression).left, right := field.region.right })
    | some { value := .arrow, .. } =>
        let _ ← token .arrow
        let field ← rawIdentifier
        let dereference := wrapExpression (.deref expression) (expressionRegion expression)
        loop (wrapExpression (.structDot dereference (cFieldName field.value))
          { left := (expressionRegion expression).left, right := field.region.right })
    | _ => pure expression
  loop base

private def parseIncrementStatementCore : Parser Statement :=
  do
    let target ← parseIncrementTarget
    if !isLValue target then failAt (expressionRegion target) "expression is not an lvalue"
    let operator ← satisfy "increment or decrement" fun
      | .plusPlus | .minusMinus => true
      | _ => false
    let node := if operator.value == .plusPlus then
      AstActions.postIncrement target else AstActions.postDecrement target
    pure (wrapStatement node {
      left := (expressionRegion target).left, right := operator.region.right })

private def parseAssignmentStatementCore : Parser Statement := do
  let left ← parseLExpression
  let operator ← parseAssignmentOperator
  let right ← parseExpression
  let result := AstActions.assignment left operator right
  emitActionDiagnostics result.diagnostics
  pure (wrapStatement result.value ((expressionRegion left).append (expressionRegion right)))

private def blockOfStatements (statements : List Statement) : Statement :=
  match statements with
  | [] => AstActions.sbogwrap .emptyStmt
  | [statement] => statement
  | first :: rest =>
      let last := rest.getLast?.getD first
      wrapStatement (.block (statements.map BlockItem.statement))
        ((statementRegion first).append (statementRegion last))

private def parseForClauseStatement : Parser Statement :=
  orElse (attempt parseAssignmentStatementCore) parseIncrementStatementCore

private def parseInlineUpdate (ghost : Bool) : Parser Statement := do
  let keyword ← anyToken
  let text ← annotationString
  let _ ← token .specBlockEnd
  let node := if ghost then StatementNode.ghostUpdate text.value else .auxUpdate text.value
  pure (wrapStatement node (keyword.region.append text.region))

private partial def parseForClauseStatements (terminator : TokenKind) : Parser Statement := do
  if ← currentIs terminator then pure (AstActions.sbogwrap .emptyStmt)
  else
    let first ← parseForClauseStatement
    let firstValues ← if ← currentIs .auxUpd then
      pure [first, ← parseInlineUpdate false]
    else pure [first]
    let rec loop (values : List Statement) : Parser (List Statement) := do
      if ← currentIs .comma then
        let _ ← token .comma
        let statement ← parseForClauseStatement
        let values := values ++ [statement]
        let values ← if ← currentIs .auxUpd then
          pure (values ++ [← parseInlineUpdate false])
        else pure values
        loop values
      else pure values
    pure (blockOfStatements (← loop firstValues))

private def parseAsmNamedExpression : Parser NamedStringExpr := do
  let name ← if ← currentIs .lbracket then
    let _ ← token .lbracket
    let name ← rawIdentifier
    let _ ← token .rbracket
    pure (some name.value)
  else pure none
  let constraint ← cStringLiteral
  let _ ← token .lparen
  let expression ← parseExpression
  let _ ← token .rparen
  pure (name, constraint.value, expression)

private def parseAsmNamedList : Parser (List NamedStringExpr) := do
  if (← currentIs .colon) || (← currentIs .rparen) then pure []
  else sepBy1 parseAsmNamedExpression (token .comma)

private def parseAsmStringList : Parser (List String) := do
  if ← currentIs .rparen then pure []
  else
    let strings ← sepBy1 cStringLiteral (token .comma)
    pure (strings.map (·.value))

private def parseAsmBlock : Parser AsmBlock := do
  let head ← cStringLiteral
  let mod1 ← if ← currentIs .colon then
    let _ ← token .colon
    parseAsmNamedList
  else pure []
  let mod2 ← if ← currentIs .colon then
    let _ ← token .colon
    parseAsmNamedList
  else pure []
  let mod3 ← if ← currentIs .colon then
    let _ ← token .colon
    parseAsmStringList
  else pure []
  pure { head := head.value, mod1, mod2, mod3 }

mutual
  partial def parseDeclaration (isLocal : Bool := false) : Parser (List (Located Declaration)) := do
    let specifiers ← parseFullDeclarationSpecifiers
    if ← currentIs .semicolon then
      let _ ← token .semicolon
      lowerEmptyDeclaration specifiers
    else
      let declarator ← parseDeclarator
      let first ← parseInitializerAfterDeclarator specifiers declarator
      let declarators ← parseRemainingInitDeclarators specifiers first
      let _ ← token .semicolon
      lowerDeclaration specifiers declarators isLocal

  partial def parseCompoundStatement : Parser Body := do
    let left ← token .lcurly
    let items ← inScope (parseBlockItems .rcurly)
    let right ← token .rcurly
    pure { value := items, region := { left := left.region.left, right := right.region.right } }

  partial def parseFunctionBody (parameters : List (CType Expr × Located String)) : Parser Body := do
    let left ← token .lcurly
    let items ← inScope do
      for parameter in parameters do declareOrdinary parameter.2.value
      parseBlockItems .rcurly
    let right ← token .rcurly
    pure { value := items, region := { left := left.region.left, right := right.region.right } }

  partial def parseBlockItems (terminator : TokenKind) : Parser (List BlockItem) := do
    let rec loop (items : List BlockItem) : Parser (List BlockItem) := do
      if (← currentIs terminator) || (← currentIs .eof) ||
          (terminator == .rcurly && ((← currentIs .case) || (← currentIs .default))) then
        pure items
      else
        let parsed ← recover parseBlockItem true
        match parsed with
        | some next => loop (items ++ next)
        | none => loop items
    loop []

  partial def parseBlockItem : Parser (List BlockItem) := do
    if ← atDeclarationStart then
      let declarations ← parseDeclaration true
      pure (declarations.map BlockItem.declaration)
    else
      pure [.statement (← parseStatement)]

  partial def parseStatement : Parser Statement := do
    let current ← peek?
    match current with
    | some current =>
        match current.value with
        | .lcurly =>
            let body ← parseCompoundStatement
            pure (wrapStatement (.block body.value) body.region)
        | .if => parseIfStatement
        | .while => parseWhileStatement
        | .do => parseDoWhileStatement
        | .for => parseForStatement
        | .switch => parseSwitchStatement
        | .return => parseReturnStatement
        | .break =>
            let left ← anyToken
            let right ← token .semicolon
            pure (wrapStatement .break { left := left.region.left, right := right.region.right })
        | .continue =>
            let left ← anyToken
            let right ← token .semicolon
            pure (wrapStatement .continue { left := left.region.left, right := right.region.right })
        | .semicolon =>
            let semicolon ← anyToken
            pure (wrapStatement .emptyStmt semicolon.region)
        | .auxUpd => parseUpdateStatement false
        | .ghostUpd => parseUpdateStatement true
        | .specBegin => parseSpecificationStatement
        | .asm => parseAsmStatement
        | _ => parseExpressionOrAssignmentStatement
    | none => fail "expected statement"

  partial def parseExpressionOrAssignmentStatement : Parser Statement :=
    orElse (attempt do
      let statement ← parseAssignmentStatementCore
      let semicolon ← token .semicolon
      pure (wrapStatement (AstActions.snode statement)
        { left := (statementRegion statement).left, right := semicolon.region.right }))
      (orElse (attempt parseIncrementStatement) (do
        let expression ← parseExpression
        let semicolon ← token .semicolon
        let result := AstActions.callExpressionStatement? expression
          { left := (expressionRegion expression).left, right := semicolon.region.right }
        emitActionDiagnostics result.diagnostics
        match result.value with
        | some statement => pure statement
        | none =>
            let region : Region := {
              left := (expressionRegion expression).left, right := semicolon.region.right }
            if isNumericConstant expression then pure ()
            else if expressionCallFree expression then
              warning region
                "Ignoring (oddly expressed) expression without side effect"
            else
              error region
                "Illegal bare expression containing function calls"
            pure (wrapStatement .emptyStmt region)))

  partial def parseIncrementStatement : Parser Statement := do
    let statement ← parseIncrementStatementCore
    let semicolon ← token .semicolon
    pure (wrapStatement (AstActions.snode statement)
      { left := (statementRegion statement).left, right := semicolon.region.right })

  partial def parseIfStatement : Parser Statement := do
    let keyword ← token .if
    let _ ← token .lparen
    let condition ← parseExpression
    let _ ← token .rparen
    let thenBranch ← parseStatement
    if ← currentIs .else then
      let _ ← token .else
      let elseBranch ← parseStatement
      pure (AstActions.ifThenElseStatement condition thenBranch elseBranch
        { left := keyword.region.left, right := (statementRegion elseBranch).right })
    else
      pure (AstActions.ifThenStatement condition thenBranch
        { left := keyword.region.left, right := (statementRegion thenBranch).right })

  partial def parseWhileStatement : Parser Statement := do
    let keyword ← token .while
    let _ ← token .lparen
    let condition ← parseExpression
    let _ ← token .rparen
    let invariant ← parseInvariant
    let body ← parseStatement
    pure (AstActions.whileStatement condition invariant body
      { left := keyword.region.left, right := (statementRegion body).right })

  partial def parseDoWhileStatement : Parser Statement := do
    let keyword ← token .do
    let invariant ← parseInvariant
    let body ← parseStatement
    let _ ← token .while
    let _ ← token .lparen
    let condition ← parseExpression
    let _ ← token .rparen
    let semicolon ← token .semicolon
    pure (AstActions.doWhileStatement condition invariant body
      { left := keyword.region.left, right := semicolon.region.right })

  partial def parseForStatement : Parser Statement := inScope do
    let keyword ← token .for
    let _ ← token .lparen
    let initializers ← if ← atDeclarationStart then
      let declarations ← parseDeclaration true
      pure (declarations.map BlockItem.declaration)
    else
      let statement ← parseForClauseStatements .semicolon
      let _ ← token .semicolon
      match AstActions.snode statement with
      | .emptyStmt => pure []
      | _ => pure [.statement statement]
    let condition ← if ← currentIs .semicolon then pure none else some <$> parseExpression
    let _ ← token .semicolon
    let step ← parseForClauseStatements .rparen
    let _ ← token .rparen
    let invariant ← parseInvariant
    let body ← parseStatement
    pure (AstActions.forStatement initializers condition step body invariant
      { left := keyword.region.left, right := (statementRegion body).right })

  partial def parseSwitchStatement : Parser Statement := do
    let keyword ← token .switch
    let _ ← token .lparen
    let value ← parseExpression
    let _ ← token .rparen
    let _ ← token .lcurly
    let cases ← parseSwitchCases
    let right ← token .rcurly
    let result := AstActions.switchStatement value cases
      { left := keyword.region.left, right := right.region.right }
    emitActionDiagnostics result.diagnostics
    pure result.value

  partial def parseSwitchCases : Parser (List AstActions.RawSwitchCase) := do
    let rec loop (cases : List AstActions.RawSwitchCase) :
        Parser (List AstActions.RawSwitchCase) := do
      if ← currentIs .rcurly then pure cases
      else
        let labels ← parseSwitchLabels
        let first ← parseStatement
        let rest ← parseBlockItems .rcurly
        loop (cases ++ [(labels, .statement first :: rest)])
    loop []

  partial def parseSwitchLabels : Parser (Located (List (Located (Option Expr)))) := do
    let first ← parseSwitchLabel
    let rec loop (labels : List (Located (Option Expr))) :
        Parser (List (Located (Option Expr))) := do
      if (← currentIs .case) || (← currentIs .default) then
        loop (labels ++ [← parseSwitchLabel])
      else pure labels
    let labels ← loop [first]
    let last := labels.getLast?.getD first
    pure { value := labels, region := first.region.append last.region }

  partial def parseSwitchLabel : Parser (Located (Option Expr)) := do
    if ← currentIs .case then
      let left ← token .case
      let value ← parseExpression
      let right ← token .colon
      pure { value := some value, region := { left := left.region.left, right := right.region.right } }
    else
      let left ← token .default
      let right ← token .colon
      pure { value := none, region := { left := left.region.left, right := right.region.right } }

  partial def parseReturnStatement : Parser Statement := do
    let keyword ← token .return
    let value ← if ← currentIs .semicolon then pure none else some <$> parseExpression
    let semicolon ← token .semicolon
    let result := AstActions.returnStatement value
      { left := keyword.region.left, right := semicolon.region.right }
    emitActionDiagnostics result.diagnostics
    pure result.value

  partial def parseUpdateStatement (ghost : Bool) : Parser Statement := do
    parseInlineUpdate ghost

  partial def parseSpecificationStatement : Parser Statement := do
    let keyword ← token .specBegin
    let opening ← annotationString
    let _ ← token .specBlockEnd
    let statements ← parseStatementsUntilSpecEnd
    let _ ← token .specEnd
    let closing ← annotationString
    let endToken ← token .specBlockEnd
    let header := splitSpecification opening.value
    pure (wrapStatement (.spec (header, statements, closing.value))
      { left := keyword.region.left, right := endToken.region.right })

  partial def parseStatementsUntilSpecEnd : Parser (List Statement) := do
    let rec loop (statements : List Statement) : Parser (List Statement) := do
      if ← currentIs .specEnd then pure statements
      else loop (statements ++ [← parseStatement])
    loop []

  partial def parseAsmStatement : Parser Statement := do
    let keyword ← token .asm
    let volatile := ← if ← currentIs .volatile then token .volatile *> pure true else pure false
    let _ ← token .lparen
    let block ← parseAsmBlock
    let _ ← token .rparen
    let semicolon ← token .semicolon
    pure (wrapStatement (.asmStmt volatile block)
      { left := keyword.region.left, right := semicolon.region.right })
end

private def parseFunctionDefinition (specifiers : DeclSpecifierList) (declarator : Declarator) :
    Parser ExternalDeclaration := do
  if let some region := hasTypedef specifiers then
    error region "Typedef illegal in function def"
  declareOrdinary declarator.name.value
  let base ← extractType specifiers
  let parameters ← match declarator.parameters with
    | none =>
        error declarator.region "Function def with no params!"
        pure []
    | some parameters => checkParameterNames declarator.name.value parameters
  let returnType ← match declarator.apply base.value with
    | .function returnType _ => pure returnType
    | _ =>
        error declarator.region "Attempted fn def with bad declarator"
        pure base.value
  let functionSpecs := extractFunctionSpecifiers specifiers.value
  let storageClasses := extractStorageClasses specifiers.value
  let specifications := AstActions.mergeSpecs [.gccAttributes declarator.attributes] functionSpecs
  if hasDidNotTranslate specifications then
    let _ ← parseFunctionBody parameters
    pure (.declaration {
      value := .extFnDecl returnType declarator.name
        (parameterValues declarator.parameters) storageClasses specifications
      region := specifiers.region.append declarator.region })
  else
    let body ← parseFunctionBody parameters
    pure (.functionDefinition (returnType, declarator.name) parameters storageClasses
      specifications body)

private def parseExternalDeclaration : Parser (List ExternalDeclaration) := do
  if ← currentIs .semicolon then
    let _ ← token .semicolon
    pure []
  else
    let specifiers ← parseFullDeclarationSpecifiers
    if ← currentIs .semicolon then
      let _ ← token .semicolon
      let declarations ← lowerEmptyDeclaration specifiers
      pure (declarations.map ExternalDeclaration.declaration)
    else
      let declarator ← parseDeclarator
      if ← currentIs .lcurly then
        pure [← parseFunctionDefinition specifiers declarator]
      else
        let first ← parseInitializerAfterDeclarator specifiers declarator
        let declarators ← parseRemainingInitDeclarators specifiers first
        let _ ← token .semicolon
        let declarations ← lowerDeclaration specifiers declarators false
        pure (declarations.map ExternalDeclaration.declaration)

partial def parseTranslationUnit : Parser TranslationUnit := do
  let rec loop (declarations : TranslationUnit) : Parser TranslationUnit := do
    let current ← peek?
    match current with
    | none =>
        let state ← get
        error state.currentRegion "token stream ended without EOF"
        pure declarations
    | some { value := .eof, .. } =>
        let _ ← token .eof
        pure declarations
    | some _ =>
        let parsed ← recover parseExternalDeclaration false
        match parsed with
        | some next => loop (declarations ++ next)
        | none => loop declarations
  loop []

end Zag.Lang.AutoCorres.CParser.Parser
