import Lang.AutoCorres.CParser.Parser.AstActions
import Lang.AutoCorres.CParser.Parser.TypeActions

/-!
# StrictC expressions and declarators

The expression, type-name, parameter, and declarator grammars are mutually
recursive in C. They live together here so every recursive edge remains an
ordinary pure parser call.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

private def expressionRegion (expression : Expr) : Region := AstActions.eregion expression

private def wrapExpression (node : ExprNode) (region : Region) : Expr :=
  AstActions.wrapExpr node region

private def emitDiagnostics (diagnostics : List Diagnostic) : Parser Unit :=
  diagnostics.forM fun diagnostic =>
    diagnose diagnostic.severity diagnostic.region diagnostic.message

private def applyBuiltinAction (expression : Expr) : Parser Expr := do
  let result := AstActions.handleBuiltinExpect expression
  emitDiagnostics result.diagnostics
  pure result.value

private def currentIs (kind : TokenKind) : Parser Bool := do
  let current ← peek?
  pure (current.any fun token => token.value == kind)

private def unsupported (token : Token) (form : String) : Parser α :=
  failAt token.region s!"{form} cannot be represented by the current C AST"

private def isAssignmentOperator : TokenKind → Bool
  | .assign | .plusEq | .minusEq | .bitAndEq | .bitOrEq | .mulEq
  | .divEq | .modEq | .bitXorEq | .leftShiftEq | .rightShiftEq => true
  | _ => false

private def binaryExpression (operator : BinOpType) (left right : Expr) : Expr :=
  wrapExpression (.binOp operator left right)
    ((expressionRegion left).append (expressionRegion right))

private def binaryOperator? (operators : List (TokenKind × BinOpType)) :
    Parser (Option BinOpType) := do
  let current ← peek?
  match current with
  | none => pure none
  | some current =>
      match operators.find? (fun entry => entry.1 == current.value) with
      | none => pure none
      | some (_, operator) =>
          let _ ← anyToken
          pure (some operator)

private partial def leftAssociative (operand : Parser Expr)
    (operators : List (TokenKind × BinOpType)) : Parser Expr := do
  let first ← operand
  let rec loop (left : Expr) : Parser Expr := do
    match ← binaryOperator? operators with
    | none => pure left
    | some operator =>
        let right ← operand
        loop (binaryExpression operator left right)
  loop first

private def parseSimpleTypeSpecifier : Parser TypeSpecifier := do
  let current ← peek?
  match current with
  | some current =>
      let value? := match current.value with
        | .int => some TypeSpecToken.int
        | .bool => some .bool
        | .char => some .char
        | .long => some .long
        | .short => some .short
        | .signed => some .signed
        | .unsigned => some .unsigned
        | .void => some .void
        | _ => none
      match value? with
      | some value =>
          let consumed ← anyToken
          pure (.token { value, region := consumed.region })
      | none => failAt current.region "expected type specifier"
  | none => fail "expected type specifier"

private def parseTypeQualifier : Parser (Located TypeQualifier) := do
  let current ← anyToken
  match current.value with
  | .const => pure { value := .const, region := current.region }
  | .volatile => pure { value := .volatile, region := current.region }
  | .restrict => pure { value := .restrict, region := current.region }
  | _ => failAt current.region "expected type qualifier"

private def parseStorageClass : Parser (Located StorageClassSpecifier) := do
  let current ← anyToken
  let value ← match current.value with
    | .typedef => pure StorageClassSpecifier.typeDef
    | .extern => pure .extern
    | .static => pure .static
    | .auto => pure .auto
    | .register => pure .register
    | .threadLocal => pure .threadLocal
    | _ => failAt current.region "expected storage-class specifier"
  pure { value, region := current.region }

private partial def parseStringLiteral : Parser (Located String) := do
  let first ← satisfy "string literal" fun
    | .stringLiteral _ => true
    | _ => false
  let firstValue := match first.value with
    | .stringLiteral value => value
    | _ => ""
  let rec loop (value : String) (region : Region) : Parser (Located String) := do
    let current ← peek?
    match current with
    | some { value := .stringLiteral next, region := nextRegion } =>
        let _ ← anyToken
        loop (value ++ next) (region.append nextRegion)
    | _ => pure { value, region }
  loop firstValue first.region

private structure ParsedStructDeclaration where
  fields : List StructField
  nested : List (Located StructIdDecl)
deriving Repr, Inhabited

private def appendStructDeclaration (left right : ParsedStructDeclaration) :
    ParsedStructDeclaration :=
  { fields := left.fields ++ right.fields, nested := left.nested ++ right.nested }

mutual
  partial def parseExpression : Parser Expr := do
    let condition ← parseLogicalOrExpression
    if ← currentIs .question then
      let _ ← token .question
      let thenExpression ← parseExpression
      let _ ← token .colon
      let elseExpression ← parseExpression
      pure <| wrapExpression (.condExp condition thenExpression elseExpression)
        ((expressionRegion condition).append (expressionRegion elseExpression))
    else
      let current ← peek?
      match current with
      | some operator =>
          if isAssignmentOperator operator.value then
            let operator ← anyToken
            unsupported operator "assignment expressions"
          else
            pure condition
      | none => pure condition

  partial def parseLogicalOrExpression : Parser Expr :=
    leftAssociative parseLogicalAndExpression [(.logicalOr, .logOr)]

  partial def parseLogicalAndExpression : Parser Expr :=
    leftAssociative parseInclusiveOrExpression [(.logicalAnd, .logAnd)]

  partial def parseInclusiveOrExpression : Parser Expr :=
    leftAssociative parseExclusiveOrExpression [(.bitwiseOr, .bitwiseOr)]

  partial def parseExclusiveOrExpression : Parser Expr :=
    leftAssociative parseAndExpression [(.bitwiseXor, .bitwiseXor)]

  partial def parseAndExpression : Parser Expr :=
    leftAssociative parseEqualityExpression [(.ampersand, .bitwiseAnd)]

  partial def parseEqualityExpression : Parser Expr :=
    leftAssociative parseRelationalExpression
      [(.equals, .equals), (.notEquals, .notEquals)]

  partial def parseRelationalExpression : Parser Expr :=
    leftAssociative parseShiftExpression
      [(.less, .lt), (.greater, .gt), (.lessEq, .leq), (.greaterEq, .geq)]

  partial def parseShiftExpression : Parser Expr :=
    leftAssociative parseAdditiveExpression [(.leftShift, .lShift), (.rightShift, .rShift)]

  partial def parseAdditiveExpression : Parser Expr :=
    leftAssociative parseMultiplicativeExpression [(.plus, .plus), (.minus, .minus)]

  partial def parseMultiplicativeExpression : Parser Expr :=
    leftAssociative parseCastExpression [(.star, .times), (.slash, .divides), (.mod, .modulus)]

  partial def parseCastExpression : Parser Expr :=
    orElse (attempt do
      let left ← token .lparen
      let type ← parseTypeName
      let _ ← token .rparen
      let expression ← parseCastExpression
      pure <| wrapExpression (.typeCast type expression)
        { left := left.region.left, right := (expressionRegion expression).right })
      parseUnaryExpression

  partial def parseUnaryExpression : Parser Expr := do
    let current ← peek?
    match current with
    | some current =>
        match current.value with
        | .minus =>
            let operator ← anyToken
            let operand ← parseCastExpression
            pure <| wrapExpression (.unOp .negate operand)
              { left := operator.region.left, right := (expressionRegion operand).right }
        | .not =>
            let operator ← anyToken
            let operand ← parseCastExpression
            pure <| wrapExpression (.unOp .not operand)
              { left := operator.region.left, right := (expressionRegion operand).right }
        | .bitNot =>
            let operator ← anyToken
            let operand ← parseCastExpression
            pure <| wrapExpression (.unOp .bitNegate operand)
              { left := operator.region.left, right := (expressionRegion operand).right }
        | .ampersand =>
            let operator ← anyToken
            let operand ← parseCastExpression
            pure <| wrapExpression (.unOp .addr operand)
              { left := operator.region.left, right := (expressionRegion operand).right }
        | .star =>
            let operator ← anyToken
            let operand ← parseCastExpression
            pure <| wrapExpression (.deref operand)
              { left := operator.region.left, right := (expressionRegion operand).right }
        | .sizeof => parseSizeofExpression
        | .plusPlus =>
            let operator ← anyToken
            unsupported operator "prefix increment"
        | .minusMinus =>
            let operator ← anyToken
            unsupported operator "prefix decrement"
        | _ => parsePostfixExpression
    | none => fail "expected unary expression"

  partial def parseSizeofExpression : Parser Expr := do
    let keyword ← token .sizeof
    orElse (attempt do
      let _ ← token .lparen
      let type ← parseTypeName
      let right ← token .rparen
      pure <| wrapExpression (.sizeofTy type)
        { left := keyword.region.left, right := right.region.right }) (do
      let expression ← parseUnaryExpression
      pure <| wrapExpression (.sizeof expression)
        { left := keyword.region.left, right := (expressionRegion expression).right })

  partial def parsePostfixExpression : Parser Expr := do
    let base ← orElse (attempt parseCompoundLiteral) parsePrimaryExpression
    let rec loop (expression : Expr) : Parser Expr := do
      let current ← peek?
      match current with
      | some current =>
          match current.value with
          | .lbracket =>
              let _ ← anyToken
              let index ← parseExpression
              let right ← token .rbracket
              loop <| wrapExpression (.arrayDeref expression index)
                { left := (expressionRegion expression).left, right := right.region.right }
          | .lparen =>
              let _ ← anyToken
              let arguments ← parseExpressionList .rparen
              let right ← token .rparen
              let call := wrapExpression (.eFnCall expression arguments)
                { left := (expressionRegion expression).left, right := right.region.right }
              loop (← applyBuiltinAction call)
          | .dot =>
              let _ ← anyToken
              let field ← rawIdentifier
              loop <| wrapExpression (.structDot expression (cFieldName field.value))
                { left := (expressionRegion expression).left, right := field.region.right }
          | .arrow =>
              let _ ← anyToken
              let field ← rawIdentifier
              let dereference := wrapExpression (.deref expression) (expressionRegion expression)
              loop <| wrapExpression (.structDot dereference (cFieldName field.value))
                { left := (expressionRegion expression).left, right := field.region.right }
          | .plusPlus =>
              let operator ← anyToken
              unsupported operator "postfix increment"
          | .minusMinus =>
              let operator ← anyToken
              unsupported operator "postfix decrement"
          | _ => pure expression
      | none => pure expression
    loop base

  partial def parseCompoundLiteral : Parser Expr := do
    let left ← token .lparen
    let type ← parseTypeName
    let _ ← token .rparen
    let _ ← token .lcurly
    let initializers ← parseInitializerEntries true
    let right ← token .rcurly
    pure <| wrapExpression (.compLiteral type.value initializers)
      { left := left.region.left, right := right.region.right }

  partial def parsePrimaryExpression : Parser Expr := do
    let current ← peek?
    match current with
    | some current =>
        match current.value with
        | .ident _ | .typeIdent _ =>
            let name ← identifier
            pure <| wrapExpression (.var name.value none) name.region
        | .numeric literal =>
            let consumed ← anyToken
            let constant : LiteralConstant := {
              value := .numConst {
                value := Int.ofNat literal.value, suffix := literal.suffix, base := literal.radix }
              region := consumed.region }
            pure <| wrapExpression (.constant constant) consumed.region
        | .stringLiteral _ =>
            let literal ← parseStringLiteral
            let constant : LiteralConstant := {
              value := .stringLit literal.value, region := literal.region }
            pure <| wrapExpression (.constant constant) literal.region
        | .lparen =>
            let left ← anyToken
            if ← currentIs .lcurly then
              unsupported left "statement expressions"
            let expression ← parseExpression
            if ← currentIs .comma then
              let comma ← token .comma
              unsupported comma "comma expressions"
            let right ← token .rparen
            let node := AstActions.enode expression
            pure <| wrapExpression node { left := left.region.left, right := right.region.right }
        | _ => failAt current.region "expected primary expression"
    | none => fail "expected primary expression"

  partial def parseExpressionList (terminator : TokenKind) : Parser (List Expr) := do
    if ← currentIs terminator then
      pure []
    else
      let first ← parseExpression
      let rec loop (values : List Expr) : Parser (List Expr) := do
        if ← currentIs .comma then
          let _ ← token .comma
          let next ← parseExpression
          loop (values ++ [next])
        else
          pure values
      loop [first]

  partial def parseInitializer : Parser Initializer := do
    if ← currentIs .lcurly then
      let _ ← token .lcurly
      if ← currentIs .rcurly then
        let _ ← token .rcurly
        pure (.initList [])
      else
        let entries ← parseInitializerEntries true
        let _ ← token .rcurly
        pure (.initList entries)
    else
      pure (.initE (← parseExpression))

  partial def parseInitializerEntries (allowTrailingComma : Bool) :
      Parser (List (List Designator × Initializer)) := do
    let first ← parseDesignatedInitializer
    let rec loop (values : List (List Designator × Initializer)) :
        Parser (List (List Designator × Initializer)) := do
      if ← currentIs .comma then
        let _ ← token .comma
        if allowTrailingComma && (← currentIs .rcurly) then
          pure values
        else
          let next ← parseDesignatedInitializer
          loop (values ++ [next])
      else
        pure values
    loop [first]

  partial def parseDesignatedInitializer : Parser (List Designator × Initializer) := do
    let designators ← parseDesignation
    let initializer ← parseInitializer
    pure (designators, initializer)

  partial def parseDesignation : Parser (List Designator) := do
    let current ← peek?
    match current with
    | some { value := .lbracket, .. } | some { value := .dot, .. } =>
        let designators ← many1 parseDesignator
        let _ ← token .assign
        pure designators
    | _ => pure []

  partial def parseDesignator : Parser Designator := do
    if ← currentIs .lbracket then
      let _ ← token .lbracket
      let expression ← parseExpression
      let _ ← token .rbracket
      pure (.designE expression)
    else
      let _ ← token .dot
      let field ← rawIdentifier
      pure (.designFld (cFieldName field.value))

  partial def parseGccAttribute : Parser GccAttribute := do
    let nameToken ← anyToken
    let name ← match nameToken.value with
      | .ident name | .typeIdent name => pure name
      | .const => pure "const"
      | _ => failAt nameToken.region "expected GCC attribute"
    if ← currentIs .lparen then
      let _ ← token .lparen
      let arguments ← parseExpressionList .rparen
      let _ ← token .rparen
      pure (.attribFn name arguments)
    else
      pure (.attribId (normalizeGccAttributeName name))

  partial def parseAttributeSpecifier : Parser (Located (List GccAttribute)) := do
    if ← currentIs .ownedBy then
      let left ← token .ownedBy
      let owner ← rawIdentifier
      let right ← token .specBlockEnd
      pure {
        value := [.ownedBy owner.value]
        region := { left := left.region.left, right := right.region.right } }
    else
      let left ← token .gccAttribute
      let _ ← token .lparen
      let _ ← token .lparen
      let attributes ← if ← currentIs .rparen then pure [] else do
        let first ← parseGccAttribute
        let rec loop (values : List GccAttribute) : Parser (List GccAttribute) := do
          if ← currentIs .comma then
            let _ ← token .comma
            if ← currentIs .rparen then pure values
            else loop (values ++ [← parseGccAttribute])
          else pure values
        loop [first]
      let _ ← token .rparen
      let right ← token .rparen
      pure { value := attributes, region := { left := left.region.left, right := right.region.right } }

  partial def parseTypeSpecifier : Parser TypeSpecifier := do
    let current ← peek?
    match current with
    | some { value := .struct, .. } => parseStructSpecifier
    | some { value := .enum, .. } => parseEnumSpecifier
    | some { value := .typeIdent _, .. } =>
        let name ← typedefIdentifier
        pure (.typeId name)
    | some { value := .ident name, region } =>
        let state ← get
        if state.lookupName name = some .typedefName then
          let name ← typedefIdentifier
          pure (.typeId name)
        else
          failAt region "expected type specifier"
    | _ => parseSimpleTypeSpecifier

  partial def parseStructSpecifier : Parser TypeSpecifier := do
    let keyword ← token .struct
    let current ← peek?
    let name? ← match current with
      | some { value := .ident _, .. } | some { value := .typeIdent _, .. } =>
          some <$> rawIdentifier
      | _ => pure none
    if ← currentIs .lcurly then
      let opening ← token .lcurly
      let declarations ← parseStructDeclarationList
      let closing ← token .rcurly
      match name? with
      | some name =>
          return makeNamedStruct keyword.region closing.region name
            declarations.fields declarations.nested
      | none =>
          return ← makeAnonymousStruct keyword.region opening.region closing.region
            declarations.fields declarations.nested
    else
      match name? with
      | some name => return makeStructReference keyword.region name
      | none => return ← failAt keyword.region "struct requires a tag or a definition"

  partial def parseStructDeclarationList : Parser ParsedStructDeclaration := do
    if ← currentIs .rcurly then
      fail "empty struct definitions are not accepted by StrictC"
    let first ← parseStructDeclaration
    let rec loop (result : ParsedStructDeclaration) : Parser ParsedStructDeclaration := do
      if ← currentIs .rcurly then
        pure result
      else
        loop (appendStructDeclaration result (← parseStructDeclaration))
    loop first

  partial def parseStructDeclaration : Parser ParsedStructDeclaration := do
    let specifiers ← parseSpecifierQualifierList
    let base ← extractType specifiers
    let nested := firstStructDeclarations specifiers.value
    if let some enumSpecifier := firstEnumDeclaration specifiers.value then
      error enumSpecifier.region "Don't declare enumerations inside structs"
    if ← currentIs .semicolon then
      let semicolon ← token .semicolon
      let name : Located String := {
        value := "", region := { left := specifiers.region.left, right := semicolon.region.left } }
      pure { fields := [(base.value, name)], nested }
    else
      let declarators ← sepBy1 parseStructDeclarator (token .comma)
      let _ ← token .semicolon
      let fields ← declarators.mapM fun declarator => do
        let rawName := declarator.declarator.value.name
        let fieldName := { rawName with value := cFieldName rawName.value }
        let type := declarator.declarator.value.apply base.value
        let type ← match declarator.bitWidth with
          | none => pure type
          | some width => applyBitfield type fieldName width
        pure (type, fieldName)
      pure { fields, nested }

  partial def parseStructDeclarator : Parser StructDeclarator := do
    let declarator ← parseDeclarator
    let bitWidth ← if ← currentIs .colon then
      let _ ← token .colon
      some <$> parseExpression
    else pure none
    pure { declarator := { value := declarator, region := declarator.region }, bitWidth }

  partial def parseEnumSpecifier : Parser TypeSpecifier := do
    let keyword ← token .enum
    let current ← peek?
    let tag? ← match current with
      | some { value := .ident _, .. } | some { value := .typeIdent _, .. } =>
          some <$> rawIdentifier
      | _ => pure none
    if ← currentIs .lcurly then
      let _ ← token .lcurly
      let enumerators ← sepBy1 parseEnumerator (token .comma)
      if ← currentIs .comma then
        let _ ← token .comma
        pure ()
      let right ← token .rcurly
      let name : Located (Option String) := match tag? with
        | some tag => { value := some tag.value, region := tag.region }
        | none => { value := none, region := keyword.region }
      pure (.enum {
        name
        enumerators
        region := { left := keyword.region.left, right := right.region.right } })
    else
      match tag? with
      | some tag => pure (.enum {
          name := { value := some tag.value, region := tag.region }
          enumerators := []
          region := keyword.region.append tag.region })
      | none => failAt keyword.region "enum requires a tag or a definition"

  partial def parseEnumerator : Parser (Located String × Option Expr) := do
    let name ← rawIdentifier
    let value ← if ← currentIs .assign then
      let _ ← token .assign
      some <$> parseExpression
    else pure none
    declareOrdinary name.value
    pure (name, value)

  partial def parseDeclarationSpecifiers (allowStorage : Bool := true) :
      Parser DeclSpecifierList := do
    let startState ← get
    let rec loop (values : List DeclSpecifier) (hasBase : Bool) : Parser (List DeclSpecifier) := do
      let current ← peek?
      match current with
      | some current =>
          match current.value with
          | .typedef | .extern | .static | .auto | .register | .threadLocal =>
              if allowStorage then
                loop (values ++ [.storage (← parseStorageClass)]) hasBase
              else pure values
          | .const | .volatile | .restrict =>
              loop (values ++ [.typeQualifier (← parseTypeQualifier)]) hasBase
          | .int | .bool | .char | .long | .short | .void =>
              loop (values ++ [.typeSpecifier (← parseTypeSpecifier)]) true
          | .signed | .unsigned =>
              loop (values ++ [.typeSpecifier (← parseTypeSpecifier)]) hasBase
          | .struct | .enum =>
              loop (values ++ [.typeSpecifier (← parseTypeSpecifier)]) true
          | .typeIdent _ =>
              if hasBase then pure values
              else loop (values ++ [.typeSpecifier (← parseTypeSpecifier)]) true
          | .ident _ =>
              pure values
          | .inline =>
              if allowStorage then
                let inlineToken ← anyToken
                let ignored : Located FunctionSpec := {
                  value := .gccAttributes [], region := inlineToken.region }
                loop (values ++ [.functionSpecifier ignored]) hasBase
              else pure values
          | .noReturn =>
              if allowStorage then
                let noReturn ← anyToken
                let specifier : Located FunctionSpec := {
                  value := .gccAttributes [.attribId "noreturn"], region := noReturn.region }
                loop (values ++ [.functionSpecifier specifier]) hasBase
              else pure values
          | .gccAttribute | .ownedBy =>
              if allowStorage then
                let attributes ← parseAttributeSpecifier
                let specifier : Located FunctionSpec := {
                  value := .gccAttributes attributes.value, region := attributes.region }
                loop (values ++ [.functionSpecifier specifier]) hasBase
              else pure values
          | _ => pure values
      | none => pure values
    let values ← loop [] false
    match values with
    | [] => failAt startState.currentRegion "expected declaration specifiers"
    | first :: rest =>
        let last := rest.getLast?.getD first
        pure { value := values, region := first.region.append last.region }

  partial def parseSpecifierQualifierList : Parser DeclSpecifierList :=
    parseDeclarationSpecifiers false

  partial def parsePointer : Parser AbstractDeclarator := do
    let star ← token .star
    let qualifiers ← many (attempt parseTypeQualifier)
    let rightRegion := qualifiers.getLast?.map (·.region) |>.getD star.region
    let current : AbstractDeclarator := .pointer (star.region.append rightRegion)
    if ← currentIs .star then
      pure (current.compose (← parsePointer))
    else
      pure current

  partial def parseDeclarator : Parser Declarator := do
    let pointer? ← if ← currentIs .star then some <$> parsePointer else pure none
    let attributes ← if pointer?.isSome && ((← currentIs .gccAttribute) || (← currentIs .ownedBy)) then
      let attributes ← parseAttributeSpecifier
      pure attributes.value
    else
      pure []
    let direct ← parseDirectDeclarator
    let direct := direct.addAttributes attributes
    pure <| match pointer? with
      | some pointer => direct.compose pointer
      | none => direct

  partial def parseDirectDeclarator : Parser Declarator := do
    let base ← orElse (do
      let name ← rawIdentifier
      pure (Declarator.direct name)) (attempt do
      let _ ← token .lparen
      let declarator ← parseDeclarator
      let _ ← token .rparen
      pure declarator)
    parseDirectDeclaratorSuffixes base

  partial def parseDirectDeclaratorSuffixes (initial : Declarator) : Parser Declarator := do
    let rec loop (declarator : Declarator) : Parser Declarator := do
      let current ← peek?
      match current with
      | some current =>
          match current.value with
          | .lbracket =>
              let left ← anyToken
              let size ← if ← currentIs .rbracket then pure none else some <$> parseExpression
              let right ← token .rbracket
              let layer := AbstractDeclarator.array
                { left := left.region.left, right := right.region.right } size
              loop (declarator.compose layer)
          | .lparen =>
              let left ← anyToken
              let rawParameters ← inScope parseParameterList
              let right ← token .rparen
              let parameters ← checkParameters {
                value := rawParameters
                region := { left := left.region.left, right := right.region.right } }
              parseCallsBlock
              let parameterTypes := parameters.map (·.value.1)
              let layer := AbstractDeclarator.function
                { left := left.region.left, right := right.region.right } parameterTypes
              loop ((declarator.compose layer).addParameters parameters)
          | .gccAttribute | .ownedBy =>
              let attributes ← parseAttributeSpecifier
              loop (declarator.addAttributes attributes.value)
          | .asm =>
              parseAsmDeclaratorModifier
              loop declarator
          | _ => pure declarator
      | none => pure declarator
    loop initial

  partial def parseCallsBlock : Parser Unit := do
    if ← currentIs .calls then
      let _ ← token .calls
      let rec ids : Parser Unit := do
        if ← currentIs .specBlockEnd then
          pure ()
        else if ← currentIs .lbracket then
          let _ ← token .lbracket
          let _ ← token .star
          let _ ← token .rbracket
          ids
        else
          let _ ← rawIdentifier
          ids
      ids
      let _ ← token .specBlockEnd
      pure ()
    else pure ()

  partial def parseAsmDeclaratorModifier : Parser Unit := do
    let _ ← token .asm
    let _ ← token .lparen
    let _ ← parseStringLiteral
    let _ ← token .rparen
    pure ()

  partial def parseParameterList : Parser (List Parameter) := do
    if ← currentIs .rparen then
      pure []
    else
      sepBy1 parseParameterDeclaration (token .comma)

  partial def parseParameterDeclaration : Parser Parameter := do
    let specifiers ← parseDeclarationSpecifiers
    orElse (attempt do
      let declarator ← parseDeclarator
      let parameter ← makeParameter specifiers (some declarator)
      declareOrdinary declarator.name.value
      pure parameter)
      (orElse (attempt do
        let declarator ← parseAbstractDeclarator
        makeAbstractParameter specifiers declarator)
        (makeParameter specifiers))

  partial def parseAbstractDeclarator : Parser AbstractDeclarator := do
    let pointer? ← if ← currentIs .star then some <$> parsePointer else pure none
    let direct? ← if (← currentIs .lparen) || (← currentIs .lbracket) then
      some <$> parseDirectAbstractDeclarator
    else pure none
    match pointer?, direct? with
    | none, none => fail "expected abstract declarator"
    | some pointer, none => pure pointer
    | none, some direct => pure direct
    | some pointer, some direct =>
        let composed := direct.compose pointer
        pure { composed with
          region := { left := pointer.region.left, right := direct.region.right } }

  partial def parseDirectAbstractDeclarator : Parser AbstractDeclarator := do
    let base ← if ← currentIs .lbracket then
      parseAbstractArray
    else
      orElse (attempt do
        let left ← token .lparen
        let declarator ← parseAbstractDeclarator
        let right ← token .rparen
        pure { declarator with region := { left := left.region.left, right := right.region.right } })
        (do
          let left ← token .lparen
          let rawParameters ← inScope parseParameterList
          let right ← token .rparen
          let parameters ← checkParameters {
            value := rawParameters
            region := { left := left.region.left, right := right.region.right } }
          pure <| AbstractDeclarator.function
            { left := left.region.left, right := right.region.right }
            (parameters.map (·.value.1)))
    parseDirectAbstractSuffixes base

  partial def parseAbstractArray : Parser AbstractDeclarator := do
    let left ← token .lbracket
    if ← currentIs .rbracket then
      let right ← token .rbracket
      -- This surprising pointer layer is the pinned grammar action.
      pure (.pointer { left := left.region.left, right := right.region.right })
    else
      let size ← parseExpression
      let right ← token .rbracket
      pure (.array { left := left.region.left, right := right.region.right } (some size))

  partial def parseDirectAbstractSuffixes (initial : AbstractDeclarator) :
      Parser AbstractDeclarator := do
    let rec loop (declarator : AbstractDeclarator) : Parser AbstractDeclarator := do
      if ← currentIs .lbracket then
        let layer ← parseAbstractArray
        loop (declarator.compose layer)
      else if ← currentIs .lparen then
        let left ← token .lparen
        let rawParameters ← inScope parseParameterList
        let right ← token .rparen
        let parameters ← checkParameters {
          value := rawParameters
          region := { left := left.region.left, right := right.region.right } }
        let layer := AbstractDeclarator.function
          { left := left.region.left, right := right.region.right }
          (parameters.map (·.value.1))
        loop (declarator.compose layer)
      else
        pure declarator
    loop initial

  partial def parseTypeName : Parser (Located (CType Expr)) := do
    let specifiers ← parseSpecifierQualifierList
    let base ← extractType specifiers
    let abstract? ← if (← currentIs .star) || (← currentIs .lparen) ||
        (← currentIs .lbracket) then
      optional (attempt parseAbstractDeclarator)
    else pure none
    match abstract? with
    | none => pure base
    | some declarator => pure {
        value := declarator.apply base.value
        region := specifiers.region.append declarator.region }
end

def isLValue : Expr → Bool
  | .e ⟨.var _ _, _⟩ => true
  | .e ⟨.structDot _ _, _⟩ => true
  | .e ⟨.arrayDeref _ _, _⟩ => true
  | .e ⟨.deref _, _⟩ => true
  | .e ⟨.compLiteral _ _, _⟩ => true
  | _ => false

def parseLExpression : Parser Expr := do
  let expression ← orElse (attempt do
    let star ← token .star
    let operand ← parseCastExpression
    pure <| wrapExpression (.deref operand)
      { left := star.region.left, right := (expressionRegion operand).right })
    parsePostfixExpression
  if isLValue expression then
    pure expression
  else
    failAt (expressionRegion expression) "expression is not an lvalue"

def parseAssignmentOperator : Parser (Option BinOpType) := do
  let operator ← anyToken
  match operator.value with
  | .assign => pure none
  | .plusEq => pure (some .plus)
  | .minusEq => pure (some .minus)
  | .bitOrEq => pure (some .bitwiseOr)
  | .bitAndEq => pure (some .bitwiseAnd)
  | .bitXorEq => pure (some .bitwiseXor)
  | .mulEq => pure (some .times)
  | .divEq => pure (some .divides)
  | .modEq => pure (some .modulus)
  | .leftShiftEq => pure (some .lShift)
  | .rightShiftEq => pure (some .rShift)
  | _ => failAt operator.region "expected assignment operator"

end Zag.Lang.AutoCorres.CParser.Parser
