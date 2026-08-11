import Lang.AutoCorres.CParser.Target
import Lang.AutoCorres.CParser.Token

/-!
# Pure StrictC lexer

This ports the state and observable tokenization rules of pinned `StrictC.lex`.
It performs no IO: the filename, target model, and complete source text are
explicit inputs and diagnostics are returned with the token stream.
-/

namespace Zag.Lang.AutoCorres.CParser

namespace Lexer

private inductive Mode where
  | initial
  | typedef
  | tag
  | tagName
  | tagBody
  | specialCommentStart
  | specialComment
  | specialCommentJunk
  | charLiteral
deriving Repr, DecidableEq, Inhabited

private structure State where
  input : Array Char
  index : Nat := 0
  source : SourceMap
  target : Target
  mode : Mode := .initial
  returnMode : Mode := .initial
  typedefScopes : List (List String) := [[]]
  typedefParenDepth : Nat := 0
  tagBraceDepth : Nat := 0
  typedefNameSeen : Bool := false
  charLiteralContent : List Nat := []
  charLiteralStart : Nat := 0
  tokens : Array Token := #[]
  diagnostics : Array Diagnostic := #[]

structure Result where
  tokens : Array Token
  diagnostics : Array Diagnostic
deriving Repr, Inhabited

private def State.atEnd (state : State) : Bool :=
  state.index >= state.input.size

private def State.peek? (state : State) (lookahead : Nat := 0) : Option Char :=
  state.input[state.index + lookahead]?

private def State.startsWith (state : State) (text : String) : Bool :=
  let chars := text.toList
  chars.zipIdx.all fun (character, offset) => state.peek? offset = some character

private def State.startsWithAt (state : State) (start : Nat) (text : String) : Bool :=
  text.toList.zipIdx.all fun (character, offset) => state.input[start + offset]? = some character

private def State.position (state : State) (offset := state.index) : SourcePos :=
  state.source.position offset

private def State.text (state : State) (start finish : Nat) : String :=
  String.ofList (state.input.toList.drop start |>.take (finish - start))

private def State.region (state : State) (start finish : Nat) : Region :=
  { left := state.position start
    right := state.position (if finish = 0 then 0 else finish - 1) }

private def State.advanceOne (state : State) : State :=
  match state.peek? with
  | some '\n' =>
      { state with
        index := state.index + 1
        source := state.source.newline (state.index + 1) }
  | some _ => { state with index := state.index + 1 }
  | none => state

private def State.advanceRaw (state : State) (count : Nat := 1) : State :=
  { state with index := min (state.index + count) state.input.size }

private def State.advanceNewline (state : State) : State :=
  if state.startsWith "\r\n" then
    { state with
      index := state.index + 2
      source := state.source.newline (state.index + 1) }
  else
    { state with
      index := state.index + 1
      source := state.source.newline (state.index + 1) }

private def State.advance (state : State) (count : Nat) : State :=
  go count state
where
  go : Nat → State → State
    | 0, state => state
    | count + 1, state => go count state.advanceOne

private def State.emitFrom (state : State) (start : Nat) (kind : TokenKind) : State :=
  { state with tokens := state.tokens.push { value := kind, region := state.region start state.index } }

private def State.emitAt (state : State) (left right : SourcePos) (kind : TokenKind) : State :=
  { state with tokens := state.tokens.push { value := kind, region := { left, right } } }

private def State.emitOnePast (state : State) (start : Nat) (kind : TokenKind) : State :=
  state.emitAt (state.position start) (state.position state.index) kind

private def State.diagnose (state : State) (severity : Severity) (start finish : Nat)
    (message : String) : State :=
  { state with diagnostics := state.diagnostics.push {
      severity, region := state.region start finish, message } }

private def State.error (state : State) (start finish : Nat) (message : String) : State :=
  state.diagnose .error start finish message

private def State.errorAt (state : State) (left right : SourcePos) (message : String) : State :=
  { state with diagnostics := state.diagnostics.push {
      severity := .error, region := { left, right }, message } }

private def isAlpha (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z')

private def isDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def isHexDigit (character : Char) : Bool :=
  character.isDigit || ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

private def isIdentStart (character : Char) : Bool :=
  isAlpha character || character = '_'

private def isIdentRest (character : Char) : Bool :=
  isIdentStart character || isDigit character

private partial def State.takeWhile (state : State) (predicate : Char → Bool) : State × String :=
  let start := state.index
  let state := go state
  (state, String.ofList (state.input.toList.drop start |>.take (state.index - start)))
where
  go (state : State) : State :=
    match state.peek? with
    | some character => if predicate character then go state.advanceOne else state
    | none => state

private def digitValue? (radix : Nat) (character : Char) : Option Nat :=
  let value? :=
    if isDigit character then some (character.toNat - '0'.toNat)
    else if 'a' ≤ character && character ≤ 'f' then some (10 + character.toNat - 'a'.toNat)
    else if 'A' ≤ character && character ≤ 'F' then some (10 + character.toNat - 'A'.toNat)
    else none
  value?.bind fun value => if value < radix then some value else none

private def parseDigits (radix : Nat) (digits : String) : Nat :=
  digits.toList.foldl (fun value character =>
    value * radix + (digitValue? radix character).getD 0) 0

private def integerSuffixes : List String :=
  ["ull", "uLL", "Ull", "ULL", "llu", "llU", "LLu", "LLU",
   "ul", "uL", "Ul", "UL", "lu", "lU", "Lu", "LU",
   "u", "U", "ll", "LL", "l", "L"]

private def suffixEnd (state : State) (start : Nat) : Nat :=
  match integerSuffixes.find? (state.startsWithAt start) with
  | some suffix => start + suffix.length
  | none => start

private partial def State.scanWhileFrom (state : State) (start : Nat)
    (predicate : Char → Bool) : Nat :=
  go start
where
  go (index : Nat) : Nat :=
    match state.input[index]? with
    | some character => if predicate character then go (index + 1) else index
    | none => index

private structure NumberCandidate where
  finish : Nat
  digitsStart : Nat
  digitsEnd : Nat
  validDigitsEnd : Nat
  radix : Radix

private def State.numberCandidate (state : State) : NumberCandidate :=
  let start := state.index
  if state.startsWith "0x" || state.startsWith "0X" then
    let digitsStart := start + 2
    let digitsEnd := state.scanWhileFrom digitsStart isHexDigit
    { finish := suffixEnd state digitsEnd
      digitsStart, digitsEnd, validDigitsEnd := digitsEnd, radix := .hexadecimal }
  else if state.startsWith "0b" || state.startsWith "0B" then
    let digitsStart := start + 2
    let digitsEnd := state.scanWhileFrom digitsStart isDigit
    let validDigitsEnd := state.scanWhileFrom digitsStart fun character =>
      (digitValue? 2 character).isSome
    { finish := suffixEnd state digitsEnd
      digitsStart, digitsEnd, validDigitsEnd, radix := .binary }
  else if state.peek? = some '0' && (state.peek? 1).any isDigit then
    let digitsEnd := state.scanWhileFrom start isDigit
    let validDigitsEnd := state.scanWhileFrom start fun character =>
      (digitValue? 8 character).isSome
    { finish := suffixEnd state digitsEnd
      digitsStart := start, digitsEnd, validDigitsEnd, radix := .octal }
  else
    let digitsEnd := state.scanWhileFrom start isDigit
    { finish := suffixEnd state digitsEnd
      digitsStart := start, digitsEnd, validDigitsEnd := digitsEnd, radix := .decimal }

private def State.lexNumber (state : State) : State :=
  let start := state.index
  let candidate := state.numberCandidate
  let radixNat := match candidate.radix with
    | .binary => 2 | .octal => 8 | .decimal => 10 | .hexadecimal => 16
  let radixName := match candidate.radix with
    | .binary => "binary" | .octal => "octal"
    | .decimal => "decimal" | .hexadecimal => "hexadecimal"
  let digits := state.text candidate.digitsStart candidate.validDigitsEnd
  let suffix := state.text candidate.digitsEnd candidate.finish
  let state := state.advance (candidate.finish - start)
  let state := state.emitFrom start (.numeric {
    value := parseDigits radixNat digits, radix := candidate.radix, suffix })
  if candidate.validDigitsEnd < candidate.digitsEnd then
    state.error candidate.validDigitsEnd candidate.digitsEnd
      s!"Invalid digit in {radixName} integer literal"
  else if candidate.validDigitsEnd = candidate.digitsStart &&
      (candidate.radix = .binary || candidate.radix = .hexadecimal) then
    state.error start candidate.digitsStart
      s!"Missing digits in {radixName} integer literal"
  else state

private def State.inTypedefScope (state : State) (name : String) : Bool :=
  state.typedefScopes.any (·.contains name)

private def State.addTypedef (state : State) (name : String) : State :=
  match state.typedefScopes with
  | [] => { state with typedefScopes := [[name]] }
  | scope :: scopes => { state with typedefScopes := (name :: scope) :: scopes }

private def underscoreSafe (name : String) : String :=
  if name.startsWith "_" then "StrictC'" ++ name else name

private def commonKeyword? (name : String) : Option TokenKind :=
  match name with
  | "extern" => some .extern
  | "unsigned" => some .unsigned
  | "signed" => some .signed
  | "short" => some .short
  | "long" => some .long
  | "int" => some .int
  | "char" => some .char
  | "_Bool" => some .bool
  | "void" => some .void
  | "inline" => some .inline
  | "_Noreturn" => some .noReturn
  | "static" => some .static
  | "if" => some .if
  | "else" => some .else
  | "while" => some .while
  | "const" => some .const
  | "volatile" => some .volatile
  | "restrict" => some .restrict
  | "switch" => some .switch
  | "case" => some .case
  | "default" => some .default
  | "do" => some .do
  | "for" => some .for
  | "break" => some .break
  | "continue" => some .continue
  | "return" => some .return
  | "sizeof" => some .sizeof
  | "__attribute__" => some .gccAttribute
  | _ => none

private def keyword? (mode : Mode) (name : String) : Option TokenKind :=
  match name, mode with
  | "struct", .initial | "struct", .tagBody => some .struct
  | "struct", .typedef => some .struct
  | "union", .typedef => some .union
  | "enum", .typedef => some .enum
  | "enum", .initial | "enum", .tag | "enum", .tagName | "enum", .tagBody => some .enum
  | "typedef", _ => some .typedef
  | "register", .initial => some .register
  | "_Thread_local", .initial => some .threadLocal
  | "auto", .initial => some .auto
  | "__asm__", .initial | "asm", .initial => some .asm
  | _, _ => commonKeyword? name

private def State.resolveIdentifier (state : State) (start : Nat) (rawName : String) : State :=
  let name := underscoreSafe rawName
  match state.mode with
  | .tag => { state.emitFrom start (.ident name) with mode := .tagName }
  | .typedef | .tagName =>
      if state.inTypedefScope name then state.emitFrom start (.typeIdent name)
      else
        let state := state.emitFrom start (.ident name)
        if state.typedefParenDepth = 0 && !state.typedefNameSeen then
          { state.addTypedef name with typedefNameSeen := true }
        else state
  | _ => state.emitFrom start
      (if state.inTypedefScope name then .typeIdent name else .ident name)

private def State.lexIdentifier (state : State) : State :=
  let start := state.index
  let (state, name) := state.takeWhile isIdentRest
  match keyword? state.mode name with
  | some .typedef =>
      if state.mode = .initial then
        { state.emitFrom start .typedef with
          mode := .typedef, typedefParenDepth := 0,
          tagBraceDepth := 0, typedefNameSeen := false }
      else
        state.error start state.index "typedef not allowed here"
  | some (.struct) =>
      let state := state.emitFrom start .struct
      if state.mode = .typedef then { state with mode := .tag, returnMode := .typedef }
      else state
  | some (.union) =>
      let state := state.emitFrom start .union
      if state.mode = .typedef then { state with mode := .tag, returnMode := .typedef }
      else state
  | some (.enum) =>
      let state := state.emitFrom start .enum
      if state.mode = .typedef then { state with mode := .tag, returnMode := .typedef }
      else state
  | some kind => state.emitFrom start kind
  | none => state.resolveIdentifier start name

private def annotationKeyword? (state : State) (allowPrefix : Bool) : Option (String × TokenKind) :=
  [ ("INVARIANT:", .invariant), ("INV:", .invariant),
    ("FNSPEC", .fnSpec), ("RELSPEC", .relSpec), ("MODIFIES:", .modifies),
    ("AUXUPD:", .auxUpd), ("GHOSTUPD:", .ghostUpd),
    ("END-SPEC:", .specEnd), ("SPEC:", .specBegin),
    ("DONT_TRANSLATE", .dontTranslate), ("CALLS", .calls),
    ("OWNED_BY", .ownedBy) ].find? fun (text, _) =>
      state.startsWith text &&
        (allowPrefix || text.endsWith ":" || !(state.peek? text.length).any fun character =>
          isIdentRest character || character = '\'')

private partial def State.skipLineComment (state : State) : State :=
  if state.atEnd then state
  else if state.startsWith "\r\n" || state.peek? = some '\n' then state.advanceNewline
  else skipLineComment state.advanceRaw

private partial def State.skipBlockComment (state : State) (left : SourcePos) : State :=
  if state.atEnd then
    state.errorAt left (state.position state.source.lineStart) "unclosed comment"
  else if state.startsWith "*/" then state.advance 2
  else if state.startsWith "\r\n" || state.peek? = some '\n' then
    skipBlockComment state.advanceNewline left
  else skipBlockComment state.advanceRaw left

private def escapedCharacter? (character : Char) : Option Char :=
  match character with
  | 'a' => some (Char.ofNat 7)
  | 'b' => some (Char.ofNat 8)
  | 'f' => some (Char.ofNat 12)
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | 'v' => some (Char.ofNat 11)
  | '\\' => some '\\'
  | '\'' => some '\''
  | '"' => some '"'
  | '?' => some '?'
  | _ => none

private partial def State.lexOrdinaryString (state : State) : State :=
  let start := state.index
  let original := state
  let state := state.advanceRaw
  let (state, characters, closed) := go state []
  if closed then
    state.emitOnePast start (.stringLiteral (String.ofList characters.reverse))
  else
    let state := original.advanceRaw
    if original.mode = .initial then
      state.error start state.index "ignoring bad character \""
    else
      state.error start state.index "Character \" can not follow typedef"
where
  go (state : State) (characters : List Char) : State × List Char × Bool :=
    match state.peek? with
    | none => (state, characters, false)
    | some '"' => (state.advanceRaw, characters, true)
    | some '\\' =>
        if state.peek? 1 = some '"' then
          go (state.advanceRaw 2) ('"' :: '\\' :: characters)
        else go state.advanceRaw ('\\' :: characters)
    | some character => go state.advanceRaw (character :: characters)

private partial def State.lexSpecialString (state : State) : State :=
  let left := state.position
  let state := state.advanceRaw
  let (state, characters, closed) := go state []
  if closed then
    { state.emitAt left (state.position state.index) (.stringLiteral (String.ofList characters.reverse)) with
      mode := .specialComment }
  else state
where
  go (state : State) (characters : List Char) : State × List Char × Bool :=
    if state.atEnd then (state, characters, false)
    else if state.peek? = some '"' then (state.advanceRaw, characters, true)
    else if state.startsWith "\\\"" then go (state.advanceRaw 2) ('"' :: characters)
    else if state.startsWith "\r\n" then
      go state.advanceNewline ('\n' :: '\r' :: characters)
    else match state.peek? with
      | some '\n' => go state.advanceNewline ('\n' :: characters)
      | some character => go state.advanceRaw (character :: characters)
      | none => (state, characters, false)

private def State.lexSpecialIdentifier (state : State) : State :=
  let start := state.index
  let (state, name) := state.takeWhile fun character => isIdentRest character || character = '\''
  state.emitFrom start (.ident (underscoreSafe name))

private def State.lexSpecialCommentStart (state : State) : State :=
  if state.startsWith "*/" then { state.advance 2 with mode := .initial }
  else match annotationKeyword? state true with
  | some (text, kind) =>
      { (state.advance text.length).emitFrom state.index kind with mode := .specialComment }
  | none =>
      if state.startsWith "\r\n" || state.peek? = some '\n' then state.advanceNewline
      else match state.peek? with
        | some ' ' | some '\t' => state.advanceRaw
        | some _ => { state.advanceRaw with mode := .specialCommentJunk }
        | none => state

private def State.lexSpecialCommentJunk (state : State) : State :=
  if state.startsWith "*/" then { state.advance 2 with mode := .initial }
  else if state.startsWith "\r\n" || state.peek? = some '\n' then state.advanceNewline
  else state.advanceRaw

private def State.lexSpecialComment (state : State) : State :=
  let start := state.index
  if state.startsWith "*/" then
    let state := state.advance 2
    { state.emitOnePast start .specBlockEnd with mode := .initial }
  else match annotationKeyword? state false with
  | some (text, kind) => (state.advance text.length).emitFrom start kind
  | none =>
      if state.startsWith "\r\n" || state.peek? = some '\n' then state.advanceNewline
      else match state.peek? with
        | some ' ' | some '\t' => state.advanceRaw
        | some '"' => state.lexSpecialString
        | some character =>
            if isIdentStart character then state.lexSpecialIdentifier
            else
              let state := state.advanceRaw
              let kind? := match character with
                | ':' => some .colon | ';' => some .semicolon
                | '[' => some .lbracket | ']' => some .rbracket
                | '*' => some .star | _ => none
              match kind? with
              | some kind => state.emitFrom start kind
              | none => state.error start state.index
                  s!"Illegal character ({character}) in special annotation"
        | none => state

private def State.emitCharValue (state : State) (value : Nat) : State :=
  let literal : NumericLiteral := { value, radix := .decimal, suffix := "" }
  state.emitFrom state.charLiteralStart (.numeric literal)

private def State.finishCharLiteral (state : State) : State :=
  let state := state.advanceRaw
  let returnMode := state.returnMode
  match state.charLiteralContent with
  | [value] =>
      match state.target.charLiteralConversion value with
      | .ok converted =>
          { state.emitCharValue converted.natAbs with mode := returnMode }
      | .error message =>
          { (state.error state.charLiteralStart state.index message).emitCharValue 0 with
            mode := returnMode }
  | _ =>
      { (state.error state.charLiteralStart state.index "Malformed character literal").emitCharValue 0 with
        mode := returnMode }

private def State.lexCharLiteral (state : State) : State :=
  if state.peek? = some '\'' then state.finishCharLiteral
  else if state.peek? != some '\\' then
    match state.peek? with
    | some character =>
        { state.advanceRaw with charLiteralContent := character.toNat :: state.charLiteralContent }
    | none => state
  else if (state.peek? 1).any fun character =>
      character = '\'' || character = '"' || character = '?' || character = '\\' ||
        character = 'a' || character = 'b' || character = 'f' || character = 'n' ||
        character = 'r' || character = 't' || character = 'v' then
    let value := (escapedCharacter? (state.peek? 1).get!).get!
    { state.advanceRaw 2 with charLiteralContent := value.toNat :: state.charLiteralContent }
  else if (state.peek? 1).any fun character => '0' ≤ character && character ≤ '7' then
    let finish := state.scanWhileFrom (state.index + 1) fun character =>
      '0' ≤ character && character ≤ '7'
    let value := parseDigits 8 (state.text (state.index + 1) finish)
    let next := { state.advanceRaw (finish - state.index) with
      charLiteralContent := value :: state.charLiteralContent }
    if value > Target.unsignedMax state.target.charWidth then
      next.error state.index (state.index + 1) "Character literal component too large!"
    else next
  else if state.peek? 1 = some 'x' && (state.peek? 2).any isHexDigit then
    let finish := state.scanWhileFrom (state.index + 2) isHexDigit
    let value := parseDigits 16 (state.text (state.index + 2) finish)
    let next := { state.advanceRaw (finish - state.index) with
      charLiteralContent := value :: state.charLiteralContent }
    if value > Target.unsignedMax state.target.charWidth then
      next.error state.index (state.index + 1) "Character literal component too large!"
    else next
  else
    let next := state.advanceRaw
    (next.error state.charLiteralStart next.index "Malformed character literal").emitCharValue 0

private def punctuators : List (String × TokenKind) :=
  [ (">>=", .rightShiftEq), ("<<=", .leftShiftEq),
    ("++", .plusPlus), ("--", .minusMinus), ("+=", .plusEq),
    ("-=", .minusEq), ("*=", .mulEq), ("|=", .bitOrEq),
    ("&=", .bitAndEq), ("/=", .divEq), ("%=", .modEq),
    ("^=", .bitXorEq), ("&&", .logicalAnd), ("||", .logicalOr),
    ("==", .equals), ("!=", .notEquals), ("->", .arrow),
    ("<<", .leftShift), (">>", .rightShift), ("<=", .lessEq),
    (">=", .greaterEq),
    ("*", .star), ("/", .slash), ("%", .mod), ("(", .lparen),
    (")", .rparen), ("{", .lcurly), ("}", .rcurly),
    ("[", .lbracket), ("]", .rbracket), (",", .comma),
    (";", .semicolon), (":", .colon), ("?", .question),
    ("=", .assign), (".", .dot), ("+", .plus), ("-", .minus),
    ("!", .not), ("&", .ampersand), ("~", .bitNot),
    ("|", .bitwiseOr), ("^", .bitwiseXor), ("<", .less), (">", .greater) ]

private def State.lexPunctuator (state : State) : Option State :=
  punctuators.find? (fun (text, _) => state.startsWith text) |>.map fun (text, kind) =>
    let start := state.index
    let advanced := state.advanceRaw text.length
    let bad := advanced.error start advanced.index s!"Character {text} can not follow typedef"
    match kind, state.mode with
    | .lparen, .tag => bad
    | .rparen, .tag => bad
    | .lcurly, .typedef => bad
    | .rcurly, .typedef => bad
    | .lparen, mode =>
        let next := advanced.emitFrom start kind
        if mode = .typedef || mode = .tagName then
          { next with typedefParenDepth := next.typedefParenDepth + 1 }
        else next
    | .rparen, mode =>
        let next := advanced.emitFrom start kind
        if mode = .typedef || mode = .tagName then
          { next with typedefParenDepth := next.typedefParenDepth - 1 }
        else next
    | .comma, mode =>
        let next := advanced.emitFrom start kind
        if (mode = .typedef || mode = .tag || mode = .tagName) &&
            next.typedefParenDepth = 0 then
          { next with typedefNameSeen := false }
        else next
    | .semicolon, mode =>
        let next := advanced.emitFrom start kind
        if mode = .typedef || mode = .tag || mode = .tagName then
          { next with mode := .initial, typedefNameSeen := false }
        else next
    | .lcurly, .initial =>
        let next := advanced.emitFrom start kind
        { next with typedefScopes := [] :: next.typedefScopes }
    | .lcurly, .tag | .lcurly, .tagName =>
        { advanced.emitFrom start kind with mode := .tagBody, tagBraceDepth := 1 }
    | .lcurly, .tagBody =>
        let next := advanced.emitFrom start kind
        { next with tagBraceDepth := next.tagBraceDepth + 1 }
    | .rcurly, .initial =>
        let next := advanced.emitFrom start kind
        { next with typedefScopes := next.typedefScopes.drop 1 }
    | .rcurly, .tagBody =>
        let next := advanced.emitFrom start kind
        if next.tagBraceDepth = 1 then
          { next with mode := .typedef, tagBraceDepth := 0 }
        else { next with tagBraceDepth := next.tagBraceDepth - 1 }
    | _, _ => advanced.emitFrom start kind

private partial def State.directiveLine? (state : State) : Option (Nat × Nat) :=
  go state.index
where
  go (index : Nat) : Option (Nat × Nat) :=
    match state.input[index]? with
    | none => none
    | some '\n' =>
        let bodyEnd := if index > state.index && state.input[index - 1]? = some '\r'
          then index - 1 else index
        some (bodyEnd, index + 1)
    | some _ => go (index + 1)

private def State.decimalIntegerEnd? (state : State) (start limit : Nat) : Option Nat :=
  if start >= limit then none
  else match state.input[start]? with
    | some '0' =>
        let finish := suffixEnd state (start + 1)
        if finish ≤ limit then some finish else none
    | some character =>
        if '1' ≤ character && character ≤ '9' then
          let digitsEnd := state.scanWhileFrom start isDigit
          let finish := suffixEnd state digitsEnd
          if finish ≤ limit then some finish else none
        else none
    | none => none

private def State.decimalIntegerValue (state : State) (start finish : Nat) : Nat :=
  let digitsEnd := min (state.scanWhileFrom start isDigit) finish
  parseDigits 10 (state.text start digitsEnd)

private partial def State.skipHorizontal (state : State) (start limit : Nat) : Nat :=
  go start
where
  go (index : Nat) : Nat :=
    if index < limit && (state.input[index]? = some ' ' || state.input[index]? = some '\t') then
      go (index + 1)
    else index

private partial def State.parseQuotedFile? (state : State) (start limit : Nat)
    (allowed : Char → Bool) : Option (String × Nat) :=
  if start >= limit || state.input[start]? != some '"' then none
  else
    let finish := go (start + 1)
    if finish > start + 1 && finish < limit && state.input[finish]? = some '"' then
      some (state.text (start + 1) finish, finish + 1)
    else none
where
  go (index : Nat) : Nat :=
    match state.input[index]? with
    | some character =>
        if index < limit && character != '"' && allowed character then go (index + 1)
        else index
    | none => index

private partial def State.parseGnuLineDirective? (state : State) (bodyEnd : Nat) : Option (String × Nat) :=
  let start := state.index
  if !state.startsWith "# " then none
  else do
    let numberEnd ← state.decimalIntegerEnd? (start + 2) bodyEnd
    if numberEnd >= bodyEnd || state.input[numberEnd]? != some ' ' then none
    let line := state.decimalIntegerValue (start + 2) numberEnd
    let (file, afterFile) ← state.parseQuotedFile? (numberEnd + 1) bodyEnd (fun _ => true)
    let rec consumeFlags (index : Nat) : Option Nat :=
      if index = bodyEnd then some index
      else if index < bodyEnd && state.input[index]? = some ' ' then do
        let finish ← state.decimalIntegerEnd? (index + 1) bodyEnd
        consumeFlags finish
      else none
    let _ ← consumeFlags afterFile
    some (file, line)

private def lineFileCharacter (character : Char) : Bool :=
  character = '-' || character = '_' || character = '.' || character = '<' ||
    character = '>' || character = '/' || character = ' ' || isAlpha character || isDigit character

private def State.parseLineDirective? (state : State) (bodyEnd : Nat) : Option (String × Nat) :=
  let start := state.index
  if !state.startsWith "#line" then none
  else do
    let numberStart := state.skipHorizontal (start + 5) bodyEnd
    if numberStart = start + 5 then none
    let numberEnd ← state.decimalIntegerEnd? numberStart bodyEnd
    let fileStart := state.skipHorizontal numberEnd bodyEnd
    if fileStart = numberEnd then none
    let (file, finish) ← state.parseQuotedFile? fileStart bodyEnd lineFileCharacter
    if state.skipHorizontal finish bodyEnd != bodyEnd then none
    some (file, state.decimalIntegerValue numberStart numberEnd)

private def State.lexDirective? (state : State) : Option State :=
  do
    let (bodyEnd, finish) ← state.directiveLine?
    if let some (file, line) := state.parseGnuLineDirective? bodyEnd then
      some { state with
        index := finish
        source := state.source.lineDirective (some file) line finish }
    else if let some (file, line) := state.parseLineDirective? bodyEnd then
      some { state with
        index := finish
        source := state.source.lineDirective (some file) line finish }
    else if state.startsWith "#pragma" then
      some { state with index := finish, source := state.source.newline finish }
    else none

private def State.atPhysicalLineStart (state : State) : Bool :=
  state.index = 0 || state.input[state.index - 1]? = some '\n'

private partial def loop (state : State) : State :=
  if state.atEnd then
    let position := state.position state.source.lineStart
    { state with tokens := state.tokens.push {
        value := .eof, region := Region.point position } }
  else match state.mode with
  | .specialCommentStart => loop state.lexSpecialCommentStart
  | .specialComment => loop state.lexSpecialComment
  | .specialCommentJunk => loop state.lexSpecialCommentJunk
  | .charLiteral => loop state.lexCharLiteral
  | _ =>
      match state.peek? with
      | some character =>
          if state.startsWith "\r\n" || character = '\n' then loop state.advanceNewline
          else if character = ' ' || character = '\t' then loop state.advanceRaw
          else if state.mode = .initial && state.startsWith "/**" then
            loop { state.advanceRaw 3 with mode := .specialCommentStart }
          else if state.startsWith "/*" then
            loop ((state.advanceRaw 2).skipBlockComment state.position)
          else if state.startsWith "//" then loop (state.advanceRaw 2 |>.skipLineComment)
          else if character = '#' && state.atPhysicalLineStart then
            match state.lexDirective? with
            | some next => loop next
            | none =>
                let next := state.advanceRaw
                if state.mode = .initial then
                  loop (next.error state.index next.index "ignoring bad character #")
                else
                  loop (next.error state.index next.index "Character # can not follow typedef")
          else if character = '"' then loop state.lexOrdinaryString
          else if character = '\'' then
            loop { state.advanceRaw with
              mode := .charLiteral, returnMode := state.mode,
              charLiteralContent := [], charLiteralStart := state.index }
          else if isDigit character then loop state.lexNumber
          else if isIdentStart character then loop state.lexIdentifier
          else match state.lexPunctuator with
            | some next => loop next
            | none =>
                let next := state.advanceRaw
                if state.mode = .initial then
                  loop (next.error state.index next.index s!"ignoring bad character {character}")
                else
                  loop (next.error state.index next.index
                    s!"Character {character} can not follow typedef")
      | none => loop state

def lex (target : Target) (file source : String) : Result :=
  let final := loop {
    input := source.toList.toArray
    source := { file }
    target }
  { tokens := final.tokens, diagnostics := final.diagnostics }

end Lexer

end Zag.Lang.AutoCorres.CParser
