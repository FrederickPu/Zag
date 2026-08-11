import Lang.AutoCorres.CParser.Source

/-!
# Pure C preprocessor

The implementation is intentionally limited to the preprocessing language used
by the vendored AutoCorres C corpus.  It preserves comments (the equivalent of
`-CC`) and reports every unsupported active directive instead of silently
discarding it.
-/

namespace Zag.Lang.AutoCorres.CParser.Preprocessor

structure File where
  name : String
  source : String
deriving Repr, DecidableEq, Inhabited

inductive Macro where
  | object (replacement : String)
  | function (parameters : List String) (variadic : Option String)
      (replacement : String)
deriving Repr, DecidableEq, Inhabited

abbrev FileMap := List File
abbrev MacroEnv := List (String × Macro)

structure Result where
  output : String
  diagnostics : Array Diagnostic
  dependencies : Array String
  macros : MacroEnv
deriving Repr, Inhabited

private inductive TokenKind where
  | identifier
  | ppNumber
  | whitespace
  | newline
  | comment
  | stringLiteral
  | charLiteral
  | other
deriving Repr, DecidableEq, Inhabited

private structure Token where
  kind : TokenKind
  text : String
  line : Nat
  offset : Nat
  hide : List String := []
deriving Repr, Inhabited

private structure Spliced where
  characters : Array Char
  lines : Array Nat
deriving Inhabited

private def isIdentStart (character : Char) : Bool :=
  character.isAlpha || character = '_'

private def isIdentRest (character : Char) : Bool :=
  isIdentStart character || character.isDigit

private partial def spliceGo (input : Array Char) (index line : Nat)
    (characters : Array Char) (lines : Array Nat) : Spliced :=
  if index >= input.size then
    { characters, lines }
  else if input[index]? = some '\\' && input[index + 1]? = some '\n' then
    spliceGo input (index + 2) (line + 1) characters lines
  else if input[index]? = some '\\' && input[index + 1]? = some '\r' &&
      input[index + 2]? = some '\n' then
    spliceGo input (index + 3) (line + 1) characters lines
  else
    let character := input[index]!
    spliceGo input (index + 1) (if character = '\n' then line + 1 else line)
      (characters.push character) (lines.push line)

private def splice (source : String) : Spliced :=
  spliceGo source.toList.toArray 0 1 #[] #[]

private def arrayText (input : Array Char) (start finish : Nat) : String :=
  String.ofList (input.toList.drop start |>.take (finish - start))

private partial def scanWhile (input : Array Char) (index : Nat)
    (predicate : Char → Bool) : Nat :=
  match input[index]? with
  | some character => if predicate character then scanWhile input (index + 1) predicate else index
  | none => index

private partial def scanPpNumber (input : Array Char) (index : Nat) (previous : Char) : Nat :=
  match input[index]? with
  | none => index
  | some character =>
      if isIdentRest character || character = '.' then
        scanPpNumber input (index + 1) character
      else if (character = '+' || character = '-') &&
          (previous = 'e' || previous = 'E' || previous = 'p' || previous = 'P') then
        scanPpNumber input (index + 1) character
      else index

private partial def scanQuoted (input : Array Char) (index : Nat) (quote : Char) : Nat × Bool :=
  match input[index]? with
  | none => (index, false)
  | some '\n' => (index, false)
  | some character =>
      if character = quote then (index + 1, true)
      else if character = '\\' && index + 1 < input.size then
        scanQuoted input (index + 2) quote
      else scanQuoted input (index + 1) quote

private partial def scanLineComment (input : Array Char) (index : Nat) : Nat :=
  match input[index]? with
  | some '\n' | none => index
  | some _ => scanLineComment input (index + 1)

private partial def scanBlockChunk (input : Array Char) (index : Nat) : Nat × Bool × Bool :=
  if index >= input.size then (index, false, false)
  else if input[index]? = some '\n' then (index, false, true)
  else if input[index]? = some '*' && input[index + 1]? = some '/' then
    (index + 2, true, false)
  else scanBlockChunk input (index + 1)

private def pointDiagnostic (file : String) (line offset : Nat)
    (message : String) : Diagnostic :=
  let position : SourcePos :=
    { file, line := Int.ofNat line, column := 0, offset }
  { severity := .error, region := Region.point position, message }

private partial def tokenizeGo (file : String) (spliced : Spliced) (index : Nat)
    (inBlock : Bool) (tokens : Array Token) (diagnostics : Array Diagnostic) :
    Array Token × Array Diagnostic :=
  if index >= spliced.characters.size then
    let diagnostics := if inBlock then
      diagnostics.push (pointDiagnostic file (spliced.lines.back?.getD 1) index
        "unterminated block comment")
    else diagnostics
    (tokens, diagnostics)
  else
    let line := spliced.lines[index]!
    if inBlock then
      let (finish, closed, atNewline) := scanBlockChunk spliced.characters index
      let tokens := if finish > index then tokens.push {
          kind := .comment, text := arrayText spliced.characters index finish,
          line, offset := index }
        else tokens
      if closed then tokenizeGo file spliced finish false tokens diagnostics
      else if atNewline then
        let token : Token := { kind := .newline, text := "\n", line, offset := finish }
        tokenizeGo file spliced (finish + 1) true (tokens.push token) diagnostics
      else tokenizeGo file spliced finish true tokens diagnostics
    else
      let character := spliced.characters[index]!
      if character = '\n' then
        tokenizeGo file spliced (index + 1) false
          (tokens.push { kind := .newline, text := "\n", line, offset := index }) diagnostics
      else if character = ' ' || character = '\t' || character = '\r' ||
          character = '\x0b' || character = '\x0c' then
        let finish := scanWhile spliced.characters index fun current =>
          current = ' ' || current = '\t' || current = '\r' ||
            current = '\x0b' || current = '\x0c'
        tokenizeGo file spliced finish false (tokens.push {
          kind := .whitespace, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics
      else if character = '/' && spliced.characters[index + 1]? = some '/' then
        let finish := scanLineComment spliced.characters (index + 2)
        tokenizeGo file spliced finish false (tokens.push {
          kind := .comment, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics
      else if character = '/' && spliced.characters[index + 1]? = some '*' then
        let (finish, closed, atNewline) := scanBlockChunk spliced.characters (index + 2)
        let tokens := tokens.push {
          kind := .comment, text := arrayText spliced.characters index finish,
          line, offset := index }
        if closed then tokenizeGo file spliced finish false tokens diagnostics
        else if atNewline then
          let newline : Token := { kind := .newline, text := "\n", line, offset := finish }
          tokenizeGo file spliced (finish + 1) true (tokens.push newline) diagnostics
        else tokenizeGo file spliced finish true tokens diagnostics
      else if character = '"' || character = '\'' then
        let (finish, closed) := scanQuoted spliced.characters (index + 1) character
        let kind := if character = '"' then TokenKind.stringLiteral else TokenKind.charLiteral
        let diagnostics := if closed then diagnostics else
          diagnostics.push (pointDiagnostic file line index
            (if character = '"' then "unterminated string literal" else
              "unterminated character literal"))
        tokenizeGo file spliced finish false (tokens.push {
          kind, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics
      else if isIdentStart character then
        let finish := scanWhile spliced.characters (index + 1) isIdentRest
        tokenizeGo file spliced finish false (tokens.push {
          kind := .identifier, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics
      else if character.isDigit || (character = '.' &&
          (spliced.characters[index + 1]?).any Char.isDigit) then
        let finish := scanPpNumber spliced.characters (index + 1) character
        tokenizeGo file spliced finish false (tokens.push {
          kind := .ppNumber, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics
      else
        let finish := if character = '.' && spliced.characters[index + 1]? = some '.' &&
            spliced.characters[index + 2]? = some '.' then index + 3 else index + 1
        tokenizeGo file spliced finish false (tokens.push {
          kind := .other, text := arrayText spliced.characters index finish,
          line, offset := index }) diagnostics

private def tokenize (file source : String) : Array Token × Array Diagnostic :=
  tokenizeGo file (splice source) 0 false #[] #[]

private def isTrivia (token : Token) : Bool :=
  token.kind = .whitespace || token.kind = .comment

private def skipTrivia : List Token → List Token
  | token :: tokens => if isTrivia token then skipTrivia tokens else token :: tokens
  | [] => []

private def trimTrivia (tokens : List Token) : List Token :=
  (skipTrivia (skipTrivia tokens).reverse).reverse

private def skipWhitespace : List Token → List Token
  | token :: tokens => if token.kind = .whitespace then skipWhitespace tokens else token :: tokens
  | [] => []

private def trimWhitespace (tokens : List Token) : List Token :=
  (skipWhitespace (skipWhitespace tokens).reverse).reverse

private def skipInvocationWhitespace : List Token → List Token
  | token :: tokens =>
      if token.kind = .whitespace || token.kind = .newline then
        skipInvocationWhitespace tokens
      else token :: tokens
  | [] => []

private def tokenText (tokens : List Token) : String :=
  tokens.foldl (fun text token => text ++ token.text) ""

private def hasName (names : List String) (name : String) : Bool :=
  names.any (· = name)

private def addName (names : List String) (name : String) : List String :=
  if hasName names name then names else name :: names

private def mergeNames (left right : List String) : List String :=
  right.foldl addName left

private def Token.hideWith (token : Token) (names : List String) : Token :=
  { token with hide := mergeNames token.hide names }

private def Token.forMacroReplacement (token : Token) : Token :=
  if token.kind = .comment && token.text.startsWith "//" then
    { token with text := "/*" ++ String.ofList (token.text.toList.drop 2) ++ "*/" }
  else token

private def tokenizeReplacement (source : String) : Array Token × Array Diagnostic :=
  let (tokens, diagnostics) := tokenize "<macro>" source
  (tokens.map (·.forMacroReplacement), diagnostics)

private def lookupMacro? (macros : MacroEnv) (name : String) : Option Macro :=
  (macros.find? fun entry => entry.1 = name).map (·.2)

private def defineMacro (macros : MacroEnv) (name : String) (value : Macro) : MacroEnv :=
  (name, value) :: macros.filter (fun entry => entry.1 != name)

private structure Invocation where
  arguments : List (List Token)
  after : List Token

private partial def parseInvocationGo (tokens : List Token) (depth : Nat)
    (current : List Token) (arguments : List (List Token)) : Option Invocation :=
  match tokens with
  | [] => none
  | token :: rest =>
      if token.kind = .other && token.text = "(" then
        parseInvocationGo rest (depth + 1) (token :: current) arguments
      else if token.kind = .other && token.text = ")" then
        if depth = 0 then
          let arguments := if arguments.isEmpty && (skipTrivia current).isEmpty then []
            else arguments.reverse ++ [current.reverse]
          some { arguments, after := rest }
        else parseInvocationGo rest (depth - 1) (token :: current) arguments
      else if token.kind = .other && token.text = "," && depth = 0 then
        parseInvocationGo rest depth [] (current.reverse :: arguments)
      else parseInvocationGo rest depth (token :: current) arguments

private def parseInvocation? (tokens : List Token) : Option Invocation :=
  -- With `-CC`, a retained comment is a real token and prevents this from
  -- being a function-like invocation; ordinary whitespace does not.
  match skipInvocationWhitespace tokens with
  | token :: rest =>
      if token.kind = .other && token.text = "(" then parseInvocationGo rest 0 [] [] else none
  | [] => none

private def commaToken (line offset : Nat) : Token :=
  { kind := .other, text := ",", line, offset }

private def joinArguments (arguments : List (List Token)) (line offset : Nat) : List Token :=
  match arguments with
  | [] => []
  | argument :: rest => rest.foldl
      (fun result next => result ++ commaToken line offset :: next) argument

private def substitute (replacement : List Token)
    (bindings : List (String × List Token)) (hide : List String) : List Token :=
  replacement.flatMap fun token =>
    if token.kind != .identifier then [token.hideWith hide]
    else match bindings.find? fun binding => binding.1 = token.text with
      | some binding => binding.2.map (fun argument => argument.hideWith (mergeNames token.hide hide))
      | none => [token.hideWith hide]

private structure Expansion where
  tokens : List Token
  errors : List (Token × String) := []
deriving Inhabited

mutual
private def expandTokens (macros : MacroEnv) (input : List Token) : Option Expansion :=
  expandTokensGo macros input [] []
partial_fixpoint

private def expandTokensGo (macros : MacroEnv) (tokens : List Token) (output : List Token)
    (errors : List (Token × String)) : Option Expansion :=
  match tokens with
  | [] => some { tokens := output.reverse, errors := errors.reverse }
  | token :: rest =>
      if token.kind != .identifier || hasName token.hide token.text then
        expandTokensGo macros rest (token :: output) errors
      else match lookupMacro? macros token.text with
        | none => expandTokensGo macros rest (token :: output) errors
        | some (.object replacement) =>
            let (replacement, lexDiagnostics) := tokenizeReplacement replacement
            let hide := addName token.hide token.text
            let errors := lexDiagnostics.toList.foldl
              (fun errors diagnostic => (token, diagnostic.message) :: errors) errors
            expandTokensGo macros
              (replacement.toList.map (fun replacementToken => replacementToken.hideWith hide) ++ rest)
              output errors
        | some (.function parameters variadic replacement) =>
            match parseInvocation? rest with
            | none => expandTokensGo macros rest (token :: output) errors
            | some invocation =>
                let arguments := if invocation.arguments.isEmpty && !parameters.isEmpty then [[]]
                  else invocation.arguments
                let required := parameters.length
                let valid := if variadic.isSome then arguments.length >= required
                  else arguments.length = required
                if !valid then
                  let expected := if variadic.isSome then s!"at least {required}" else s!"{required}"
                  expandTokensGo macros rest (token :: output)
                    ((token, s!"macro '{token.text}' expects {expected} arguments, got {arguments.length}") :: errors)
                else
                  do
                    let fixedExpansions ← (arguments.take required).mapM (expandTokens macros)
                    let bindings := parameters.zip (fixedExpansions.map (·.tokens))
                    let errors := fixedExpansions.foldl
                      (fun errors expansion => expansion.errors.reverse ++ errors) errors
                    match variadic with
                      | none =>
                          expandSubstituted macros replacement token invocation.after bindings
                            output errors
                      | some name => do
                          let raw := joinArguments (arguments.drop required) token.line token.offset
                          let expanded ← expandTokens macros raw
                          expandSubstituted macros replacement token invocation.after
                            ((name, expanded.tokens) :: bindings) output
                            (expanded.errors.reverse ++ errors)
partial_fixpoint

private def expandSubstituted (macros : MacroEnv) (source : String) (token : Token)
    (after : List Token) (bindings : List (String × List Token)) (output : List Token)
    (errors : List (Token × String)) : Option Expansion :=
  let (replacement, lexDiagnostics) := tokenizeReplacement source
  let errors := lexDiagnostics.toList.foldl
    (fun errors (diagnostic : Diagnostic) => (token, diagnostic.message) :: errors) errors
  let hide := addName token.hide token.text
  let result := substitute replacement.toList bindings hide
  expandTokensGo macros (result ++ after) output errors
partial_fixpoint
end

private def splitLines (tokens : List Token) : List (List Token) :=
  go tokens [] []
where
  go (tokens : List Token) (line : List Token) (lines : List (List Token)) : List (List Token) :=
    match tokens with
    | [] => if line.isEmpty then lines.reverse else (line.reverse :: lines).reverse
    | token :: rest =>
        if token.kind = .newline then go rest [] ((token :: line).reverse :: lines)
        else go rest (token :: line) lines

private def lineBody (line : List Token) : List Token :=
  match line.reverse with
  | token :: rest => if token.kind = .newline then rest.reverse else line
  | [] => []

private def lineEnding (line : List Token) : String :=
  match line.reverse with
  | token :: _ => if token.kind = .newline then token.text else ""
  | [] => ""

private def lineAfter (line : List Token) (fallback : Nat) : Nat :=
  match line.reverse with
  | token :: _ => if token.kind = .newline then token.line + 1 else fallback + 1
  | [] => fallback + 1

private structure Directive where
  name : String
  arguments : List Token
  token : Token

private def directive? (line : List Token) : Option Directive :=
  match skipTrivia (lineBody line) with
  | hash :: rest =>
      if hash.kind != .other || hash.text != "#" then none
      else match skipTrivia rest with
        | name :: arguments =>
            if name.kind = .identifier then some { name := name.text, arguments, token := name }
            else some { name := "", arguments := name :: arguments, token := hash }
        | [] => some { name := "", arguments := [], token := hash }
  | [] => none

private structure Conditional where
  parentActive : Bool
  branchActive : Bool

private def conditionActive : List Conditional → Bool
  | frame :: _ => frame.parentActive && frame.branchActive
  | [] => true

private structure Engine where
  files : FileMap
  macros : MacroEnv
  diagnostics : Array Diagnostic := #[]
  dependencies : Array String := #[]
  onceFiles : List String := []
  includeStack : List String := []
  output : Array String := #[]
  pending : List Token := []

private def Engine.diagnose (engine : Engine) (file : String) (token : Token)
    (message : String) : Engine :=
  let diagnostic := pointDiagnostic file token.line token.offset message
  { engine with diagnostics := engine.diagnostics.push diagnostic }

private def Engine.emit (engine : Engine) (text : String) : Engine :=
  if text.isEmpty then engine else { engine with output := engine.output.push text }

private def Engine.ensureNewline (engine : Engine) : Engine :=
  match engine.output.back? with
  | some text => if text.endsWith "\n" then engine else engine.emit "\n"
  | none => engine

private def Engine.flush (engine : Engine) (file : String) : Engine :=
  if engine.pending.isEmpty then engine
  else match expandTokens engine.macros engine.pending with
    | none =>
        let engine := engine.diagnose file engine.pending.head!
          "macro expansion did not terminate"
        { engine with pending := [] }
    | some expansion =>
        let engine := expansion.errors.foldl (fun engine error =>
          engine.diagnose file error.1 error.2) engine
        { (engine.emit (tokenText expansion.tokens)) with pending := [] }

private def Engine.addDependency (engine : Engine) (file : String) : Engine :=
  if engine.dependencies.contains file then engine
  else { engine with dependencies := engine.dependencies.push file }

private def splitPath (path : String) : List String :=
  go path.toList [] []
where
  go (characters : List Char) (part : List Char) (parts : List String) : List String :=
    match characters with
    | [] => (String.ofList part.reverse :: parts).reverse
    | '/' :: rest => go rest [] (String.ofList part.reverse :: parts)
    | character :: rest => go rest (character :: part) parts

private def normalizePath (path : String) : String :=
  let path := String.ofList (path.toList.map fun character => if character = '\\' then '/' else character)
  let normalized := (splitPath path).foldl (fun result part =>
    if part.isEmpty || part = "." then result
    else if part = ".." then result.drop 1
    else part :: result) [] |>.reverse
  String.intercalate "/" normalized

private def directory (file : String) : String :=
  match (splitPath file).reverse with
  | [] | [_] => ""
  | _ :: rest => String.intercalate "/" rest.reverse

private def resolveInclude (sourceFile included : String) : String :=
  normalizePath (if (directory sourceFile).isEmpty then included
    else directory sourceFile ++ "/" ++ included)

private def lookupFile? (files : FileMap) (name : String) : Option String :=
  (files.find? fun file => file.name = name).map (·.source)

private def quoteMarkerFile (file : String) : String :=
  file.toList.foldl (fun result character =>
    if character = '\\' then result ++ "\\\\"
    else if character = '"' then result ++ "\\\""
    else result.push character) ""

private def lineMarker (line : Nat) (file : String) (flag : Nat) : String :=
  s!"# {line} \"{quoteMarkerFile file}\" {flag}\n"

private def parseQuotedInclude? (tokens : List Token) : Option String :=
  match skipTrivia tokens with
  | token :: rest =>
      if token.kind != .stringLiteral || !(skipTrivia rest).isEmpty || token.text.length < 2 then none
      else some (String.ofList (token.text.toList.drop 1 |>.take (token.text.length - 2)))
  | [] => none

private def parseConditionName? (tokens : List Token) : Option String :=
  match skipTrivia tokens with
  | token :: rest =>
      if token.kind = .identifier && (skipTrivia rest).isEmpty then some token.text else none
  | [] => none

private partial def parseParameters (tokens : List Token) :
    Except String (List String × Option String × List Token) :=
  go (skipTrivia tokens) []
where
  go (tokens : List Token) (parameters : List String) :
      Except String (List String × Option String × List Token) :=
    match tokens with
    | [] => .error "unterminated function-like macro parameter list"
    | token :: rest =>
        if token.kind = .other && token.text = ")" then
          .ok (parameters.reverse, none, rest)
        else if token.kind != .identifier then
          .error "expected a macro parameter name"
        else
          let name := token.text
          match skipTrivia rest with
          | ellipsis :: afterEllipsis =>
              if ellipsis.kind = .other && ellipsis.text = "..." then
                match skipTrivia afterEllipsis with
                | close :: replacement =>
                    if close.kind = .other && close.text = ")" then
                      .ok (parameters.reverse, some name, replacement)
                    else .error "GNU named variadic parameter must be last"
                | [] => .error "unterminated GNU named variadic parameter"
              else if ellipsis.kind = .other && ellipsis.text = ")" then
                .ok ((name :: parameters).reverse, none, afterEllipsis)
              else if ellipsis.kind = .other && ellipsis.text = "," then
                go (skipTrivia afterEllipsis) (name :: parameters)
              else .error "expected ',' or ')' after macro parameter"
          | [] => .error "unterminated function-like macro parameter list"

private def hasMacroOperator (tokens : List Token) : Bool :=
  tokens.any fun token => token.kind = .other && token.text = "#"

private def parseDefinition (arguments : List Token) : Except String (String × Macro) := do
  let tokens := skipTrivia arguments
  let nameToken ← match tokens with
    | token :: _ => if token.kind = .identifier then .ok token else .error "expected macro name"
    | [] => .error "expected macro name"
  let rest := tokens.drop 1
  match rest with
  | opener :: afterOpen =>
      if opener.kind = .other && opener.text = "(" &&
          opener.offset = nameToken.offset + nameToken.text.length then
        let (parameters, variadic, replacement) ← parseParameters afterOpen
        let replacement := trimWhitespace replacement
        if hasMacroOperator replacement then
          .error "macro stringification and token pasting are unsupported"
        else .ok (nameToken.text, .function parameters variadic (tokenText replacement))
      else
        let replacement := trimWhitespace rest
        if hasMacroOperator replacement then
          .error "macro stringification and token pasting are unsupported"
        else .ok (nameToken.text, .object (tokenText replacement))
  | [] => .ok (nameToken.text, .object "")

private partial def processFile (engine : Engine) (file : String) : Engine :=
  if hasName engine.onceFiles file then engine
  else if hasName engine.includeStack file then
    let token : Token := { kind := .other, text := "", line := 1, offset := 0 }
    engine.diagnose file token s!"recursive include of '{file}'"
  else match lookupFile? engine.files file with
  | none =>
      let token : Token := { kind := .other, text := "", line := 1, offset := 0 }
      engine.diagnose file token s!"source file not found: '{file}'"
  | some source =>
      let (tokens, lexicalDiagnostics) := tokenize file source
      let engine := { engine with
        diagnostics := engine.diagnostics ++ lexicalDiagnostics
        includeStack := file :: engine.includeStack }
      let engine := processLines engine file (splitLines tokens.toList) []
      { engine with includeStack := engine.includeStack.drop 1 }
where
  processLines (engine : Engine) (file : String) (lines : List (List Token))
      (conditionals : List Conditional) : Engine :=
    match lines with
    | [] =>
        let engine := engine.flush file
        match conditionals with
        | [] => engine
        | _ =>
            let token : Token := { kind := .other, text := "", line := 1, offset := 0 }
            engine.diagnose file token "unterminated conditional directive"
    | line :: rest =>
        match directive? line with
        | none =>
            if conditionActive conditionals then
              processLines { engine with pending := engine.pending ++ line } file rest conditionals
            else processLines (engine.emit (lineEnding line)) file rest conditionals
        | some directive =>
            let engine := engine.flush file
            let active := conditionActive conditionals
            match directive.name with
            | "ifdef" | "ifndef" =>
                match parseConditionName? directive.arguments with
                | none =>
                    let engine := if active then engine.diagnose file directive.token
                      s!"malformed #{directive.name}" else engine
                    let frame := { parentActive := active, branchActive := false }
                    processLines (engine.emit (lineEnding line)) file rest (frame :: conditionals)
                | some name =>
                    let defined := (lookupMacro? engine.macros name).isSome
                    let branch := if directive.name = "ifdef" then defined else !defined
                    let frame := { parentActive := active, branchActive := branch }
                    processLines (engine.emit (lineEnding line)) file rest (frame :: conditionals)
            | "endif" =>
                match conditionals with
                | [] =>
                    let engine := if active then engine.diagnose file directive.token
                      "#endif without matching #ifdef or #ifndef" else engine
                    processLines (engine.emit (lineEnding line)) file rest []
                | _ :: outer => processLines (engine.emit (lineEnding line)) file rest outer
            | "else" | "elif" =>
                let relevant := match conditionals with
                  | frame :: _ => frame.parentActive
                  | [] => true
                let engine := if relevant then engine.diagnose file directive.token
                    s!"unsupported active directive: #{directive.name}"
                  else engine
                processLines (engine.emit (lineEnding line)) file rest conditionals
            | "define" =>
                if !active then processLines (engine.emit (lineEnding line)) file rest conditionals
                else match parseDefinition directive.arguments with
                | .error message =>
                    processLines ((engine.diagnose file directive.token message).emit (lineEnding line))
                      file rest conditionals
                | .ok (name, value) =>
                    let engine := { engine with macros := defineMacro engine.macros name value }
                    processLines (engine.emit (lineEnding line)) file rest conditionals
            | "include" =>
                if !active then processLines (engine.emit (lineEnding line)) file rest conditionals
                else match parseQuotedInclude? directive.arguments with
                | none =>
                    let engine := engine.diagnose file directive.token
                      "only #include \"...\" is supported in active branches"
                    processLines (engine.emit (lineEnding line)) file rest conditionals
                | some included =>
                    let resolved := resolveInclude file included
                    let engine := engine.addDependency resolved
                    if (lookupFile? engine.files resolved).isNone then
                      let engine := engine.diagnose file directive.token
                        s!"included source file not found: '{resolved}'"
                      processLines (engine.emit (lineEnding line)) file rest conditionals
                    else if hasName engine.onceFiles resolved then
                      processLines (engine.emit (lineEnding line)) file rest conditionals
                    else
                      let engine := engine.emit (lineMarker 1 resolved 1)
                      let engine := processFile engine resolved
                      let nextLine := lineAfter line directive.token.line
                      let engine := engine.ensureNewline.emit (lineMarker nextLine file 2)
                      processLines engine file rest conditionals
            | "pragma" =>
                if !active then processLines (engine.emit (lineEnding line)) file rest conditionals
                else
                  let arguments := tokenText (trimTrivia (skipTrivia directive.arguments))
                  if arguments = "once" then
                    let onceFiles := addName engine.onceFiles file
                    processLines ({ engine with onceFiles }.emit (lineEnding line)) file rest conditionals
                  else
                    let engine := engine.diagnose file directive.token
                      s!"unsupported active directive: #pragma {arguments}"
                    processLines (engine.emit (lineEnding line)) file rest conditionals
            | name =>
                if !active then processLines (engine.emit (lineEnding line)) file rest conditionals
                else
                  let display := if name.isEmpty then "#" else "#" ++ name
                  let engine := engine.diagnose file directive.token
                    s!"unsupported active directive: {display}"
                  processLines (engine.emit (lineEnding line)) file rest conditionals

/--
Preprocess `entry` from an immutable normalized filename/source map.  Quoted
includes are resolved relative to the including filename; no filesystem access
or ambient include path is used.
-/
def preprocess (files : FileMap) (entry : String) (initialMacros : MacroEnv := []) : Result :=
  let normalizedFiles := files.map fun file => { file with name := normalizePath file.name }
  let entry := normalizePath entry
  let engine := processFile { files := normalizedFiles, macros := initialMacros } entry |>.flush entry
  { output := engine.output.toList.foldl (· ++ ·) ""
    diagnostics := engine.diagnostics
    dependencies := engine.dependencies
    macros := engine.macros }

end Zag.Lang.AutoCorres.CParser.Preprocessor
