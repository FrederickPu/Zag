import Lang.AutoCorres.CParser.Lexer
import Lang.AutoCorres.CParser.Parser.Name

/-!
# Pure parser core

Parser alternatives are transactional: a checkpoint includes input position,
diagnostics, dynamic C name scopes, and anonymous-name allocation.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

inductive NameClass where
  | ordinary
  | typedefName
deriving Repr, DecidableEq, Inhabited

structure NameBinding where
  name : String
  kind : NameClass
deriving Repr, DecidableEq, Inhabited

structure State where
  tokens : Array Token
  index : Nat := 0
  nameScopes : List (List NameBinding) := [[]]
  diagnostics : Array Diagnostic := #[]
  nextAnonymousStruct : Nat := 1
deriving Repr, Inhabited

structure Checkpoint where
  index : Nat
  nameScopes : List (List NameBinding)
  diagnosticCount : Nat
  nextAnonymousStruct : Nat
deriving Repr, Inhabited

structure Failure where
  region : Region
  message : String
deriving Repr, DecidableEq, Inhabited

inductive Result (α : Type u) where
  | success (value : α) (state : State)
  | failure (error : Failure) (state : State)
deriving Repr

abbrev Parser (α : Type u) := State → Result α

namespace State

def ofTokens (tokens : Array Token) (diagnostics : Array Diagnostic := #[]) : State :=
  { tokens, diagnostics }

def ofLexerResult (result : Lexer.Result) : State :=
  ofTokens result.tokens result.diagnostics

def checkpoint (state : State) : Checkpoint :=
  { index := state.index
    nameScopes := state.nameScopes
    diagnosticCount := state.diagnostics.size
    nextAnonymousStruct := state.nextAnonymousStruct }

def restore (state : State) (checkpoint : Checkpoint) : State :=
  { state with
    index := checkpoint.index
    nameScopes := checkpoint.nameScopes
    diagnostics := state.diagnostics.extract 0 checkpoint.diagnosticCount
    nextAnonymousStruct := checkpoint.nextAnonymousStruct }

def current? (state : State) : Option Token := state.tokens[state.index]?

def currentRegion (state : State) : Region :=
  match state.current? with
  | some token => token.region
  | none => state.tokens.back?.map (·.region) |>.getD Region.bogus

def atEnd (state : State) : Bool :=
  match state.current? with
  | none => true
  | some token => token.value == .eof

def advance (state : State) : State :=
  if state.index < state.tokens.size then { state with index := state.index + 1 } else state

def pushScope (state : State) : State := { state with nameScopes := [] :: state.nameScopes }

def popScope (state : State) : State :=
  match state.nameScopes with
  | _ :: outer@(_ :: _) => { state with nameScopes := outer }
  | _ => state

private def lookupInScope (name : String) : List NameBinding → Option NameClass
  | [] => none
  | binding :: bindings =>
      if binding.name = name then some binding.kind else lookupInScope name bindings

def lookupName (state : State) (name : String) : Option NameClass :=
  state.nameScopes.findSome? (lookupInScope name)

def bindName (state : State) (name : String) (kind : NameClass) : State :=
  let binding := { name, kind }
  match state.nameScopes with
  | [] => { state with nameScopes := [[binding]] }
  | scope :: scopes =>
      let scope := binding :: scope.filter (·.name != name)
      { state with nameScopes := scope :: scopes }

def addDiagnostic (state : State) (severity : Severity) (region : Region)
    (message : String) : State :=
  { state with diagnostics := state.diagnostics.push { severity, region, message } }

end State

instance : Monad Parser where
  pure value state := .success value state
  bind parser next state :=
    match parser state with
    | .success value state => next value state
    | .failure error state => .failure error state

def get : Parser State := fun state => .success state state

def set (next : State) : Parser Unit := fun _ => .success () next

def modify (update : State → State) : Parser Unit := fun state => .success () (update state)

def failAt (region : Region) (message : String) : Parser α :=
  fun state => .failure { region, message } state

def fail (message : String) : Parser α := fun state => failAt state.currentRegion message state

def diagnose (severity : Severity) (region : Region) (message : String) : Parser Unit :=
  modify fun state => state.addDiagnostic severity region message

def error (region : Region) (message : String) : Parser Unit := diagnose .error region message

def warning (region : Region) (message : String) : Parser Unit := diagnose .warning region message

def peek? : Parser (Option Token) := fun state => .success state.current? state

def anyToken : Parser Token := fun state =>
  match state.current? with
  | some token => .success token state.advance
  | none => .failure { region := state.currentRegion, message := "unexpected end of token stream" } state

def satisfy (description : String) (predicate : TokenKind → Bool) : Parser Token := fun state =>
  match state.current? with
  | some token =>
      if predicate token.value then .success token state.advance
      else .failure {
        region := token.region
        message := s!"expected {description}, found {reprStr token.value}" } state
  | none => .failure {
      region := state.currentRegion
      message := s!"expected {description}, found end of token stream" } state

def token (kind : TokenKind) : Parser Token :=
  satisfy (reprStr kind) (· == kind)

def rawIdentifier : Parser (Located String) := fun state =>
  match state.current? with
  | some { value := .ident name, region } | some { value := .typeIdent name, region } =>
      .success { value := name, region } state.advance
  | some found => .failure {
      region := found.region
      message := s!"expected identifier, found {reprStr found.value}" } state
  | none => .failure {
      region := state.currentRegion, message := "expected identifier, found end of token stream" } state

def identifier : Parser (Located String) := fun state =>
  match state.current? with
  | some { value := .ident name, region } =>
      .success { value := name, region } state.advance
  | some { value := .typeIdent name, region } =>
      .failure { region, message := s!"expected identifier, found typedef name {name}" } state
  | some found => .failure {
      region := found.region
      message := s!"expected identifier, found {reprStr found.value}" } state
  | none => .failure {
      region := state.currentRegion, message := "expected identifier, found end of token stream" } state

def typedefIdentifier : Parser (Located String) := fun state =>
  match state.current? with
  | some { value := .typeIdent name, region } =>
      .success { value := name, region } state.advance
  | some { value := .ident name, region } =>
      .failure { region, message := s!"expected typedef name, found identifier {name}" } state
  | some found => .failure {
      region := found.region
      message := s!"expected typedef name, found {reprStr found.value}" } state
  | none => .failure {
      region := state.currentRegion, message := "expected typedef name, found end of token stream" } state

def declareTypedef (name : String) : Parser Unit := modify (·.bindName name .typedefName)

def declareOrdinary (name : String) : Parser Unit := modify (·.bindName name .ordinary)

def pushScope : Parser Unit := modify State.pushScope

def popScope : Parser Unit := modify State.popScope

def checkpoint : Parser Checkpoint := fun state => .success state.checkpoint state

def restore (saved : Checkpoint) : Parser Unit := modify (·.restore saved)

def attempt (parser : Parser α) : Parser α := fun state =>
  let saved := state.checkpoint
  match parser state with
  | result@(.success _ _) => result
  | .failure failure failedState => .failure failure (failedState.restore saved)

def orElse (first second : Parser α) : Parser α := fun state =>
  let saved := state.checkpoint
  match first state with
  | result@(.success _ _) => result
  | result@(.failure _ failedState) =>
      if failedState.index = state.index then second (failedState.restore saved) else result

instance : OrElse (Parser α) where orElse first second := orElse first (second ())

def optional (parser : Parser α) : Parser (Option α) :=
  orElse (some <$> parser) (pure none)

partial def many (parser : Parser α) : Parser (List α) := fun state =>
  let saved := state.checkpoint
  match parser state with
  | .failure failure failedState =>
      if failedState.index = state.index then
        .success [] (failedState.restore saved)
      else
        .failure failure failedState
  | .success value next =>
      if next.index = state.index then
        .failure {
          region := state.currentRegion
          message := "repetition parser succeeded without consuming input" } next
      else
        match many parser next with
        | .success values finalState => .success (value :: values) finalState
        | .failure failure finalState => .failure failure finalState

def many1 (parser : Parser α) : Parser (List α) := do
  let first ← parser
  let rest ← many parser
  pure (first :: rest)

partial def sepBy1 (parser : Parser α) (separator : Parser β) : Parser (List α) := do
  let first ← parser
  let rest ← many (attempt (separator *> parser))
  pure (first :: rest)

def sepBy (parser : Parser α) (separator : Parser β) : Parser (List α) :=
  orElse (sepBy1 parser separator) (pure [])

def between (left : Parser α) (right : Parser β) (parser : Parser γ) : Parser γ :=
  left *> parser <* right

def inScope (parser : Parser α) : Parser α := fun state =>
  let outerScopes := state.nameScopes
  match parser state.pushScope with
  | .success value state => .success value { state with nameScopes := outerScopes }
  | .failure failure state => .failure failure { state with nameScopes := outerScopes }

structure ParseOutput (α : Type u) where
  value : Option α
  failure : Option Failure
  state : State
deriving Repr

def run (parser : Parser α) (state : State) : ParseOutput α :=
  match parser state with
  | .success value state => { value := some value, failure := none, state }
  | .failure failure state =>
      let state := state.addDiagnostic .error failure.region failure.message
      { value := none, failure := some failure, state }

def runTokens (parser : Parser α) (tokens : Array Token)
    (diagnostics : Array Diagnostic := #[]) : ParseOutput α :=
  run parser (State.ofTokens tokens diagnostics)

def runSource (target : Target) (file source : String) (parser : Parser α) : ParseOutput α :=
  run parser (State.ofLexerResult (Lexer.lex target file source))

end Zag.Lang.AutoCorres.CParser.Parser
