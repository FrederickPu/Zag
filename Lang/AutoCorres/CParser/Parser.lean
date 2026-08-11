import Lang.AutoCorres.CParser.Parser.Grammar

/-!
# Public StrictC parser API
-/

namespace Zag.Lang.AutoCorres.CParser

abbrev TranslationUnit := Parser.TranslationUnit

structure Result (α : Type u) where
  value : Option α
  diagnostics : Array Diagnostic
  failure : Option Parser.Failure
deriving Repr

namespace Result

def isSuccess (result : Result α) : Bool := result.value.isSome

end Result

private def hasErrors (diagnostics : Array Diagnostic) : Bool :=
  diagnostics.any fun diagnostic => diagnostic.severity == .error

def parseTokens (tokens : Array Token) (diagnostics : Array Diagnostic := #[]) :
    Result TranslationUnit :=
  let parsed := Parser.runTokens Parser.parseTranslationUnit tokens diagnostics
  { value := if hasErrors parsed.state.diagnostics then none else parsed.value
    diagnostics := parsed.state.diagnostics
    failure := parsed.failure }

def parseSource (target : Target) (file source : String) : Result TranslationUnit :=
  let lexed := Lexer.lex target file source
  parseTokens lexed.tokens lexed.diagnostics

end Zag.Lang.AutoCorres.CParser
