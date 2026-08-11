import Lang.AutoCorres.CParser.Preprocessor
import Lang.AutoCorres.CParser.ProgramAnalysis

/-! # Pure StrictC frontend -/

namespace Zag.Lang.AutoCorres.CParser.Frontend

open ProgramAnalysis

structure Result where
  program : Option Program
  diagnostics : Array Diagnostic
  parseFailure : Option Parser.Failure
  analysisError : Option AnalysisError
  preprocessedSource : String
  dependencies : Array String

namespace Result

def isSuccess (result : Result) : Bool :=
  result.program.isSome && !result.diagnostics.any (·.severity == .error) &&
    result.analysisError.isNone

end Result

/-- Lex, parse, and analyze an already preprocessed StrictC source string. -/
def analyzeSource (target : Target) (file source : String) : Result :=
  let parsed := CParser.parseSource target file source
  match parsed.value with
  | none => {
      program := none
      diagnostics := parsed.diagnostics
      parseFailure := parsed.failure
      analysisError := none
      preprocessedSource := source
      dependencies := #[] }
  | some translationUnit =>
      match ProgramAnalysis.analyze target translationUnit with
      | .ok program => {
          program := some program
          diagnostics := parsed.diagnostics
          parseFailure := parsed.failure
          analysisError := none
          preprocessedSource := source
          dependencies := #[] }
      | .error error => {
          program := none
          diagnostics := parsed.diagnostics
          parseFailure := parsed.failure
          analysisError := some error
          preprocessedSource := source
          dependencies := #[] }

/-- Preprocess an entry from an in-memory file map, then lex, parse, and analyze it. -/
def preprocessAndAnalyze (target : Target) (files : Preprocessor.FileMap)
    (entry : String) : Result :=
  let preprocessed := Preprocessor.preprocess files entry
  if preprocessed.diagnostics.any (·.severity == .error) then {
    program := none
    diagnostics := preprocessed.diagnostics
    parseFailure := none
    analysisError := none
    preprocessedSource := preprocessed.output
    dependencies := preprocessed.dependencies
  } else
    let result := analyzeSource target entry preprocessed.output
    { result with
      diagnostics := preprocessed.diagnostics ++ result.diagnostics
      dependencies := preprocessed.dependencies }

end Zag.Lang.AutoCorres.CParser.Frontend
