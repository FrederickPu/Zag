import Lang.AutoCorres.CParser.Parser
import Test.AutoCorres.CParser.EmbeddedFixtures

/-!
# StrictC fixture smoke runner

This executable harness preprocesses and parses every C entry in the embedded
vendored corpus. Both phases and their fixture inputs remain filesystem-free.
-/

namespace Zag.Test.AutoCorres.CParser.FixtureSmoke

open Zag.Lang.AutoCorres.CParser

private def diagnosticText (diagnostic : Diagnostic) : String :=
  s!"{diagnostic.region.left.file}:{diagnostic.region.left.line}:" ++
    s!"{diagnostic.region.left.column}: {diagnostic.message}"

def main : IO Unit := do
  let mut checked := 0
  let mut failures : List String := []
  for name in EmbeddedFixtures.entries do
    checked := checked + 1
    let preprocessed := Preprocessor.preprocess EmbeddedFixtures.files name
    if !preprocessed.diagnostics.isEmpty then
      let diagnostics := preprocessed.diagnostics.toList.map diagnosticText
      failures := s!"{name} preprocessing:\n  {String.intercalate "\n  " diagnostics}" :: failures
    else
      let result := parseSource .arm name preprocessed.output
      if !result.isSuccess then
        let diagnostics := result.diagnostics.toList.map diagnosticText
        failures := s!"{name}:\n  {String.intercalate "\n  " diagnostics}" :: failures
  if failures.isEmpty && checked = 67 then
    IO.println s!"preprocessed and parsed all {checked} C fixtures"
  else if failures.isEmpty then
    throw <| IO.userError s!"expected 67 C fixtures, found {checked}"
  else
    throw <| IO.userError <|
      s!"{failures.length} fixture parses failed:\n{String.intercalate "\n" failures.reverse}"

end Zag.Test.AutoCorres.CParser.FixtureSmoke
