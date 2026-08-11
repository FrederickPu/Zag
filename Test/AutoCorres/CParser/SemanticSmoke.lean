import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures

/-! # Embedded StrictC fixture semantic-analysis runner -/

namespace Zag.Test.AutoCorres.CParser.SemanticSmoke

open Zag.Lang.AutoCorres.CParser

def main : IO Unit := do
  let mut checked := 0
  let mut failures : List String := []
  for name in EmbeddedFixtures.entries do
    let result := Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files name
    if result.isSuccess then checked := checked + 1
    else if let some error := result.analysisError then
      failures := s!"{name}: {reprStr error}" :: failures
    else
      failures := s!"{name}: preprocessing or parsing failed" :: failures
  if failures.isEmpty && checked = 67 then
    IO.println s!"semantically analyzed all {checked} C fixtures"
  else if failures.isEmpty then
    throw <| IO.userError s!"expected 67 C fixtures, analyzed {checked}"
  else
    throw <| IO.userError <|
      s!"{failures.length} fixture analyses failed:\n{String.intercalate "\n" failures.reverse}"

end Zag.Test.AutoCorres.CParser.SemanticSmoke
