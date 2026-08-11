import Test.AutoCorresPhases
import Test.AutoCorres.CParser.SemanticSmoke

def main : IO Unit := do
  Zag.Test.AutoCorres.CParser.FixtureSmoke.main
  Zag.Test.AutoCorres.CParser.SemanticSmoke.main
