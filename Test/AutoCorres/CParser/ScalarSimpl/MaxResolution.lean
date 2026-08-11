import Test.AutoCorres.CParser.ScalarSimpl.MaxCertificate

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

private def simpleProgram : ProgramAnalysis.Program := maxCertificate.program

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem max_fixture_resolves : (resolveIR simpleProgram "max").isOk := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem max_exact_resolution : (resolveFunction simpleProgram "max").toOption = some maxFunction :=
  by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
