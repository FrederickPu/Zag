import Test.AutoCorres.CParser.ScalarSimpl.MultByAddCertificate

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

private def multByAddProgram : ProgramAnalysis.Program := multByAddCertificate.program

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem mult_by_add_fixture_resolves : (resolveIR multByAddProgram "mult_by_add").isOk := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem mult_by_add_exact_resolution :
    (resolveFunction multByAddProgram "mult_by_add").toOption = some multByAdd := by
  native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
