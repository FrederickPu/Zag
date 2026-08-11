import Test.AutoCorres.CParser.ScalarSimpl.Plus2Certificate

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

private def plus2Program : ProgramAnalysis.Program := plus2Certificate.program

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus2_fixture_resolves : (resolveIR plus2Program "plus2").isOk := by native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus2_exact_resolution :
    (resolveFunction plus2Program "plus2").toOption = some plus2 := by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
