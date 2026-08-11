import Test.AutoCorres.CParser.ScalarSimpl.Common
import Test.AutoCorres.CParser.EmbeddedFixtures

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

opaque plusCertifiedResult :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error
      (Certified .arm EmbeddedFixtures.files "examples/plus.c" "plus") :=
  certifyFrontend .arm EmbeddedFixtures.files "examples/plus.c" "plus"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus_fixture_certifies :
    plusCertifiedResult.isOk := by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
