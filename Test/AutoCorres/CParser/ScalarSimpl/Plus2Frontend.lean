import Test.AutoCorres.CParser.ScalarSimpl.Common
import Test.AutoCorres.CParser.EmbeddedFixtures

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

opaque plus2CertifiedResult :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error
      (Certified .arm EmbeddedFixtures.files "examples/plus.c" "plus2") :=
  certifyFrontend .arm EmbeddedFixtures.files "examples/plus.c" "plus2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem plus2_fixture_certifies : plus2CertifiedResult.isOk := by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
