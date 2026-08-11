import Test.AutoCorres.CParser.ScalarSimpl.Common
import Test.AutoCorres.CParser.EmbeddedFixtures

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

opaque multByAddCertifiedResult :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error
      (Certified .arm EmbeddedFixtures.files "examples/mult_by_add.c" "mult_by_add") :=
  certifyFrontend .arm EmbeddedFixtures.files "examples/mult_by_add.c" "mult_by_add"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem mult_by_add_fixture_certifies : multByAddCertifiedResult.isOk := by native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
