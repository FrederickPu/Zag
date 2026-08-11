import Test.AutoCorres.CParser.ScalarSimpl.MaxFrontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def maxCertified : Certified .arm EmbeddedFixtures.files
    "examples/simple.c" "max" :=
  maxCertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk maxCertifiedResult max_fixture_certifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
