import Test.AutoCorres.CParser.ScalarSimpl.GcdFrontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def gcdCertified : Certified .arm EmbeddedFixtures.files "examples/simple.c" "gcd" :=
  gcdCertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk gcdCertifiedResult gcd_fixture_certifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
