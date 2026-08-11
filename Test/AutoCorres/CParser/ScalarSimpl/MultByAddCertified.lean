import Test.AutoCorres.CParser.ScalarSimpl.MultByAddFrontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def multByAddCertified : Certified .arm EmbeddedFixtures.files
    "examples/mult_by_add.c" "mult_by_add" :=
  multByAddCertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk multByAddCertifiedResult mult_by_add_fixture_certifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
