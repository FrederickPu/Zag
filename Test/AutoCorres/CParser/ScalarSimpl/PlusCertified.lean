import Test.AutoCorres.CParser.ScalarSimpl.PlusFrontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def plusCertified : Certified .arm EmbeddedFixtures.files
    "examples/plus.c" "plus" :=
  plusCertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk plusCertifiedResult plus_fixture_certifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
