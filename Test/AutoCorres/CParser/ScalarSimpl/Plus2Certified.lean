import Test.AutoCorres.CParser.ScalarSimpl.Plus2Frontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def plus2Certified : Certified .arm EmbeddedFixtures.files
    "examples/plus.c" "plus2" :=
  plus2CertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk plus2CertifiedResult plus2_fixture_certifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
