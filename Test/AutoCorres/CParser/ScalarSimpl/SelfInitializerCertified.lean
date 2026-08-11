import Test.AutoCorres.CParser.ScalarSimpl.SelfInitializerFrontend

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
def selfInitCertified : Certified .arm selfInitFiles "self-init.c" "f" :=
  selfInitCertifiedResult.toOption.get
    (except_toOption_isSome_of_isOk selfInitCertifiedResult selfInitFixtureCertifies)

end Zag.Test.AutoCorres.CParser.ScalarSimpl
