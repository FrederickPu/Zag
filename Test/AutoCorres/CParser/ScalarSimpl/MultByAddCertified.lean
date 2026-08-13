import Test.AutoCorres.CParser.ScalarSimpl.MultByAddFrontend
import Lang.AutoCorres.Refinement

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

run_refinement multByAddCertified from multByAddCertifiedResult
success_by exact mult_by_add_fixture_certifies

end Zag.Test.AutoCorres.CParser.ScalarSimpl
