import Test.AutoCorres.CParser.ScalarSimpl.Plus2Function

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def plus2Certificate : Certificate .arm EmbeddedFixtures.files
    "examples/plus.c" "plus2" plus2 := plus2Certified.certificate

end Zag.Test.AutoCorres.CParser.ScalarSimpl
