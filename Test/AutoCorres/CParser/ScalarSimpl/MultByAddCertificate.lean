import Test.AutoCorres.CParser.ScalarSimpl.MultByAddFunction

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def multByAddCertificate : Certificate .arm EmbeddedFixtures.files
    "examples/mult_by_add.c" "mult_by_add" multByAdd := multByAddCertified.certificate

end Zag.Test.AutoCorres.CParser.ScalarSimpl
