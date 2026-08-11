import Test.AutoCorres.CParser.ScalarSimpl.MaxFunction

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def maxCertificate : Certificate .arm EmbeddedFixtures.files
    "examples/simple.c" "max" maxFunction := maxCertified.certificate

end Zag.Test.AutoCorres.CParser.ScalarSimpl
