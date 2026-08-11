import Test.AutoCorres.CParser.ScalarSimpl.PlusFunction

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
def plusCertificate : Certificate .arm EmbeddedFixtures.files
    "examples/plus.c" "plus" plus := plusCertified.certificate

end Zag.Test.AutoCorres.CParser.ScalarSimpl
