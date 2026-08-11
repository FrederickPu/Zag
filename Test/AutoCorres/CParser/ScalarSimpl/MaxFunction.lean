import Test.AutoCorres.CParser.ScalarSimpl.MaxCertified

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def maxFunction : Function := maxCertified.function

theorem max_full_function_eq : maxCertified.function = maxFunction := rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
