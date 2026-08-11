import Test.AutoCorres.CParser.ScalarSimpl.MultByAddCertified

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def multByAdd : Function := multByAddCertified.function

theorem mult_by_add_full_function_eq : multByAddCertified.function = multByAdd := rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
