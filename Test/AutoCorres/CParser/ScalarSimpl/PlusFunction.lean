import Test.AutoCorres.CParser.ScalarSimpl.PlusCertified

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def plus : Function := plusCertified.function

theorem plus_full_function_eq : plusCertified.function = plus := rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
