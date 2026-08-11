import Test.AutoCorres.CParser.ScalarSimpl.Plus2Certified

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def plus2 : Function := plus2Certified.function

theorem plus2_full_function_eq : plus2Certified.function = plus2 := rfl

end Zag.Test.AutoCorres.CParser.ScalarSimpl
