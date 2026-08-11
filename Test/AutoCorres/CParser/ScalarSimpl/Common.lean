import Lang.AutoCorres.CParser.ScalarSimpl

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

namespace FixtureHelpers

theorem except_toOption_isSome_of_isOk (value : Except ε α) (isOk : value.isOk) :
    value.toOption.isSome := by
  cases value with
  | error _ => cases isOk
  | ok _ => rfl

def u32 : ScalarType := ⟨.unsigned, 32⟩
def s32 : ScalarType := ⟨.signed, 32⟩

theorem u32_cast_idempotent (value : Int) :
    u32.cast (u32.cast value) = u32.cast value := by
  simp [u32, ScalarType.cast, ScalarType.unsignedValue, ScalarType.modulus]

theorem u32_checked (value : Int) :
    Expr.checked u32 value = some (u32.cast value) := by
  rfl

end FixtureHelpers

end Zag.Test.AutoCorres.CParser.ScalarSimpl
