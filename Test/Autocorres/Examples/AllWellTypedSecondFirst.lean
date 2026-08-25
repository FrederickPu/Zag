import Test.Autocorres.Examples.AllBlocks

namespace Zag.Test.Autocorres.Examples

set_option maxRecDepth 100000 in
theorem autocorresBlocksSecondFirstWellTyped :
    ∀ entry ∈ autocorresBlocksSecondFirst, Block.WellTyped autocorresCtx entry.2 := by
  have h :
      (Pr.TypeUnification.checkBlocks? autocorresCtx
        autocorresBlocksSecondFirst).isSome = true := by
    decide
  cases hcheck : Pr.TypeUnification.checkBlocks? autocorresCtx autocorresBlocksSecondFirst with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

end Zag.Test.Autocorres.Examples
