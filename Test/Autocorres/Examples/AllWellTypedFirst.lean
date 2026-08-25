import Test.Autocorres.Examples.AllBlocks

namespace Zag.Test.Autocorres.Examples

set_option maxRecDepth 100000 in
theorem autocorresBlocksFirstWellTyped :
    ∀ entry ∈ autocorresBlocksFirst, Block.WellTyped autocorresCtx entry.2 := by
  have h :
      (Pr.TypeUnification.checkBlocks? autocorresCtx autocorresBlocksFirst).isSome = true := by
    decide
  cases hcheck : Pr.TypeUnification.checkBlocks? autocorresCtx autocorresBlocksFirst with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

end Zag.Test.Autocorres.Examples
