import Test.Autocorres.Examples.AllBlocks

namespace Zag.Test.Autocorres.Examples

set_option maxRecDepth 100000 in
theorem autocorresBlocksSecondLastWellTyped :
    ∀ entry ∈ autocorresBlocksSecondLast, Block.WellTyped autocorresCtx entry.2 := by
  have h :
      (Pr.TypeUnification.checkBlocks? autocorresCtx
        autocorresBlocksSecondLast).isSome = true := by
    decide
  cases hcheck : Pr.TypeUnification.checkBlocks? autocorresCtx autocorresBlocksSecondLast with
  | none => simp [hcheck] at h
  | some proof => exact proof.down

end Zag.Test.Autocorres.Examples
