import Test.Autocorres.Examples.TypeStrengthenTricks

/-!
The upstream `Incremental.thy` re-runs AutoCorres over selected functions from
`type_strengthen.c`. The block analogue reuses the same selected program context.
-/

namespace Zag.Test.Autocorres.Examples

abbrev incrementalBlocks := typeStrengthenBlocks
abbrev incrementalProgramBlocks := typeStrengthenProgramBlocks
abbrev incrementalCtx := typeStrengthenCtx

theorem incrementalCtx_wellTyped : Ctx.WellTyped incrementalCtx :=
  typeStrengthenCtx_wellTyped

end Zag.Test.Autocorres.Examples
