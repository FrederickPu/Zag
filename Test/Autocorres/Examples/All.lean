import Test.Autocorres.Examples.AllWellTypedFirst
import Test.Autocorres.Examples.AllWellTypedSecondFirst
import Test.Autocorres.Examples.AllWellTypedSecondLast

namespace Zag.Test.Autocorres.Examples

theorem autocorresCtx_wellTyped : Ctx.WellTyped autocorresCtx := by
  intro entry hentry
  have hgroups : entry ∈ autocorresBlocksFirst ++ autocorresBlocksSecond := hentry
  rcases List.mem_append.mp hgroups with hfirst | hsecond
  · exact autocorresBlocksFirstWellTyped entry hfirst
  · have hsecondGroups :
        entry ∈ autocorresBlocksSecondFirst ++ autocorresBlocksSecondLast := hsecond
    rcases List.mem_append.mp hsecondGroups with hsecondFirst | hsecondLast
    · exact autocorresBlocksSecondFirstWellTyped entry hsecondFirst
    · exact autocorresBlocksSecondLastWellTyped entry hsecondLast

end Zag.Test.Autocorres.Examples
