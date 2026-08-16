import Test.Autocorres.Examples.CList

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev listRevBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    reverse(heap : Heap, head : Ptr) : State[Ptr] {
      ret call listReverse [heap, head]
    }
  ]

abbrev listRevProgramBlocks : BlockCtx.Raw heapCtx :=
  listBlocks ++ listRevBlocks

theorem listRevProgramBlocksValid : BlockCtx.Valid listRevProgramBlocks := by
  valid_blocks [listRevProgramBlocks, listBlocks, listRevBlocks]

abbrev listRevCtx : Ctx := mkCtx listRevProgramBlocks listRevProgramBlocksValid

theorem listRevCtx_wellTyped : Ctx.WellTyped listRevCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
