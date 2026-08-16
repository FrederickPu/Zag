import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev traceDemoBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    traceInc(heap : Heap, ptr : Ptr) : Heap {
      old := op "load"[heap, ptr];
      ret op "store"[heap, ptr, op "add"[old, nat(1)]]
    }
  ]

theorem traceDemoBlocksValid : BlockCtx.Valid traceDemoBlocks := by
  valid_blocks [traceDemoBlocks]

abbrev traceDemoCtx : Ctx := mkCtx traceDemoBlocks traceDemoBlocksValid

theorem traceDemoCtx_wellTyped : Ctx.WellTyped traceDemoCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
