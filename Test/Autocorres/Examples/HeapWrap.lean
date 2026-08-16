import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev heapWrapBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    heapWrap(heap : Heap, ptr : Ptr, value : Nat) : Heap {
      field := op "ptrAdd"[ptr, nat(1)];
      heapField := op "store"[heap, field, value];
      alias := op "ptrAdd"[field, nat(1)];
      ret op "store"[heapField, alias, op "load"[heapField, field]]
    }
  ]

theorem heapWrapBlocksValid : BlockCtx.Valid heapWrapBlocks := by
  valid_blocks [heapWrapBlocks]

abbrev heapWrapCtx : Ctx := mkCtx heapWrapBlocks heapWrapBlocksValid

theorem heapWrapCtx_wellTyped : Ctx.WellTyped heapWrapCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
