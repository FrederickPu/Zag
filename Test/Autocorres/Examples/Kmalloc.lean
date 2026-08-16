import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev kmallocBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    kmalloc(heap : Heap, size : Nat, align : Nat) : State[Ptr] {
      rounded := op "add"[size, align];
      ptr := op "allocPtr"[heap, rounded];
      heapNext := op "allocHeap"[heap, rounded];
      ret op "mkState"[heapNext, ptr]
    },
    kfree(heap : Heap, ptr : Ptr, size : Nat) : Heap {
      ret op "freeHeap"[heap, ptr, size]
    },
    sepKmalloc(heap : Heap, size : Nat, align : Nat) : State[Ptr] {
      ret call kmalloc [heap, size, align]
    },
    sepFree(heap : Heap, ptr : Ptr, size : Nat) : Heap {
      ret call kfree [heap, ptr, size]
    }
  ]

theorem kmallocBlocksValid : BlockCtx.Valid kmallocBlocks := by
  valid_blocks [kmallocBlocks]

abbrev kmallocCtx : Ctx := mkCtx kmallocBlocks kmallocBlocksValid

theorem kmallocCtx_wellTyped : Ctx.WellTyped kmallocCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
