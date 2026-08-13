import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev kmallocBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    kmalloc(heap : Heap, size : Nat, align : Nat) : StatePtr {
      rounded := op "add"[size, align];
      ptr := op "allocPtr"[heap, rounded];
      heapNext := op "allocHeap"[heap, rounded];
      ret op "mkStatePtr"[heapNext, ptr]
    },
    kfree(heap : Heap, ptr : Ptr, size : Nat) : Heap {
      ret op "freeHeap"[heap, ptr, size]
    },
    sepKmalloc(heap : Heap, size : Nat, align : Nat) : StatePtr {
      ret call kmalloc [heap, size, align]
    },
    sepFree(heap : Heap, ptr : Ptr, size : Nat) : Heap {
      ret call kfree [heap, ptr, size]
    }
  ]

theorem kmallocBlocksValid : BlockCtx.Valid kmallocBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [kmallocBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev kmallocCtx : Ctx := mkCtx kmallocBlocks kmallocBlocksValid

theorem kmallocCtx_wellTyped : Ctx.WellTyped kmallocCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
