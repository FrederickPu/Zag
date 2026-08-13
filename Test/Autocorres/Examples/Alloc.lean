import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev allocBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    initAllocator() : Heap {
      ret raw(termHeap Heap.empty)
    },
    addMemPool(heap : Heap, size : Nat) : Heap {
      ptr := op "allocPtr"[heap, size];
      ret op "allocHeap"[heap, size]
    },
    alloc(heap : Heap, size : Nat) : StatePtr {
      ptr := op "allocPtr"[heap, size];
      heapNext := op "allocHeap"[heap, size];
      ret op "mkStatePtr"[heapNext, ptr]
    },
    dealloc(heap : Heap, ptr : Ptr, size : Nat) : Heap {
      ret op "freeHeap"[heap, ptr, size]
    }
  ]

theorem allocBlocksValid : BlockCtx.Valid allocBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [allocBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev allocCtx : Ctx := mkCtx allocBlocks allocBlocksValid

theorem allocCtx_wellTyped : Ctx.WellTyped allocCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
