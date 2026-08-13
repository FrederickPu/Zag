import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev swapBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    swap(heap : Heap, a : Ptr, b : Ptr) : Heap {
      av := op "load"[heap, a];
      bv := op "load"[heap, b];
      heapA := op "store"[heap, a, bv];
      ret op "store"[heapA, b, av]
    }
  ]

theorem swapBlocksValid : BlockCtx.Valid swapBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [swapBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev swapCtx : Ctx := mkCtx swapBlocks swapBlocksValid

theorem swapCtx_wellTyped : Ctx.WellTyped swapCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
