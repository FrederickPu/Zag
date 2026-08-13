import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev schorrWaiteBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    mark(heap : Heap, root : Ptr) : Heap {
      ret call markLoop [heap, root]
    },
    markLoop(heap : Heap, current : Ptr) : Heap {
      done := op "ptrIsNull"[current];
      markField := op "ptrAdd"[current, nat(2)];
      heapMarked := op "store"[heap, markField, nat(1)];
      nextAddr := op "load"[heap, op "ptrAdd"[current, nat(1)]];
      nextPtr := op "ptrOfNat"[nextAddr];
      ret if done { heap } else { call markLoop [heapMarked, nextPtr] }
    },
    recursiveMark(heap : Heap, root : Ptr) : Heap {
      ret call mark [heap, root]
    }
  ]

theorem schorrWaiteBlocksValid : BlockCtx.Valid schorrWaiteBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [schorrWaiteBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool,
        Term.ite, termHeap, termPtr, termArray]

abbrev schorrWaiteCtx : Ctx := mkCtx schorrWaiteBlocks schorrWaiteBlocksValid

theorem schorrWaiteCtx_wellTyped : Ctx.WellTyped schorrWaiteCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
