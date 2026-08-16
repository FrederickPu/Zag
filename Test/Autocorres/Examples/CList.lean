import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev listBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    listPrepend(heap : Heap, head : Ptr, value : Nat) : State[Ptr] {
      node := op "allocPtr"[heap, nat(2)];
      heapAlloc := op "allocHeap"[heap, nat(2)];
      nextField := op "ptrAdd"[node, nat(1)];
      heapValue := op "store"[heapAlloc, node, value];
      headAddr := op "ptrAddr"[head];
      heapNext := op "store"[heapValue, nextField, headAddr];
      ret op "mkState"[heapNext, node]
    },
    listReverse(heap : Heap, head : Ptr) : State[Ptr] {
      ret call listReverseLoop [heap, head, raw(termPtr 0)]
    },
    listReverseLoop(heap : Heap, current : Ptr, acc : Ptr) : State[Ptr] {
      done := op "ptrIsNull"[current];
      nextField := op "ptrAdd"[current, nat(1)];
      nextAddr := op "load"[heap, nextField];
      nextPtr := op "ptrOfNat"[nextAddr];
      accAddr := op "ptrAddr"[acc];
      heapNext := op "store"[heap, nextField, accAddr];
      ret if done { op "mkState"[heap, acc] } else { call listReverseLoop [heapNext, nextPtr, current] }
    },
    sortedInsert(xs : Array, value : Nat) : Array {
      ret op "arrayInsertSorted"[xs, value]
    }
  ]

theorem listBlocksValid : BlockCtx.Valid listBlocks := by
  valid_blocks [listBlocks]

abbrev listCtx : Ctx := mkCtx listBlocks listBlocksValid

theorem listCtx_wellTyped : Ctx.WellTyped listCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
