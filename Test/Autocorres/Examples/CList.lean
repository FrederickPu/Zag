import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev listBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    listPrepend(heap : Heap, head : Ptr, value : Nat) : StatePtr {
      node := op "allocPtr"[heap, nat(2)];
      heapAlloc := op "allocHeap"[heap, nat(2)];
      nextField := op "ptrAdd"[node, nat(1)];
      heapValue := op "store"[heapAlloc, node, value];
      headAddr := op "ptrAddr"[head];
      heapNext := op "store"[heapValue, nextField, headAddr];
      ret op "mkStatePtr"[heapNext, node]
    },
    listReverse(heap : Heap, head : Ptr) : StatePtr {
      ret call listReverseLoop [heap, head, raw(termPtr 0)]
    },
    listReverseLoop(heap : Heap, current : Ptr, acc : Ptr) : StatePtr {
      done := op "ptrIsNull"[current];
      nextField := op "ptrAdd"[current, nat(1)];
      nextAddr := op "load"[heap, nextField];
      nextPtr := op "ptrOfNat"[nextAddr];
      accAddr := op "ptrAddr"[acc];
      heapNext := op "store"[heap, nextField, accAddr];
      ret if done { op "mkStatePtr"[heap, acc] } else { call listReverseLoop [heapNext, nextPtr, current] }
    },
    sortedInsert(xs : Array, value : Nat) : Array {
      ret op "arrayInsertSorted"[xs, value]
    }
  ]

theorem listBlocksValid : BlockCtx.Valid listBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [listBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev listCtx : Ctx := mkCtx listBlocks listBlocksValid

theorem listCtx_wellTyped : Ctx.WellTyped listCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
