import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev suzukiBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    suzuki(heap : Heap, w : Ptr) : StateNat {
      next1Addr := op "load"[heap, op "ptrAdd"[w, nat(1)]];
      next1 := op "ptrOfNat"[next1Addr];
      next2Addr := op "load"[heap, op "ptrAdd"[next1, nat(1)]];
      next2 := op "ptrOfNat"[next2Addr];
      heapData := op "store"[heap, next2, nat(4)];
      data := op "load"[heapData, next2];
      ret op "mkStateNat"[heapData, data]
    }
  ]

theorem suzukiBlocksValid : BlockCtx.Valid suzukiBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [suzukiBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev suzukiCtx : Ctx := mkCtx suzukiBlocks suzukiBlocksValid

theorem suzukiCtx_wellTyped : Ctx.WellTyped suzukiCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
