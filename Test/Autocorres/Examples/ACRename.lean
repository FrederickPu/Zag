import Test.Autocorres.Examples.Common

/-! Block analogue of upstream `AC_Rename.thy`. -/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev renameBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    getVAR(heap : Heap, ptr : Ptr) : Nat {
      ret op "load"[heap, ptr]
    },
    setVAR(heap : Heap, ptr : Ptr, value : Nat) : Heap {
      ret op "store"[heap, ptr, value]
    }
  ]

theorem renameBlocksValid : BlockCtx.Valid renameBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [renameBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev renameCtx : Ctx := mkCtx renameBlocks renameBlocksValid

theorem renameCtx_wellTyped : Ctx.WellTyped renameCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
