import Test.Autocorres.Examples.CList

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev listRevBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    reverse(heap : Heap, head : Ptr) : StatePtr {
      ret call listReverse [heap, head]
    }
  ]

abbrev listRevProgramBlocks : BlockCtx.Raw heapCtx :=
  listBlocks ++ listRevBlocks

theorem listRevProgramBlocksValid : BlockCtx.Valid listRevProgramBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [listRevProgramBlocks, listBlocks, listRevBlocks, Block.callNames,
        Term.callNames, Term.nat, Term.bool, Term.ite, termHeap, termPtr, termArray]

abbrev listRevCtx : Ctx := mkCtx listRevProgramBlocks listRevProgramBlocksValid

theorem listRevCtx_wellTyped : Ctx.WellTyped listRevCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
