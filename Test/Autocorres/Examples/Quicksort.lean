import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev quicksortBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    quicksort(xs : Array, low : Nat, high : Nat) : Array {
      ret op "arraySort"[xs]
    },
    partition(xs : Array, low : Nat, high : Nat) : Array {
      ret op "arraySort"[xs]
    }
  ]

theorem quicksortBlocksValid : BlockCtx.Valid quicksortBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [quicksortBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev quicksortCtx : Ctx := mkCtx quicksortBlocks quicksortBlocksValid

theorem quicksortCtx_wellTyped : Ctx.WellTyped quicksortCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
