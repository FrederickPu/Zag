import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev memsetBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    memset(xs : Array, start : Nat, value : Nat, len : Nat) : Array {
      ret op "arrayFill"[xs, start, len, value]
    },
    zeroNode(xs : Array, start : Nat) : Array {
      ret call memset [xs, start, nat(0), nat(4)]
    }
  ]

theorem memsetBlocksValid : BlockCtx.Valid memsetBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [memsetBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev memsetCtx : Ctx := mkCtx memsetBlocks memsetBlocksValid

theorem memsetCtx_wellTyped : Ctx.WellTyped memsetCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
