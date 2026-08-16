import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev wordAbsBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    wordOps(x : Nat, y : Nat, shift : Nat) : Nat {
      anded := op "bitAnd"[x, y];
      ored := op "bitOr"[x, y];
      xored := op "bitXor"[anded, ored];
      shifted := op "shl"[xored, shift];
      ret op "shr"[shifted, shift]
    }
  ]

theorem wordAbsBlocksValid : BlockCtx.Valid wordAbsBlocks := by
  valid_blocks [wordAbsBlocks]

abbrev wordAbsCtx : Ctx := mkCtx wordAbsBlocks wordAbsBlocksValid

theorem wordAbsCtx_wellTyped : Ctx.WellTyped wordAbsCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
