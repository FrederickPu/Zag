import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev memcpyBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    memcpy(xs : Array, dst : Nat, src : Nat, len : Nat) : Array {
      ret op "arrayCopy"[xs, dst, src, len]
    },
    memcpyInt(xs : Array, dst : Nat, src : Nat) : Array {
      ret call memcpy [xs, dst, src, nat(1)]
    },
    memcpyStruct(xs : Array, dst : Nat, src : Nat) : Array {
      ret call memcpy [xs, dst, src, nat(4)]
    }
  ]

theorem memcpyBlocksValid : BlockCtx.Valid memcpyBlocks := by
  valid_blocks [memcpyBlocks]

abbrev memcpyCtx : Ctx := mkCtx memcpyBlocks memcpyBlocksValid

theorem memcpyCtx_wellTyped : Ctx.WellTyped memcpyCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
