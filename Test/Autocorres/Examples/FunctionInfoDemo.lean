import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev functionInfoBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    rec(n : Nat) : Nat {
      ret call rec [n]
    },
    f(n : Nat) : Nat {
      ret call rec [n]
    }
  ]

theorem functionInfoBlocksValid : BlockCtx.Valid functionInfoBlocks := by
  valid_blocks [functionInfoBlocks]

abbrev functionInfoCtx : Ctx := mkCtx functionInfoBlocks functionInfoBlocksValid

theorem functionInfoCtx_wellTyped : Ctx.WellTyped functionInfoCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
