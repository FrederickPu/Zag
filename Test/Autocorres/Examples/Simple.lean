import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev simpleBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    max(x : Nat, y : Nat) : Nat {
      yGreater := op "lt"[x, y];
      ret if yGreater { y } else { x }
    },
    gcd(x : Nat, y : Nat) : Nat {
      ret call gcdLoop [x, y]
    },
    gcdLoop(x : Nat, y : Nat) : Nat {
      done := primEq y nat(0);
      ret if done { x } else { call gcdLoop [y, op "mod"[x, y]] }
    }
  ]

theorem simpleBlocksValid : BlockCtx.Valid simpleBlocks := by
  valid_blocks [simpleBlocks]

abbrev simpleCtx : Ctx := mkCtx simpleBlocks simpleBlocksValid

theorem simpleCtx_wellTyped : Ctx.WellTyped simpleCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
