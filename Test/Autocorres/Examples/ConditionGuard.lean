import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev conditionGuardBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    guardedLoad(heap : Heap, ptr : Ptr) : Nat {
      isNull := op "ptrIsNull"[ptr];
      ret if isNull { nat(0) } else { op "load"[heap, ptr] }
    },
    guardedDiv(x : Nat, y : Nat) : Nat {
      zero := primEq y nat(0);
      ret if zero { nat(0) } else { op "div"[x, y] }
    }
  ]

theorem conditionGuardBlocksValid : BlockCtx.Valid conditionGuardBlocks := by
  valid_blocks [conditionGuardBlocks]

abbrev conditionGuardCtx : Ctx := mkCtx conditionGuardBlocks conditionGuardBlocksValid

theorem conditionGuardCtx_wellTyped : Ctx.WellTyped conditionGuardCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
