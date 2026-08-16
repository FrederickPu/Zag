import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev binarySearchBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    binarySearch(xs : Array, needle : Nat) : Bool {
      len := op "arrayLen"[xs];
      ret call binarySearchLoop [xs, needle, nat(0), len]
    },
    binarySearchLoop(xs : Array, needle : Nat, low : Nat, high : Nat) : Bool {
      empty := op "le"[high, low];
      mid := op "div"[op "add"[low, high], nat(2)];
      value := op "arrayGet"[xs, mid];
      found := primEq value needle;
      goLeft := op "lt"[needle, value];
      ret if empty { bool(false) } else {
        if found { bool(true) } else {
          if goLeft { call binarySearchLoop [xs, needle, low, mid] }
          else { call binarySearchLoop [xs, needle, op "add"[mid, nat(1)], high] }
        }
      }
    }
  ]

theorem binarySearchBlocksValid : BlockCtx.Valid binarySearchBlocks := by
  valid_blocks [binarySearchBlocks]

abbrev binarySearchCtx : Ctx := mkCtx binarySearchBlocks binarySearchBlocksValid

theorem binarySearchCtx_wellTyped : Ctx.WellTyped binarySearchCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
