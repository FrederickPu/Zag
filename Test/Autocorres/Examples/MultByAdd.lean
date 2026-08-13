import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev multByAddBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    multByAdd(x : Nat, y : Nat) : Nat {
      ret call multByAddLoop [x, y, nat(0)]
    },
    multByAddLoop(x : Nat, remaining : Nat, acc : Nat) : Nat {
      done := primEq remaining nat(0);
      ret if done { acc } else { call multByAddLoop [x, op "sub"[remaining, nat(1)], op "add"[acc, x]] }
    }
  ]

theorem multByAddBlocksValid : BlockCtx.Valid multByAddBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [multByAddBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool,
        Term.ite, termHeap, termPtr, termArray]

abbrev multByAddCtx : Ctx := mkCtx multByAddBlocks multByAddBlocksValid

theorem multByAddCtx_wellTyped : Ctx.WellTyped multByAddCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
