import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev factorialBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    factorial(n : Nat) : Nat {
      done := primEq n nat(0);
      ret if done { nat(1) } else { op "mul"[n, call factorial [op "sub"[n, nat(1)]]] }
    },
    callFactorial() : Nat {
      ret call factorial [nat(42)]
    }
  ]

theorem factorialBlocksValid : BlockCtx.Valid factorialBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [factorialBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool,
        Term.ite, termHeap, termPtr, termArray]

abbrev factorialCtx : Ctx := mkCtx factorialBlocks factorialBlocksValid

theorem factorialCtx_wellTyped : Ctx.WellTyped factorialCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
