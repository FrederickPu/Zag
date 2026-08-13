import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev fibBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    fib(n : Nat) : Nat {
      small := op "lt"[n, nat(2)];
      ret if small { n } else { op "add"[call fib [op "sub"[n, nat(1)]], call fib [op "sub"[n, nat(2)]]] }
    },
    fibLinear(n : Nat) : Nat {
      ret call fibLinearLoop [n, nat(0), nat(1)]
    },
    fibLinearLoop(remaining : Nat, a : Nat, b : Nat) : Nat {
      done := primEq remaining nat(0);
      ret if done { a } else { call fibLinearLoop [op "sub"[remaining, nat(1)], b, op "add"[a, b]] }
    },
    callFib() : Nat {
      ignored := call fib [nat(42)];
      ret nat(0)
    }
  ]

theorem fibBlocksValid : BlockCtx.Valid fibBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [fibBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev fibCtx : Ctx := mkCtx fibBlocks fibBlocksValid

theorem fibCtx_wellTyped : Ctx.WellTyped fibCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
