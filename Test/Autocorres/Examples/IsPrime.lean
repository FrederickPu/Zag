import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev isPrimeBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    isPrime(n : Nat) : Bool {
      small := op "lt"[n, nat(2)];
      ret if small { bool(false) } else { call isPrimeLoop [n, nat(2)] }
    },
    isPrimeLoop(n : Nat, div : Nat) : Bool {
      past := op "lt"[n, op "mul"[div, div]];
      divides := primEq op "mod"[n, div] nat(0);
      ret if past { bool(true) } else { if divides { bool(false) } else { call isPrimeLoop [n, op "add"[div, nat(1)]] } }
    },
    isPrimeSqrt(n : Nat, limit : Nat) : Bool {
      small := op "lt"[n, nat(2)];
      ret if small { bool(false) } else { call isPrimeSqrtLoop [n, nat(2), limit] }
    },
    isPrimeSqrtLoop(n : Nat, div : Nat, limit : Nat) : Bool {
      pastLimit := op "lt"[limit, div];
      pastSquare := op "lt"[n, op "mul"[div, div]];
      done := op "ite"[pastLimit, bool(true), pastSquare];
      divides := primEq op "mod"[n, div] nat(0);
      ret if done { bool(true) } else { if divides { bool(false) } else { call isPrimeSqrtLoop [n, op "add"[div, nat(1)], limit] } }
    }
  ]

theorem isPrimeBlocksValid : BlockCtx.Valid isPrimeBlocks := by
  constructor
  case left => decide
  case right =>
    set_option linter.unusedSimpArgs false in
      simp [isPrimeBlocks, Block.callNames, Term.callNames, Term.nat, Term.bool, Term.ite,
        termHeap, termPtr, termArray]

abbrev isPrimeCtx : Ctx := mkCtx isPrimeBlocks isPrimeBlocksValid

theorem isPrimeCtx_wellTyped : Ctx.WellTyped isPrimeCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
