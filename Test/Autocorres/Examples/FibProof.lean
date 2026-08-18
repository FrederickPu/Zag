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

theorem fibBlocksValid : BlockCtx.Valid fibBlocks := by valid_blocks [fibBlocks]

abbrev fibCtx : Ctx := mkCtx fibBlocks fibBlocksValid

theorem fibCtx_wellTyped : Ctx.WellTyped fibCtx := by typecheck_ctx

def fibLinearLoopSpec : Nat → Nat → Nat → Nat
| 0, a, _b => a
| n + 1, a, b => fibLinearLoopSpec n b (a + b)

theorem fibLinearLoop_eval (remaining a b : Nat) :
    EvaluatesCall fibCtx "fibLinearLoop"
        ([Val.nat remaining, Val.nat a, Val.nat b] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec remaining a b)) := by
  tail_induction 300 [heapOpCtx, Op.fixed, fibBlocks, fibLinearLoopSpec]
    remaining generalizing a b

theorem fibLinear_eval (n : Nat) :
    EvaluatesCall fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec n 0 1)) := by
  evaluates_call 300 [heapOpCtx, Op.fixed, fibBlocks]
  use_call 300 [heapOpCtx, Op.fixed, fibBlocks] fibLinearLoop_eval

/-- The same statement at the surface: calling `fibLinear` on a literal. -/
theorem fibLinear_eval_call (n : Nat) :
    EvaluatesTo fibCtx [] (.call "fibLinear" [Term.nat n])
      (Val.nat (fibLinearLoopSpec n 0 1)) := by
  refine EvaluatesTo.call (fibLinear_eval n) rfl ?_
  evaluates_to_all [heapOpCtx, Op.fixed, fibBlocks]

end Zag.Test.Autocorres.Examples
