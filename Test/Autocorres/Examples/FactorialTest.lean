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
  valid_blocks [factorialBlocks]

abbrev factorialCtx : Ctx := mkCtx factorialBlocks factorialBlocksValid

theorem factorialCtx_wellTyped : Ctx.WellTyped factorialCtx := by typecheck_ctx

def factorialSpec : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * factorialSpec n

theorem factorial_eval (n : Nat) :
    EvaluatesCall factorialCtx "factorial" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (factorialSpec n)) := by
  tail_induction 300 [heapOpCtx, Op.fixed, factorialBlocks, factorialSpec] n

theorem callFactorial_eval :
    EvaluatesCall factorialCtx "callFactorial" [] (Val.nat (factorialSpec 42)) := by
  evaluates_call 300 [heapOpCtx, Op.fixed, factorialBlocks]
  use_call 300 [heapOpCtx, Op.fixed, factorialBlocks] factorial_eval

/-- The same statement at the surface: calling `factorial` on a literal. -/
theorem factorial_eval_call (n : Nat) :
    EvaluatesTo factorialCtx [] (.call "factorial" [Term.nat n])
      (Val.nat (factorialSpec n)) := by
  refine EvaluatesTo.call (factorial_eval n) rfl ?_
  evaluates_to_all [heapOpCtx, Op.fixed, factorialBlocks]

end Zag.Test.Autocorres.Examples
