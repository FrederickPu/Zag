import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`FactorialTest.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/FactorialTest.thy).

The C recursion is represented exactly, but unsigned arithmetic is abstracted to unbounded `Nat`.
Thus `factorialSpec` and its evaluation theorems are the no-overflow mathematical view; this module
does not claim fixed-width multiplication or wraparound fidelity. The program has no memory access.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

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

abbrev factorialCtx : Ctx := mkPureCtx factorialBlocks factorialBlocksValid

theorem factorialCtx_wellTyped : Ctx.WellTyped factorialCtx := by typecheck_ctx

def factorialSpec : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * factorialSpec n

private theorem factorial_eval_exact (n : Nat) :
    Exact.EvaluatesCallValues factorialCtx "factorial" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (factorialSpec n)) := by
  induction n with
  | zero =>
      evaluates_call 100 [heapOpCtx, Op.fixed, factorialBlocks, factorialSpec]
  | succ n ih =>
      evaluates_call 300 [heapOpCtx, Op.fixed, factorialBlocks, factorialSpec]
      zspec_call 100 [heapOpCtx, Op.fixed, factorialBlocks, factorialSpec] ih

theorem factorial_eval (n : Nat) :
    Zag.EvaluatesCallValues factorialCtx "factorial" ([Val.nat n] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (factorialSpec n))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using factorial_eval_exact n

private theorem callFactorial_eval_exact :
    Exact.EvaluatesCallValues factorialCtx "callFactorial" []
      (Val.nat (factorialSpec 42)) := by
  evaluates_call [heapOpCtx, Op.fixed, factorialBlocks]
  zspec_call [heapOpCtx, Op.fixed, factorialBlocks] (factorial_eval_exact 42)

theorem callFactorial_eval :
    Zag.EvaluatesCallValues factorialCtx "callFactorial" []
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (factorialSpec 42))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using callFactorial_eval_exact

/-- The same statement at the surface: calling `factorial` on a literal. -/
theorem factorial_eval_call (n : Nat) :
    Exact.EvaluatesTo factorialCtx [] (.call "factorial" [Term.nat n])
      (Val.nat (factorialSpec n)) := by
  zspec_call [heapOpCtx, Op.fixed, factorialBlocks] (factorial_eval_exact n)

end Zag.Test.Autocorres.Examples
