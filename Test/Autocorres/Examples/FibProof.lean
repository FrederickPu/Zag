import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`FibProof.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/FibProof.thy).

Both upstream algorithms are modeled over unbounded `Nat`: recursive calls and linear control flow
match the C source, while additions and subtractions express its no-overflow abstraction. There is
no fixed-width guard or wraparound semantics, and these functions do not access the heap.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact

private abbrev heapOpCtx := pureHeapOpCtx

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

abbrev fibCtx : Ctx := mkPureCtx fibBlocks fibBlocksValid

theorem fibCtx_wellTyped : Ctx.WellTyped fibCtx := by typecheck_ctx

/-- Mathematical Fibonacci numbers, independent of either program's control flow. -/
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibonacci (n + 1) + fibonacci n

def fibLinearLoopSpec : Nat → Nat → Nat → Nat
| 0, a, _b => a
| n + 1, a, b => fibLinearLoopSpec n b (a + b)

theorem fibLinearLoopSpec_fibonacci (n k : Nat) :
    fibLinearLoopSpec n (fibonacci k) (fibonacci (k + 1)) = fibonacci (k + n) := by
  induction n generalizing k with
  | zero => simp [fibLinearLoopSpec]
  | succ n ih =>
      rw [fibLinearLoopSpec]
      rw [show fibonacci k + fibonacci (k + 1) = fibonacci (k + 2) by
        simp [fibonacci, Nat.add_comm]]
      rw [ih (k + 1)]
      congr 1
      omega

theorem fibLinearLoopSpec_zero_one (n : Nat) :
    fibLinearLoopSpec n 0 1 = fibonacci n := by
  simpa [fibonacci] using fibLinearLoopSpec_fibonacci n 0

private theorem fibLinearLoop_eval_exact (remaining a b : Nat) :
    EvaluatesCallValues fibCtx "fibLinearLoop"
        ([Val.nat remaining, Val.nat a, Val.nat b] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec remaining a b)) := by
  induction remaining generalizing a b with
  | zero =>
      evaluates_call 100 [heapOpCtx, Op.fixed, fibBlocks, fibLinearLoopSpec]
  | succ remaining ih =>
      evaluates_call 300 [heapOpCtx, Op.fixed, fibBlocks, fibLinearLoopSpec]
      zspec_call 100 [heapOpCtx, Op.fixed, fibBlocks, fibLinearLoopSpec] (ih b (a + b))

theorem fibLinearLoop_eval (remaining a b : Nat) :
    Zag.EvaluatesCallValues fibCtx "fibLinearLoop"
        ([Val.nat remaining, Val.nat a, Val.nat b] : List (Val heapCtx))
      (EvalTriple.Singleton.idPre True)
      (EvalTriple.Singleton.idPost (· = Val.nat (fibLinearLoopSpec remaining a b))) := by
  simpa [EvaluatesCallValues, pre, post, EvalTriple.Singleton.idPre, EvalTriple.Singleton.idPost]
    using fibLinearLoop_eval_exact remaining a b

private theorem fibLinear_eval_exact (n : Nat) :
    EvaluatesCallValues fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (fibLinearLoopSpec n 0 1)) := by
  evaluates_call 100 [heapOpCtx, Op.fixed, fibBlocks]
  zspec_call 100 [heapOpCtx, Op.fixed, fibBlocks] (fibLinearLoop_eval_exact n 0 1)

theorem fibLinear_eval (n : Nat) :
    Zag.EvaluatesCallValues fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (EvalTriple.Singleton.idPre True)
      (EvalTriple.Singleton.idPost (· = Val.nat (fibLinearLoopSpec n 0 1))) := by
  simpa [EvaluatesCallValues, pre, post, EvalTriple.Singleton.idPre, EvalTriple.Singleton.idPost]
    using fibLinear_eval_exact n

/-- The linear source program computes the independent mathematical Fibonacci sequence. -/
theorem fibLinear_correct (n : Nat) :
    Zag.EvaluatesCallValues fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (EvalTriple.Singleton.idPre True)
      (EvalTriple.Singleton.idPost (· = Val.nat (fibonacci n))) := by
  simpa [fibLinearLoopSpec_zero_one] using fibLinear_eval n

set_option maxHeartbeats 800000 in
/-- Private Exact spine for the mutual recursive induction. -/
private theorem fib_correct_pair (n : Nat) :
    (EvaluatesCallValues fibCtx "fib" ([Val.nat n] : List (Val heapCtx))
        (Val.nat (fibonacci n))) ∧
    (EvaluatesCallValues fibCtx "fib" ([Val.nat (n + 1)] : List (Val heapCtx))
      (Val.nat (fibonacci (n + 1)))) := by
  induction n with
  | zero =>
      constructor
      · evaluates_call 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
      · evaluates_call 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
  | succ n ih =>
      constructor
      · simpa [Nat.succ_eq_add_one] using ih.2
      · apply EvaluatesCallValues.of_evaluatesInstrs (block := fibBlocks[0].2) <;> try rfl
        dsimp [fibBlocks, Block.entryEnv]
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · evaluates 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
        apply EvaluatesInstrs.nil
        evaluates 300 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
        refine EvalTriple.Exact.EvaluatesFrom.eval_then
          (hterm := EvaluatesTo.call (hM := rfl) ih.2 rfl ?_) ?_
        · evaluates_to_all 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
        · intro scope
          evaluates_from 300 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
          refine EvalTriple.Exact.EvaluatesFrom.eval_then
            (hterm := EvaluatesTo.call (hM := rfl) ih.1 rfl ?_) ?_
          · evaluates_to_all 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]
          · intro scope
            evaluates_from 100 [heapOpCtx, Op.fixed, fibBlocks, fibonacci]

/-- The recursive source program computes the same independent Fibonacci sequence. -/
theorem fib_correct (n : Nat) :
    Zag.EvaluatesCallValues fibCtx "fib" ([Val.nat n] : List (Val heapCtx))
      (EvalTriple.Singleton.idPre True)
      (EvalTriple.Singleton.idPost (· = Val.nat (fibonacci n))) := by
  simpa [EvaluatesCallValues, pre, post, EvalTriple.Singleton.idPre, EvalTriple.Singleton.idPost]
    using (fib_correct_pair n).1

/-- The same statement at the surface: calling `fibLinear` on a literal. -/
theorem fibLinear_eval_call (n : Nat) :
    EvaluatesTo fibCtx [] (.call "fibLinear" [Term.nat n])
      (Val.nat (fibonacci n)) := by
  have h : EvaluatesCallValues fibCtx "fibLinear" ([Val.nat n] : List (Val heapCtx))
      (Val.nat (fibonacci n)) := by
    simpa [fibLinearLoopSpec_zero_one] using fibLinear_eval_exact n
  zspec_call [heapOpCtx, Op.fixed, fibBlocks] h

end Zag.Test.Autocorres.Examples
