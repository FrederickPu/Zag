import Test.Autocorres.Examples.Common
import Meta.Peano.Eval

/-!
Upstream Isabelle theory:
[`MultByAdd.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/MultByAdd.thy).

The loop proof is the apply-only spine (performance baseline matching MultByAddLoopManual).
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open scoped Std.Do

abbrev multByAddBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    multByAdd(x : Nat, y : Nat) : Nat {
      ret call multByAddLoop [y, x, nat(0)]
    },
    multByAddLoop(x : Nat, remaining : Nat, acc : Nat) : Nat {
      final := while [multByAddCond, multByAddBody] (acc, remaining, x);
      ret final
    },
    multByAddCond(acc : Nat, remaining : Nat, x : Nat) : Bool {
      ret primGt remaining nat(0)
    },
    multByAddBody(acc : Nat, remaining : Nat, x : Nat,
        loop : func[Nat, Nat, Nat] => Nat) : Nat {
      nextAcc := op "add"[acc, x];
      nextRemaining := op "sub"[remaining, nat(1)];
      ret apply loop [nextAcc, nextRemaining, x]
    }
  ]

theorem multByAddBlocksValid : BlockCtx.Valid multByAddBlocks := by
  valid_blocks [multByAddBlocks]

abbrev multByAddCtx : Ctx := mkPureCtx multByAddBlocks multByAddBlocksValid

theorem multByAddCtx_wellTyped : Ctx.WellTyped multByAddCtx := by typecheck_ctx

/-- Pure total-correctness: monadic `EvaluatesCallValues` with trivial pre and equality post. -/
theorem multByAddLoop_eval (x remaining acc : Nat) :
    Zag.EvaluatesCallValues multByAddCtx "multByAddLoop"
      ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (acc + remaining * x))) := by
  -- Exact sugar is the Id specialization of the same monadic judgment.
  change Exact.EvaluatesCallValues (hM := rfl) multByAddCtx "multByAddLoop"
    ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
    (Val.nat (acc + remaining * x))
  zspec whileInduction [pureHeapOpCtx, Op.fixed, multByAddBlocks, Nat.succ_mul]
    (fun k args =>
      args = [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x])
    stopping_at remaining returning (Val.nat (acc + remaining * x))

example :
    Zag.EvaluatesCallValues multByAddCtx "multByAddLoop"
      ([Val.nat 3, Val.nat 4, Val.nat 0] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat 12)) := by
  simpa using multByAddLoop_eval 3 4 0

theorem multByAdd_eval (x y : Nat) :
    Zag.EvaluatesCallValues multByAddCtx "multByAdd"
      ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x * y))) := by
  change Exact.EvaluatesCallValues (hM := rfl) multByAddCtx "multByAdd"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x * y))
  have hloop : Exact.EvaluatesCallValues multByAddCtx "multByAddLoop"
      ([Val.nat y, Val.nat x, Val.nat 0] : List (Val heapCtx))
      (Val.nat (x * y)) := by
    simpa [Nat.mul_comm, Exact.EvaluatesCallValues, Exact.pre, Exact.post,
      Singleton.idPre, Singleton.idPost] using multByAddLoop_eval y x 0
  open Exact in
  apply EvaluatesCallValues.of_evaluatesInstrs
    (name := "multByAdd") (block := multByAddBlocks[0].2)
  · rfl
  · rfl
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call hloop (by rfl)
    (EvaluatesList.cons (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl))
        (EvaluatesList.cons (evaluates_nat _ 0) EvaluatesList.nil)))

theorem multByAdd_eval_call (x y : Nat) :
    Exact.EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  have h := multByAdd_eval x y
  change Exact.EvaluatesCallValues (hM := rfl) multByAddCtx "multByAdd"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x * y)) at h
  open Exact in
  exact EvaluatesTo.call h (by rfl)
    (EvaluatesList.cons (evaluates_nat _ x)
      (EvaluatesList.cons (evaluates_nat _ y) EvaluatesList.nil))

end Zag.Test.Autocorres.Examples
