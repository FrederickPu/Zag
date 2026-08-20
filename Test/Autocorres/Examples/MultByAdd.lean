import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! `multByAddLoop` is a `while` over three variables. The loop answers with its *first* variable,
  so the state is ordered `(acc, remaining, x)` even though the block's own parameters keep the
  upstream order. The CPS body computes the simultaneous next state and passes it to the loop
  continuation; `x` remains unchanged. -/
abbrev multByAddBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    multByAdd(x : Nat, y : Nat) : Nat {
      ret call multByAddLoop [x, y, nat(0)]
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

abbrev multByAddCtx : Ctx := mkCtx multByAddBlocks multByAddBlocksValid

theorem multByAddCtx_wellTyped : Ctx.WellTyped multByAddCtx := by typecheck_ctx

/-- The loop accumulates one `x` per remaining step: after `k` turns the state is
  `(acc + k * x, remaining - k, x)`, and it exits after `remaining` of them. -/
theorem multByAddLoop_eval (x remaining acc : Nat) :
    EvaluatesCall multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Val.nat (acc + remaining * x)) := by
  while_induction [heapOpCtx, Op.fixed, multByAddBlocks, Nat.succ_mul]
    (fun k args => args = [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x])
    stopping_at remaining returning (Val.nat (acc + remaining * x))

/-- The same loop with `Nat.succ_mul` withheld -- the smallest case in the repository where the
  tactic does not close everything.

  `+arith` handles the linear part, so the residue is exactly the one nonlinear fact about the
  accumulator, exposed as an ordinary preservation goal. -/
example (x remaining acc : Nat) :
    EvaluatesCall multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Val.nat (acc + remaining * x)) := by
  while_induction [heapOpCtx, Op.fixed, multByAddBlocks]
    (fun k args => args = [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x])
    stopping_at remaining returning (Val.nat (acc + remaining * x))
  case step.preservation =>
    constructor
    · simp [Nat.succ_mul, Nat.add_comm]
    · omega

/-- The machine really runs the three-variable loop: four concrete turns of four blocks each. -/
example : EvaluatesCall multByAddCtx "multByAddLoop"
    ([Val.nat 3, Val.nat 4, Val.nat 0] : List (Val heapCtx)) (Val.nat 12) := by
  evaluates_call [heapOpCtx, Op.fixed, Op.whileOp, Op.Body.collect,
    Op.whileBodyFromValues, Op.whileAfterCondition, Op.whileResultTy?, multByAddBlocks]

theorem multByAdd_eval (x y : Nat) :
    EvaluatesCall multByAddCtx "multByAdd" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x * y)) := by
  evaluates_call_wp [heapOpCtx, Op.fixed, multByAddBlocks, Nat.mul_comm]
  use_call [heapOpCtx, Op.fixed, multByAddBlocks, Nat.mul_comm] multByAddLoop_eval

/-- The same statement at the surface: calling `multByAdd` on two literals. -/
theorem multByAdd_eval_call (x y : Nat) :
    EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  refine EvaluatesTo.call (multByAdd_eval x y) rfl ?_
  evaluates_to_all [heapOpCtx, Op.fixed, multByAddBlocks]

end Zag.Test.Autocorres.Examples
