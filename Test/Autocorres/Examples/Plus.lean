import Test.Autocorres.Examples.Common

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.Pr.Induction

/-! `plusLoop` is a `while` over two variables: it increments `x` and decrements `y` until `y`
  reaches zero, and answers with `x`. The CPS body computes both next-state values from the current
  state, then passes them to the loop continuation.

  `plusLoop` keeps index 1 in the list: `Test/Induction.lean` reaches for `plusBlocks[1].2`. -/
abbrev plusBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    plus(x : Nat, y : Nat) : Nat {
      ret op "add"[x, y]
    },
    plusLoop(x : Nat, y : Nat) : Nat {
      final := while [plusLoopCond, plusLoopBody] (x, y);
      ret final
    },
    plusLoopCond(x : Nat, y : Nat) : Bool {
      ret primGt y nat(0)
    },
    plusLoopBody(x : Nat, y : Nat, loop : func[Nat, Nat] => Nat) : Nat {
      nextX := op "add"[x, nat(1)];
      nextY := op "sub"[y, nat(1)];
      ret apply loop [nextX, nextY]
    },
    plusMain() : Nat {
      direct := call plus [nat(1), nat(2)];
      looped := call plusLoop [nat(1), nat(2)];
      same := primEq direct looped;
      ret if same { nat(0) } else { nat(1) }
    }
  ]

theorem plusBlocksValid : BlockCtx.Valid plusBlocks := by valid_blocks [plusBlocks]

abbrev plusCtx : Ctx := mkCtx plusBlocks plusBlocksValid

theorem plusCtx_wellTyped : Ctx.WellTyped plusCtx := by typecheck_ctx

/-! ### what the program computes -/

theorem plus_eval (x y : Nat) :
    EvaluatesCall plusCtx "plus" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x + y)) := by
  evaluates_call [heapOpCtx, Op.fixed, plusBlocks]

/-- After `k` turns the state is `(x + k, y - k)`, and the loop exits after `y` of them. -/
theorem plusLoop_eval (x y : Nat) :
    EvaluatesCall plusCtx "plusLoop" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (x + y)) := by
  while_induction [heapOpCtx, Op.fixed, plusBlocks]
    (fun k args => args = [Val.nat (x + k), Val.nat (y - k)]) stopping_at y
    returning (Val.nat (x + y))

/-- The machine really runs the loop: three concrete turns, no invariant involved. -/
example : EvaluatesCall plusCtx "plusLoop" ([Val.nat 1, Val.nat 3] : List (Val heapCtx))
    (Val.nat 4) := by
  evaluates_call [heapOpCtx, Op.fixed, Op.whileOp, Op.Body.collect,
    Op.whileBodyFromValues, Op.whileAfterCondition, Op.whileResultTy?, plusBlocks]

/-- The loop agrees with the one-shot version, which is what `plusMain` checks at runtime. -/
theorem plusMain_eval : EvaluatesCall plusCtx "plusMain" [] (Val.nat 0) := by
  evaluates_call_wp [heapOpCtx, Op.fixed, plusBlocks]
  use_call [heapOpCtx, Op.fixed, plusBlocks] plus_eval
  use_call [heapOpCtx, Op.fixed, plusBlocks] plusLoop_eval
  exact EvaluatesFrom.of_evaluatesTo
    (evaluates_eq_nat (EvaluatesTo.var_local (by rfl)) (EvaluatesTo.var_local (by rfl)))
  apply EvaluatesInstrs.nil
  refine EvaluatesTo.op_applyVals
    (values := [Val.bool true, Val.nat 0, Val.nat 1]) (result := Val.nat 0)
    (Peano.Model.iteOp (ctx := plusCtx))
    (EvaluatesToAll.cons (EvaluatesTo.var_local (name := "same") (v := Val.bool true) (by rfl))
      (EvaluatesToAll.cons (evaluates_nat _ 0)
        (EvaluatesToAll.cons (evaluates_nat _ 1) EvaluatesToAll.nil)))
    (by simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals])

end Zag.Test.Autocorres.Examples
