import Test.Autocorres.Examples.Common
import Meta.Peano.Eval

/-!
Upstream Isabelle theory:
[`Plus.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Plus.thy).

Both unsigned C functions are represented over unbounded `Nat`. Their blocks preserve the source
control flow, but the theorems are explicitly the no-overflow abstraction: neither direct addition
nor loop increment wraps, and no fixed-width or typed-memory fidelity is claimed.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.Pr.Induction
open Zag.EvalTriple
open Zag.EvalTriple.Exact

private abbrev heapOpCtx := pureHeapOpCtx

/-! `plusLoop` is the internal loop for upstream `plus2`: it increments `x` and decrements `y` until `y`
  reaches zero, and answers with `x`. The CPS body computes both next-state values from the current
  state, then passes them to the loop continuation. The public `plus2` block is an extensional
  current-model wrapper around that loop; the split preserves the C algorithm while retaining the
  loop block used by the repository's reflected-induction test.

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
    plus2(x : Nat, y : Nat) : Nat {
      ret call plusLoop [x, y]
    },
    plusMain() : Nat {
      direct := call plus [nat(1), nat(2)];
      looped := call plus2 [nat(1), nat(2)];
      same := primEq direct looped;
      ret if same { nat(0) } else { nat(1) }
    }
  ]

theorem plusBlocksValid : BlockCtx.Valid plusBlocks := by valid_blocks [plusBlocks]

abbrev plusCtx : Ctx := mkPureCtx plusBlocks plusBlocksValid

theorem plusCtx_wellTyped : Ctx.WellTyped plusCtx := by typecheck_ctx

/-! ### what the program computes -/

theorem plus_eval (x y : Nat) :
    Zag.EvaluatesCallValues plusCtx "plus"
      ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x + y))) := by
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plus"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x + y))
  evaluates_call [heapOpCtx, Op.fixed, plusBlocks]

/-- After `k` turns the state is `(x + k, y - k)`, and the loop exits after `y` of them. -/
theorem plusLoop_eval (x y : Nat) :
    Zag.EvaluatesCallValues plusCtx "plusLoop"
      ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x + y))) := by
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plusLoop"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x + y))
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [plusBlocks, Block.entryEnv]
  apply EvaluatesInstrs.cons
  · apply Peano.Exact.while_evaluatesTo (hM := rfl)
      (condName := "plusLoopCond") (bodyName := "plusLoopBody")
      (stateTys := [Ty.prim "Nat" [], Ty.prim "Nat" []]) (resultTy := Ty.prim "Nat" [])
      (I := fun k args => args = [Val.nat (x + k), Val.nat (y - k)]) (N := y)
      (initial := [Val.nat x, Val.nat y]) (loopResult := Val.nat (x + y))
    auto_eval_refinement_goals [heapOpCtx, Op.fixed, plusBlocks]
    case hargs =>
      exact EvaluatesList.cons (by
        apply EvaluatesTo.of_eq
          (EvaluatesTo.var_block (ctx := plusCtx)
            (env := [("x", Val.nat x), ("y", Val.nat y)])
            (name := "plusLoopCond") (hM := rfl) (by rfl) (by rfl))
        rfl)
        (EvaluatesList.cons (by
          apply EvaluatesTo.of_eq
            (EvaluatesTo.var_block (ctx := plusCtx)
              (env := [("x", Val.nat x), ("y", Val.nat y)])
              (name := "plusLoopBody") (hM := rfl) (by rfl) (by rfl))
          rfl)
          (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl))
              EvaluatesList.nil)))
    case preserved =>
      intro n hn
      constructor
      · apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [plusBlocks, Block.entryEnv]
        apply EvaluatesInstrs.nil
        apply EvaluatesTo.of_eq
          (evaluates_gt_nat
            (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (evaluates_nat (hM := rfl) _ 0))
        simp
        omega
      · intro hloop
        apply EvaluatesCallValues.of_evaluatesInstrs
        · rfl
        · rfl
        dsimp [plusBlocks, Block.entryEnv]
        refine EvaluatesInstrs.cons (instrValue := Val.nat (x + n + 1)) ?_ ?_
        · exact evaluates_add_nat
            (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (evaluates_nat (hM := rfl) _ 1)
        refine EvaluatesInstrs.cons (instrValue := Val.nat (y - (n + 1))) ?_ ?_
        · apply EvaluatesTo.of_eq
            (evaluates_sub_nat
              (EvaluatesTo.var_local (hM := rfl) (by rfl))
              (evaluates_nat (hM := rfl) _ 1))
          simp [Nat.sub_sub]
        apply EvaluatesInstrs.nil
        exact EvaluatesTo.app
          (EvaluatesTo.var_local (hM := rfl) (by rfl))
          (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl))
            (EvaluatesList.cons (EvaluatesTo.var_local (hM := rfl) (by rfl))
              EvaluatesList.nil))
          hloop
    case exits =>
      apply EvaluatesCallValues.of_evaluatesInstrs
      · rfl
      · rfl
      dsimp [plusBlocks, Block.entryEnv]
      apply EvaluatesInstrs.nil
      simpa using evaluates_gt_nat
        (ctx := plusCtx)
        (env := [("x", Val.nat (x + y)), ("y", Val.nat 0)])
        (EvaluatesTo.var_local (ctx := plusCtx)
          (env := [("x", Val.nat (x + y)), ("y", Val.nat 0)])
          (name := "y") (value := Val.nat 0) (hM := rfl) (by rfl))
        (evaluates_nat (ctx := plusCtx)
          (env := [("x", Val.nat (x + y)), ("y", Val.nat 0)]) (hM := rfl) 0)
  · apply EvaluatesInstrs.nil
    exact EvaluatesTo.var_local (by rfl)

theorem plus2_eval (x y : Nat) :
    Zag.EvaluatesCallValues plusCtx "plus2"
      ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (x + y))) := by
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plus2"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x + y))
  have hloop := plusLoop_eval x y
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plusLoop"
    ([Val.nat x, Val.nat y] : List (Val heapCtx)) (Val.nat (x + y)) at hloop
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [plusBlocks, Block.entryEnv]
  apply EvaluatesInstrs.nil
  exact EvaluatesTo.call hloop rfl
    (EvaluatesList.cons (EvaluatesTo.var_local (by rfl))
      (EvaluatesList.cons (EvaluatesTo.var_local (by rfl)) EvaluatesList.nil))

/-- A concrete specialization of the exact loop-machine theorem. -/
example : Zag.EvaluatesCallValues plusCtx "plusLoop"
    ([Val.nat 1, Val.nat 3] : List (Val heapCtx))
    (Singleton.idPre True) (Singleton.idPost (· = Val.nat 4)) := by
  simpa using plusLoop_eval 1 3

/-- The loop agrees with the one-shot version, which is what `plusMain` checks at runtime. -/
theorem plusMain_eval :
    Zag.EvaluatesCallValues plusCtx "plusMain" []
      (Singleton.idPre True) (Singleton.idPost (· = Val.nat 0)) := by
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plusMain" [] (Val.nat 0)
  have hplus := plus_eval 1 2
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plus"
    ([Val.nat 1, Val.nat 2] : List (Val heapCtx)) (Val.nat 3) at hplus
  have hplus2 := plus2_eval 1 2
  change Exact.EvaluatesCallValues (hM := rfl) plusCtx "plus2"
    ([Val.nat 1, Val.nat 2] : List (Val heapCtx)) (Val.nat 3) at hplus2
  apply EvaluatesCallValues.of_evaluatesInstrs
  · rfl
  · rfl
  dsimp [plusBlocks, Block.entryEnv]
  refine EvaluatesInstrs.cons (instrValue := Val.nat 3) ?_ ?_
  · exact EvaluatesTo.call hplus rfl
      (EvaluatesList.cons (evaluates_nat _ 1)
        (EvaluatesList.cons (evaluates_nat _ 2) EvaluatesList.nil))
  refine EvaluatesInstrs.cons (instrValue := Val.nat 3) ?_ ?_
  · exact EvaluatesTo.call hplus2 rfl
      (EvaluatesList.cons (evaluates_nat _ 1)
        (EvaluatesList.cons (evaluates_nat _ 2) EvaluatesList.nil))
  refine EvaluatesInstrs.cons (instrValue := Val.bool true) ?_ ?_
  · exact evaluates_eq_nat
      (EvaluatesTo.var_local (name := "direct") (value := Val.nat 3) (hM := rfl) (by rfl))
      (EvaluatesTo.var_local (name := "looped") (value := Val.nat 3) (hM := rfl) (by rfl))
  apply EvaluatesInstrs.nil
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons
      (EvaluatesTo.var_local (name := "same") (value := Val.bool true) (hM := rfl) (by rfl))
      (EvaluatesList.cons (evaluates_nat _ 0)
        (EvaluatesList.cons (evaluates_nat _ 1) EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

end Zag.Test.Autocorres.Examples
