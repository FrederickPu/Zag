import Test.Autocorres.Examples.MultByAdd

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! An apply-only proof of `multByAddLoop_eval`. Evaluation is assembled from semantic rules;
  there are no evaluator tactics or `simp` calls in this file. Run
  `lake env lean -D 'trace.profiler=true' -D 'trace.profiler.threshold=1'
  Test/Autocorres/Examples/MultByAddLoopManual.lean` for the detailed breakdown. -/

theorem multByAddLoop_eval_manual (x remaining acc : Nat) :
    EvaluatesCall multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Val.nat (acc + remaining * x)) := by
  apply EvaluatesCall.of_evaluatesInstrs
    (name := "multByAddLoop") (block := multByAddBlocks[1].2)
  · rfl
  · rfl
  refine EvaluatesInstrs.cons
    (instrValue := Val.nat (acc + remaining * x)) ?_ ?_
  · apply Peano.while_evaluatesTo
      (I := fun k args =>
        args = [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x])
      (N := remaining)
      (opName := "while")
      (condName := "multByAddCond")
      (bodyName := "multByAddBody")
      (stateTys := [Peano.NatTy, Peano.NatTy, Peano.NatTy])
      (resultTy := Peano.NatTy)
      (initial := [Val.nat acc, Val.nat remaining, Val.nat x])
    · rfl
    · exact EvaluatesToAll.cons
        (EvaluatesTo.var_block (ctx := multByAddCtx)
          (env := [("x", Val.nat x), ("remaining", Val.nat remaining), ("acc", Val.nat acc)])
          (name := "multByAddCond") (block := multByAddBlocks[2].2) (by rfl) (by rfl))
        (EvaluatesToAll.cons
          (EvaluatesTo.var_block (ctx := multByAddCtx)
            (env := [("x", Val.nat x), ("remaining", Val.nat remaining), ("acc", Val.nat acc)])
            (name := "multByAddBody") (block := multByAddBlocks[3].2) (by rfl) (by rfl))
          (EvaluatesToAll.cons
            (EvaluatesTo.var_local (by rfl))
            (EvaluatesToAll.cons
              (EvaluatesTo.var_local (by rfl))
              (EvaluatesToAll.cons
                (EvaluatesTo.var_local (by rfl))
                EvaluatesToAll.nil))))
    · rfl
    · change [Val.nat acc, Val.nat remaining, Val.nat x] =
        [Val.nat (acc + 0 * x), Val.nat (remaining - 0), Val.nat x]
      rw [Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    · intro k args hargs
      subst args
      rfl
    · intro k args hk hargs
      subst args
      constructor
      · apply EvaluatesCall.of_evaluatesInstrs
          (name := "multByAddCond") (block := multByAddBlocks[2].2)
        · rfl
        · rfl
        apply EvaluatesInstrs.nil
        change EvaluatesTo multByAddCtx
          [("acc", Val.nat (acc + k * x)),
           ("remaining", Val.nat (remaining - k)),
           ("x", Val.nat x)]
          (.op "gt" [.var "remaining", Term.nat 0]) (Val.bool true)
        have hgt := evaluates_gt_nat (ctx := multByAddCtx)
          (env :=
            [("acc", Val.nat (acc + k * x)),
             ("remaining", Val.nat (remaining - k)),
             ("x", Val.nat x)])
          (a := .var "remaining") (b := Term.nat 0)
          (m := remaining - k) (n := 0)
          (EvaluatesTo.var_local (by rfl))
          (evaluates_nat _ 0)
        have hp : decide (0 < remaining - k) = true :=
          decide_eq_true (Nat.sub_pos_of_lt hk)
        rw [hp] at hgt
        exact hgt
      intro loop
      let loopRef : Val heapCtx :=
        Peano.whileRef "while" "multByAddCond" "multByAddBody"
          [Peano.NatTy, Peano.NatTy, Peano.NatTy] Peano.NatTy
      change EvaluatesCall multByAddCtx "multByAddBody"
        [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x, loopRef]
        (Val.nat (acc + remaining * x))
      apply EvaluatesCall.of_evaluatesInstrs
        (name := "multByAddBody") (block := multByAddBlocks[3].2)
      · rfl
      · rfl
      refine EvaluatesInstrs.cons
        (instrValue := Val.nat ((acc + k * x) + x)) ?_ ?_
      · exact evaluates_add_nat (ctx := multByAddCtx)
          (env :=
            [("acc", Val.nat (acc + k * x)),
             ("remaining", Val.nat (remaining - k)),
             ("x", Val.nat x),
             ("loop", loopRef)])
          (a := .var "acc") (b := .var "x")
          (EvaluatesTo.var_local (by rfl))
          (EvaluatesTo.var_local (by rfl))
      refine EvaluatesInstrs.cons
        (instrValue := Val.nat ((remaining - k) - 1)) ?_ ?_
      · exact evaluates_sub_nat (ctx := multByAddCtx)
          (env :=
            [("acc", Val.nat (acc + k * x)),
             ("remaining", Val.nat (remaining - k)),
             ("x", Val.nat x),
             ("loop", loopRef),
             ("nextAcc", Val.nat ((acc + k * x) + x))])
          (a := .var "remaining") (b := Term.nat 1)
          (EvaluatesTo.var_local (by rfl))
          (evaluates_nat _ 1)
      apply EvaluatesInstrs.nil
      apply EvaluatesTo.app
      · exact EvaluatesTo.var_local (by rfl)
      · exact EvaluatesToAll.cons
          (EvaluatesTo.var_local (by rfl))
          (EvaluatesToAll.cons
            (EvaluatesTo.var_local (by rfl))
            (EvaluatesToAll.cons
              (EvaluatesTo.var_local (by rfl))
              EvaluatesToAll.nil))
      apply loop
      have hacc : (acc + k * x) + x = acc + (k + 1) * x := by
        calc
          (acc + k * x) + x = acc + (k * x + x) := Nat.add_assoc _ _ _
          _ = acc + (k + 1) * x :=
            congrArg (fun n => acc + n) (Nat.succ_mul k x).symm
      have hremaining : (remaining - k) - 1 = remaining - (k + 1) :=
        Nat.sub_sub remaining k 1
      rw [hacc, hremaining]
    · intro args hargs
      subst args
      constructor
      · apply EvaluatesCall.of_evaluatesInstrs
          (name := "multByAddCond") (block := multByAddBlocks[2].2)
        · rfl
        · rfl
        apply EvaluatesInstrs.nil
        change EvaluatesTo multByAddCtx
          [("acc", Val.nat (acc + remaining * x)),
           ("remaining", Val.nat (remaining - remaining)),
           ("x", Val.nat x)]
          (.op "gt" [.var "remaining", Term.nat 0]) (Val.bool false)
        have hgt := evaluates_gt_nat (ctx := multByAddCtx)
          (env :=
            [("acc", Val.nat (acc + remaining * x)),
             ("remaining", Val.nat (remaining - remaining)),
             ("x", Val.nat x)])
          (a := .var "remaining") (b := Term.nat 0)
          (m := remaining - remaining) (n := 0)
          (EvaluatesTo.var_local (by rfl))
          (evaluates_nat _ 0)
        have hp : decide (0 < remaining - remaining) = false := by
          apply decide_eq_false
          omega
        rw [hp] at hgt
        exact hgt
      · rfl
  exact EvaluatesInstrs.nil (EvaluatesTo.var_local (by rfl))

end Zag.Test.Autocorres.Examples
