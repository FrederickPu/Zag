import Test.Autocorres.Examples.Common

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

abbrev multByAddWhileRef : Val heapCtx :=
  Peano.Exact.whileRef "while" "multByAddCond" "multByAddBody" [NatTy, NatTy, NatTy] NatTy

theorem multByAddCond_eval? (acc remaining x : Nat) :
    Std.Do.Triple (Exact.callValues? multByAddCtx "multByAddCond"
        ([Val.nat acc, Val.nat remaining, Val.nat x] : List (Val heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.bool (decide (0 < remaining)))) := by
  let env := multByAddBlocks[2].2.entryEnv
    ([Val.nat acc, Val.nat remaining, Val.nat x] : List (Val heapCtx))
  have hremaining : Std.Do.Triple (Exact.eval? multByAddCtx env
      (Term.var "remaining") rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat remaining)) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hzero : Std.Do.Triple (Exact.eval? multByAddCtx env
      (Term.nat 0) rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat 0)) := by
    exact Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.evaluates_nat (ctx := multByAddCtx) env 0)
  have hgt : Std.Do.Triple (Exact.eval? multByAddCtx env
      (.op "gt" [Term.var "remaining", Term.nat 0]) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.bool (decide (0 < remaining)))) :=
    Peano.Exact.eval?_gt_nat_eq_spec hremaining hzero
  rw [Std.Do.Triple.iff]
  mstart
  mspec (Exact.callValues?_block_spec
    (ctx := multByAddCtx) (name := "multByAddCond")
    (args := ([Val.nat acc, Val.nat remaining, Val.nat x] : List (Val heapCtx)))
    (block := multByAddBlocks[2].2) (hM := rfl)
    (hblock := by rfl) (hargs := by rfl)
    (Q := someEqPost (Val.bool (decide (0 < remaining)))))
  mspec (Exact.evalInstrs?_nil_spec
    (Q := somePost fun value =>
      (someEqPost (Val.bool (decide (0 < remaining)))).1 (some value)))

theorem multByAddBody_eval? (acc remaining x : Nat) {loopResult : Val heapCtx}
    (hloop : Exact.EvaluatesApply multByAddCtx multByAddWhileRef
      ([Val.nat (acc + x), Val.nat (remaining - 1), Val.nat x] : List (Val heapCtx))
      loopResult) :
    Std.Do.Triple (Exact.callValues? multByAddCtx "multByAddBody"
        ([Val.nat acc, Val.nat remaining, Val.nat x, multByAddWhileRef] : List (Val heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost loopResult) := by
  let env0 := multByAddBlocks[3].2.entryEnv
    ([Val.nat acc, Val.nat remaining, Val.nat x, multByAddWhileRef] : List (Val heapCtx))
  let env1 := env0 ++ [("nextAcc", Val.nat (acc + x))]
  let env2 := env1 ++ [("nextRemaining", Val.nat (remaining - 1))]
  have hacc0 : Std.Do.Triple (Exact.eval? multByAddCtx env0
      (Term.var "acc") rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat acc)) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hx0 : Std.Do.Triple (Exact.eval? multByAddCtx env0
      (Term.var "x") rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat x)) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hnextAcc : Std.Do.Triple (Exact.eval? multByAddCtx env0
      (.op "add" [Term.var "acc", Term.var "x"]) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.nat (acc + x))) :=
    Peano.Exact.eval?_add_nat_eq_spec hacc0 hx0
  have hremaining1 : Std.Do.Triple (Exact.eval? multByAddCtx env1
      (Term.var "remaining") rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat remaining)) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hone1 : Std.Do.Triple (Exact.eval? multByAddCtx env1
      (Term.nat 1) rfl) (Std.Do.SPred.pure True)
      (someEqPost (Val.nat 1)) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.evaluates_nat (ctx := multByAddCtx) env1 1)
  have hnextRemaining : Std.Do.Triple (Exact.eval? multByAddCtx env1
      (.op "sub" [Term.var "remaining", Term.nat 1]) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.nat (remaining - 1))) :=
    Peano.Exact.eval?_sub_nat_eq_spec hremaining1 hone1
  have hfn2 : Std.Do.Triple (Exact.eval? multByAddCtx env2
      (Term.var "loop") rfl) (Std.Do.SPred.pure True)
      (someEqPost multByAddWhileRef) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hargs2 : Std.Do.Triple (Exact.evalList? multByAddCtx env2
      ([Term.var "nextAcc", Term.var "nextRemaining", Term.var "x"] : List (Term heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost
        ([Val.nat (acc + x), Val.nat (remaining - 1), Val.nat x] : List (Val heapCtx))) :=
    Exact.evalList?_eq_triple_of_evaluatesList
      (Exact.EvaluatesList.cons
        (Exact.EvaluatesTo.var_local (by rfl))
        (Exact.EvaluatesList.cons
          (Exact.EvaluatesTo.var_local (by rfl))
          (Exact.EvaluatesList.cons
            (Exact.EvaluatesTo.var_local (by rfl))
            Exact.EvaluatesList.nil)))
  have happ2 : Std.Do.Triple (Exact.eval? multByAddCtx env2
      (.app (Term.var "loop") [Term.var "nextAcc", Term.var "nextRemaining", Term.var "x"]) rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.app
        (Exact.evaluatesTo_of_eval?_triple hfn2)
        (Exact.evaluatesList_of_evalList?_triple hargs2)
        hloop)
  have happ2Block : Std.Do.Triple (Exact.eval? multByAddCtx env2
      multByAddBlocks[3].2.result rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) := by
    simpa [multByAddBlocks] using happ2
  have hnil : Std.Do.Triple (Exact.evalInstrs? multByAddCtx []
      multByAddBlocks[3].2.result env2 rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.evalInstrs?_nil_eq_spec happ2Block
  have htail : Std.Do.Triple (Exact.evalInstrs? multByAddCtx
      [Instr.ofTerm "nextRemaining" (.op "sub" [Term.var "remaining", Term.nat 1])]
      multByAddBlocks[3].2.result env1 rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.evalInstrs?_cons_eq_spec
      (instr := Instr.ofTerm "nextRemaining" (.op "sub" [Term.var "remaining", Term.nat 1]))
      hnextRemaining hnil
  have hinstrs : Std.Do.Triple (Exact.evalInstrs? multByAddCtx
      [Instr.ofTerm "nextAcc" (.op "add" [Term.var "acc", Term.var "x"]),
       Instr.ofTerm "nextRemaining" (.op "sub" [Term.var "remaining", Term.nat 1])]
      multByAddBlocks[3].2.result env0 rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.evalInstrs?_cons_eq_spec
      (instr := Instr.ofTerm "nextAcc" (.op "add" [Term.var "acc", Term.var "x"]))
      hnextAcc htail
  rw [Std.Do.Triple.iff]
  mstart
  mspec (Exact.callValues?_block_spec
    (ctx := multByAddCtx) (name := "multByAddBody")
    (args := ([Val.nat acc, Val.nat remaining, Val.nat x, multByAddWhileRef] : List (Val heapCtx)))
    (block := multByAddBlocks[3].2) (hM := rfl)
    (hblock := by rfl) (hargs := by rfl)
    (Q := someEqPost loopResult))

theorem multByAddLoop_eval? (x remaining acc : Nat) :
    Std.Do.Triple (Exact.callValues? multByAddCtx "multByAddLoop"
        ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.nat (acc + remaining * x))) := by
  let loopResult : Val heapCtx := Val.nat (acc + remaining * x)
  let env0 := multByAddBlocks[1].2.entryEnv
    ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
  let env1 := env0 ++ [("final", loopResult)]
  have hstateArgs : Std.Do.Triple (Exact.evalList? multByAddCtx env0
      ([Term.var "acc", Term.var "remaining", Term.var "x"] : List (Term heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost
        ([Val.nat acc, Val.nat remaining, Val.nat x] : List (Val heapCtx))) :=
    Exact.evalList?_eq_triple_of_evaluatesList
      (Exact.EvaluatesList.cons
        (Exact.EvaluatesTo.var_local (by rfl))
        (Exact.EvaluatesList.cons
          (Exact.EvaluatesTo.var_local (by rfl))
          (Exact.EvaluatesList.cons
            (Exact.EvaluatesTo.var_local (by rfl))
            Exact.EvaluatesList.nil)))
  have hwhile : Std.Do.Triple (Exact.eval? multByAddCtx env0
      (.op "while" [Term.var "multByAddCond", Term.var "multByAddBody",
        Term.var "acc", Term.var "remaining", Term.var "x"]) rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) := by
    mvcgen invariants
      · fun
          | _ :: remainingValue :: _ :: [] => ⟨remainingValue.asNat?.getD 0⟩
          | _ => ⟨0⟩
      · Std.Do.PostCond.noThrow fun
          | .inl args => Std.Do.SPred.pure
              (∃ k, k ≤ remaining ∧
                args = [Val.nat (acc + k * x), Val.nat (remaining - k), Val.nat x])
          | .inr value => Std.Do.SPred.pure (value = loopResult)
      with
      | vc2.typed =>
          intro args hI
          obtain ⟨k, _hk, hargs⟩ := hI
          subst args
          simp
      | vc3.step =>
          intro args ma hmeasure hI
          obtain ⟨k, hk, hargs⟩ := hI
          subst args
          have hma : ma = remaining - k := by
            simpa [Std.Do.WhileVariant.eval, Val.asNat?_nat] using
              congrArg ULift.down hmeasure
          subst ma
          by_cases hpos : 0 < remaining - k
          · apply Or.inl
            constructor
            · simpa [hpos] using multByAddCond_eval? (acc + k * x) (remaining - k) x
            · intro hnext
              apply multByAddBody_eval? (acc + k * x) (remaining - k) x
              apply hnext
                ([Val.nat ((acc + k * x) + x), Val.nat ((remaining - k) - 1), Val.nat x] :
                  List (Val heapCtx)) ((remaining - k) - 1)
              · simp [Std.Do.WhileVariant.eval, Val.asNat?_nat]
              · omega
              · refine ⟨k + 1, ?_, ?_⟩
                · omega
                · simp [Nat.succ_mul]
                  omega
          · apply Or.inr
            have hk_eq : k = remaining := by omega
            constructor
            · have hzero : remaining - k = 0 := by omega
              simpa [hzero] using multByAddCond_eval? (acc + k * x) (remaining - k) x
            · simp [loopResult, hk_eq]
      | vc4 =>
          simp at *
          exact ⟨0, Nat.zero_le remaining, by simp_all⟩
  have hfinal : Std.Do.Triple (Exact.eval? multByAddCtx env1
      (Term.var "final") rfl) (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.eval?_eq_triple_of_evaluatesTo
      (Exact.EvaluatesTo.var_local (by rfl))
  have hnil : Std.Do.Triple (Exact.evalInstrs? multByAddCtx []
      multByAddBlocks[1].2.result env1 rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.evalInstrs?_nil_eq_spec hfinal
  have hinstrs : Std.Do.Triple (Exact.evalInstrs? multByAddCtx
      [Instr.ofTerm "final" (.op "while" [Term.var "multByAddCond", Term.var "multByAddBody",
        Term.var "acc", Term.var "remaining", Term.var "x"])]
      multByAddBlocks[1].2.result env0 rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) :=
    Exact.evalInstrs?_cons_eq_spec
      (instr := Instr.ofTerm "final" (.op "while" [Term.var "multByAddCond", Term.var "multByAddBody",
        Term.var "acc", Term.var "remaining", Term.var "x"]))
      hwhile hnil
  have hcall : Std.Do.Triple (Exact.callValues? multByAddCtx "multByAddLoop"
      ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx)) rfl)
      (Std.Do.SPred.pure True) (someEqPost loopResult) := by
    rw [Std.Do.Triple.iff]
    mstart
    mspec (Exact.callValues?_block_spec
      (ctx := multByAddCtx) (name := "multByAddLoop")
      (args := ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx)))
      (block := multByAddBlocks[1].2) (hM := rfl)
      (hblock := by rfl) (hargs := by rfl)
      (Q := someEqPost loopResult))
  simpa [loopResult] using hcall

theorem multByAdd_values_eval? (x y : Nat) :
    Std.Do.Triple (Exact.callValues? multByAddCtx "multByAdd"
        ([Val.nat x, Val.nat y] : List (Val heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.nat (x * y))) := by
  mvcgen invariants
    · fun
        | _ :: remainingValue :: _ :: [] => ⟨remainingValue.asNat?.getD 0⟩
        | _ => ⟨0⟩
    · Std.Do.PostCond.noThrow fun
        | .inl args => Std.Do.SPred.pure
            (∃ k, k ≤ x ∧ args = [Val.nat (k * y), Val.nat (x - k), Val.nat y])
        | .inr value => Std.Do.SPred.pure (value = Val.nat (x * y))
    with
    | vc5.typed =>
        intro args hI
        obtain ⟨k, _hk, hargs⟩ := hI
        subst args
        simp
    | vc6.step =>
        intro args ma hmeasure hI
        obtain ⟨k, hk, hargs⟩ := hI
        subst args
        have hma : ma = x - k := by
          simpa [Std.Do.WhileVariant.eval, Val.asNat?_nat] using
            congrArg ULift.down hmeasure
        subst ma
        by_cases hpos : 0 < x - k
        · apply Or.inl
          constructor
          · simpa [hpos] using multByAddCond_eval? (k * y) (x - k) y
          · intro hnext
            apply multByAddBody_eval? (k * y) (x - k) y
            apply hnext
              ([Val.nat (k * y + y), Val.nat ((x - k) - 1), Val.nat y] :
                List (Val heapCtx)) ((x - k) - 1)
            · simp [Std.Do.WhileVariant.eval, Val.asNat?_nat]
            · omega
            · refine ⟨k + 1, ?_, ?_⟩
              · omega
              · simp [Nat.succ_mul]
                omega
        · apply Or.inr
          have hk_eq : k = x := by omega
          constructor
          · have hzero : x - k = 0 := by omega
            simpa [hzero] using multByAddCond_eval? (k * y) (x - k) y
          · simp [hk_eq]
    | vc7.pre.pre =>
        exact ⟨0, Nat.zero_le x, by simp⟩

theorem multByAdd_eval? (x y : Nat) :
    Std.Do.Triple (Exact.eval? multByAddCtx []
        (.call "multByAdd" [Term.nat x, Term.nat y]) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost (Val.nat (x * y))) := by
  have hvalues := multByAdd_values_eval? x y
  have hargs : Std.Do.Triple (Exact.evalList? multByAddCtx []
      ([Term.nat x, Term.nat y] : List (Term heapCtx)) rfl)
      (Std.Do.SPred.pure True)
      (someEqPost ([Val.nat x, Val.nat y] : List (Val heapCtx))) :=
    Exact.evalList?_eq_triple_of_evaluatesList
      (Exact.EvaluatesList.cons
        (Exact.evaluates_nat (ctx := multByAddCtx) [] x)
        (Exact.EvaluatesList.cons
          (Exact.evaluates_nat (ctx := multByAddCtx) [] y)
          Exact.EvaluatesList.nil))
  exact Exact.eval?_eq_triple_of_evaluatesTo
    (Exact.EvaluatesTo.call
      (Exact.evaluatesCallValues_of_callValues?_triple hvalues)
      (by rfl)
      (Exact.evaluatesList_of_evalList?_triple hargs))

/-- Pure total-correctness: monadic `EvaluatesCallValues` with trivial pre and equality post. -/
theorem multByAddLoop_eval (x remaining acc : Nat) :
    Zag.EvaluatesCallValues multByAddCtx "multByAddLoop"
      ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (acc + remaining * x))) := by
  change Exact.EvaluatesCallValues (hM := rfl) multByAddCtx "multByAddLoop"
    ([Val.nat x, Val.nat remaining, Val.nat acc] : List (Val heapCtx))
    (Val.nat (acc + remaining * x))
  exact Exact.evaluatesCallValues_of_callValues?_triple
    (multByAddLoop_eval? x remaining acc)

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
  exact Exact.evaluatesCallValues_of_callValues?_triple
    (multByAdd_values_eval? x y)

theorem multByAdd_eval_call (x y : Nat) :
    Exact.EvaluatesTo multByAddCtx [] (.call "multByAdd" [Term.nat x, Term.nat y])
      (Val.nat (x * y)) := by
  exact Exact.evaluatesTo_of_eval?_triple (multByAdd_eval? x y)

end Zag.Test.Autocorres.Examples
