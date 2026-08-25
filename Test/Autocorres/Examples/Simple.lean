import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Simple.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Simple.thy).
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple
open Zag.EvalTriple.Exact
open scoped Std.Do

private abbrev heapOpCtx := pureHeapOpCtx

def simpleGcdSpec (a b : Nat) : Nat :=
  if _h : a = 0 then b else simpleGcdSpec (b % a) a
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

abbrev simpleBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    max(x : Nat, y : Nat) : Nat {
      yGreater := op "lt"[x, y];
      ret if yGreater { y } else { x }
    },
    gcd(x : Nat, y : Nat) : Nat {
      ret call gcdLoop [x, y]
    },
    gcdLoop(a : Nat, b : Nat) : Nat {
      done := primEq a nat(0);
      ret if done { b } else {
        call gcdLoop [op "mod"[b, a], a]
      }
    }
  ]

theorem simpleBlocksValid : BlockCtx.Valid simpleBlocks := by
  valid_blocks [simpleBlocks]

abbrev simpleCtx : Ctx := mkPureCtx simpleBlocks simpleBlocksValid

theorem simpleCtx_wellTyped : Ctx.WellTyped simpleCtx := by
  typecheck_ctx

@[eval_semantic] theorem simple_evaluates_mod {env : Env heapCtx}
    {lhsTerm rhsTerm : Term heapCtx} {lhs rhs : Nat}
    (hlhs : EvaluatesTo simpleCtx env lhsTerm (Val.nat lhs))
    (hrhs : EvaluatesTo simpleCtx env rhsTerm (Val.nat rhs)) :
    EvaluatesTo simpleCtx env (.op "mod" [lhsTerm, rhsTerm]) (Val.nat (lhs % rhs)) := by
  refine EvaluatesTo.op_applyVals (oper := binaryNatOp Nat.mod) rfl
    (EvaluatesList.cons hlhs (EvaluatesList.cons hrhs EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, binaryNatOp, Op.ofVals, Op.Body.applyVals, Op.Body.eager]
  rfl

theorem simple_evaluates_ite_false {env : Env heapCtx}
    {conditionTerm thenTerm elseTerm : Term heapCtx} {thenValue value : Val heapCtx}
    (hcondition : EvaluatesTo simpleCtx env conditionTerm (Val.bool false))
    (hthen : EvaluatesTo simpleCtx env thenTerm thenValue)
    (helse : EvaluatesTo simpleCtx env elseTerm value) :
    EvaluatesTo simpleCtx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  refine EvaluatesTo.op_applyVals (oper := Op.ite) Peano.Model.iteOp
    (EvaluatesList.cons hcondition
      (EvaluatesList.cons hthen (EvaluatesList.cons helse EvaluatesList.nil))) ?_
  simp [Op.applyValsAt, Op.ite, Op.fixed, Op.Body.applyVals]

private theorem simple_max_eval_exact (x y : Nat) :
    Exact.EvaluatesCallValues simpleCtx "max" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Val.nat (max x y)) := by
  by_cases hxy : x < y
  · rw [Nat.max_eq_right (Nat.le_of_lt hxy)]
    evaluates_call 100 [heapOpCtx, Op.fixed, simpleBlocks, hxy]
  · rw [Nat.max_eq_left (Nat.le_of_not_gt hxy)]
    evaluates_call 100 [heapOpCtx, Op.fixed, simpleBlocks, hxy]

/-- The generated `max` block computes Lean's maximum, as in the upstream correctness lemma. -/
theorem simple_max_eval (x y : Nat) :
    Zag.EvaluatesCallValues simpleCtx "max" ([Val.nat x, Val.nat y] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (max x y))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using simple_max_eval_exact x y

/-- The pure Euclidean recurrence computes the mathematical gcd. -/
theorem simpleGcdSpec_eq_gcd (a b : Nat) : simpleGcdSpec a b = Nat.gcd a b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
      rw [simpleGcdSpec]
      split <;> rename_i hzero
      · subst a
        simp
      · rw [ih (b % a) (Nat.mod_lt _ (Nat.pos_of_ne_zero hzero))]
        exact (Nat.gcd_rec a b).symm

/-- Private Exact spine for the recursive Euclidean loop. -/
private theorem simple_gcdLoop_eval_exact (a b : Nat) :
    Exact.EvaluatesCallValues simpleCtx "gcdLoop"
      ([Val.nat a, Val.nat b] : List (Val heapCtx)) (Val.nat (simpleGcdSpec a b)) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
      rw [simpleGcdSpec]
      split <;> rename_i hzero
      · subst a
        evaluates_call 100 [heapOpCtx, Op.fixed, simpleBlocks]
      · have hrec := ih (b % a) (Nat.mod_lt _ (Nat.pos_of_ne_zero hzero)) a
        apply EvaluatesCallValues.of_evaluatesInstrs (block := simpleBlocks[2].2) <;> try rfl
        refine EvaluatesInstrs.cons (instrValue := Val.bool false) ?_ ?_
        · evaluates 100 [heapOpCtx, Op.fixed, simpleBlocks, hzero]
        apply EvaluatesInstrs.nil
        apply simple_evaluates_ite_false
        · exact EvaluatesTo.var_local (name := "done") (value := Val.bool false) (by rfl)
        · exact EvaluatesTo.var_local (name := "b") (value := Val.nat b) (by rfl)
        apply EvaluatesTo.call hrec rfl
        exact EvaluatesList.cons
          (simple_evaluates_mod
            (EvaluatesTo.var_local (name := "b") (value := Val.nat b) (by rfl))
            (EvaluatesTo.var_local (name := "a") (value := Val.nat a) (by rfl)))
          (EvaluatesList.cons
            (EvaluatesTo.var_local (name := "a") (value := Val.nat a) (by rfl))
            EvaluatesList.nil)

/-- The recursive IR block executes the source Euclidean loop and stops exactly when `a = 0`. -/
theorem simple_gcdLoop_eval (a b : Nat) :
    Zag.EvaluatesCallValues simpleCtx "gcdLoop"
      ([Val.nat a, Val.nat b] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (simpleGcdSpec a b))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using simple_gcdLoop_eval_exact a b

private theorem simple_gcd_eval_exact (a b : Nat) :
    Exact.EvaluatesCallValues simpleCtx "gcd" ([Val.nat a, Val.nat b] : List (Val heapCtx))
      (Val.nat (simpleGcdSpec a b)) := by
  evaluates_call 100 [heapOpCtx, Op.fixed, simpleBlocks]
  zspec_call 100 [heapOpCtx, Op.fixed, simpleBlocks] (simple_gcdLoop_eval_exact a b)

/-- The entry block executes the source loop from its original `(a, b)` state. -/
theorem simple_gcd_eval (a b : Nat) :
    Zag.EvaluatesCallValues simpleCtx "gcd" ([Val.nat a, Val.nat b] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (simpleGcdSpec a b))) := by
  simpa [Exact.EvaluatesCallValues, Exact.pre, Exact.post, Singleton.idPre, Singleton.idPost]
    using simple_gcd_eval_exact a b

/-- Universal executable correctness of the generated `gcd` block. -/
theorem simple_gcd_correct (a b : Nat) :
    Zag.EvaluatesCallValues simpleCtx "gcd" ([Val.nat a, Val.nat b] : List (Val heapCtx))
      (Singleton.idPre True)
      (Singleton.idPost (· = Val.nat (Nat.gcd a b))) := by
  simpa only [simpleGcdSpec_eq_gcd] using simple_gcd_eval a b

end Zag.Test.Autocorres.Examples
