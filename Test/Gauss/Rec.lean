import Test.Gauss
import Meta.Peano.Eval

namespace Zag.Test.Gauss.Rec

open Zag Zag.Lib.Peano
open Zag.Test.Gauss

def sumTo : Nat → Nat
| 0 => 0
| n + 1 => sumTo n + (n + 1)

def closedForm (n : Nat) : Nat := (n * (n + 1)).div 2

def lhsProgram (n : Nat) : Term natCtx := .call "gauss" [Term.nat n]

def rhsTerm (n : Nat) : Term natCtx :=
  .op "div" [.op "mul" [Term.nat n, .op "add" [Term.nat n, Term.nat 1]], Term.nat 2]

def gaussStatement (n : Nat) : Pr (Term natCtx) :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType gaussCtx [] (lhsProgram n) NatTy := by
  unfold lhsProgram
  refine Term.hasType.call (ctx := gaussCtx) (varCtx := []) (name := "gauss")
    (args := [Term.nat n]) (block := gaussBlocks[0].2) rfl rfl ?_
  intro idx
  cases idx using Fin.cases with
  | zero => exact Term.hasType.prim _
  | succ idx => exact Fin.elim0 idx

theorem rhsTerm_hasType (n : Nat) :
    Term.hasType gaussCtx [] (rhsTerm n) NatTy := by
  unfold rhsTerm
  have hn : Term.hasType gaussCtx [] (Term.nat n) NatTy := Term.hasType.prim _
  have h1 : Term.hasType gaussCtx [] (Term.nat 1) NatTy := Term.hasType.prim _
  have h2 : Term.hasType gaussCtx [] (Term.nat 2) NatTy := Term.hasType.prim _
  have hadd : Term.hasType gaussCtx [] (.op "add" [Term.nat n, Term.nat 1]) NatTy :=
    Term.hasType.binOp (ctx := gaussCtx) (name := "add") (argTy := NatTy) rfl hn h1
  have hmul : Term.hasType gaussCtx []
      (.op "mul" [Term.nat n, .op "add" [Term.nat n, Term.nat 1]]) NatTy :=
    Term.hasType.binOp (ctx := gaussCtx) (name := "mul") (argTy := NatTy) rfl hn hadd
  exact Term.hasType.binOp (ctx := gaussCtx) (name := "div") (argTy := NatTy) rfl hmul h2

/-- What the loop has added after `k` turns: `i + (i-1) + … + (i-k+1)`. Counting down is what
  the loop does, and stating the invariant that way keeps it free of truncated subtraction. -/
def sumDown (i : Nat) : Nat → Nat
| 0 => 0
| k + 1 => sumDown i k + (i - k)

theorem sumDown_succ (i k : Nat) :
    sumDown i (k + 1) = sumDown i k + (i - k) := by
  rfl

theorem sumDown_add_sumTo (i : Nat) :
    ∀ k, k ≤ i → sumDown i k + sumTo (i - k) = sumTo i := by
  intro k
  induction k with
  | zero => intro _; simp [sumDown]
  | succ k ih =>
      intro hk
      have hik : i - k = (i - (k + 1)) + 1 := by omega
      have hstep : sumTo (i - k) = sumTo (i - (k + 1)) + (i - k) := by
        rw [hik]; simp [sumTo]
      have hih := ih (by omega)
      simp only [sumDown]
      omega

/-- Counting all the way down is the same as counting up. -/
theorem sumDown_self (i : Nat) : sumDown i i = sumTo i := by
  simpa [sumTo] using sumDown_add_sumTo i i (Nat.le_refl i)

theorem loop_eval (i acc : Nat) :
    EvaluatesCall gaussCtx "loop" ([Val.nat i, Val.nat acc] : List (Val natCtx))
      (Val.nat (acc + sumTo i)) := by
  while_induction [natOpCtx, Op.fixed, gaussBlocks, sumDown, sumDown_succ, sumDown_self]
    (fun k args => args = [Val.nat (acc + sumDown i k), Val.nat (i - k)]) stopping_at i
    returning (Val.nat (acc + sumTo i))

theorem gauss_eval (n : Nat) :
    EvaluatesCall gaussCtx "gauss" ([Val.nat n] : List (Val natCtx)) (Val.nat (sumTo n)) := by
  evaluates_call [gaussBlocks]
  use_call [gaussBlocks] (loop_eval n 0)

theorem lhsProgram_eval_sumTo (n : Nat) (env : Env natCtx) :
    EvaluatesTo gaussCtx env (lhsProgram n) (Val.nat (sumTo n)) := by
  unfold lhsProgram
  refine EvaluatesTo.call (block := gaussBlocks[0].2) (hcall := gauss_eval n) ?_ ?_
  · rfl
  · evaluates_to_all [gaussBlocks]

theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
      calc
        2 * sumTo (n + 1) = 2 * (sumTo n + (n + 1)) := by simp [sumTo]
        _ = 2 * sumTo n + 2 * (n + 1) := by rw [Nat.left_distrib]
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 2) * (n + 1) := by rw [(Nat.add_mul n 2 (n + 1)).symm]
        _ = (n + 1) * (n + 2) := by rw [Nat.mul_comm]

theorem sumTo_eq_closed (n : Nat) : sumTo n = closedForm n := by
  unfold closedForm
  have h2 : Not ((2 : Nat) = 0) := by decide
  exact Nat.eq_div_of_mul_eq_right h2 (two_mul_sumTo n)

theorem lhsProgram_eval_rhs (n : Nat) (env : Env natCtx) :
    EvaluatesTo gaussCtx env (lhsProgram n) (Val.nat (closedForm n)) := by
  simpa [sumTo_eq_closed n] using lhsProgram_eval_sumTo n env

theorem rhsTerm_eval_rhs (n : Nat) (env : Env natCtx) :
    EvaluatesTo gaussCtx env (rhsTerm n) (Val.nat (closedForm n)) := by
  unfold rhsTerm closedForm
  evaluates 100 [natOpCtx, Op.fixed]

theorem gaussEq (n : Nat) :
    Term.eq gaussCtx [] NatTy (lhsProgram n) (rhsTerm n) :=
  term_eq_nat_of_eval (lhsProgram_hasType n) (rhsTerm_hasType n) fun env _ =>
    ⟨closedForm n, lhsProgram_eval_rhs n env, rhsTerm_eval_rhs n env⟩

theorem gaussProvable (n : Nat) :
    Pr.Provable gaussCtx [] [] (gaussStatement n) := by
  refine Pr.Provable.ofProof ?_
  change Term.eq gaussCtx (VarCtx.subst [] []) (Ty.subst [] NatTy)
    (Term.subst [] (lhsProgram n)) (Term.subst [] (rhsTerm n))
  simpa [VarCtx.subst, Peano.NatTy, NatTy, Ty.subst] using gaussEq n

example : Pr.Provable gaussCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

end Zag.Test.Gauss.Rec
