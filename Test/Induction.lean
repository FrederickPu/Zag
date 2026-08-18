import Test.Autocorres.Examples.Plus

/-!
Zag proving a fact about itself.

`Plus.lean` has Lean evaluate `plusLoop`; this file has *Zag* state `plusLoop x n = x + n` as a
proposition of its own and derive it from `Pr.Induction`'s rule, with Lean discharging only the
base and step. There is no counterpart to any of this in the upstream `plus.thy`, which is why
it lives here rather than alongside the program.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.Pr.Induction

/-! ### the same fact, proved inside Zag by induction

  Above, Lean evaluates the program. Here Zag states `plusLoop x n = x + n` as a proposition of
  its own and derives it from `Pr.Induction`'s rule; Lean only discharges the base and step. -/

theorem plusSuccSpec : SuccSpec plusCtx "succ" where
  hasType_op := fun _ _ ht => Term.hasType.unOp rfl ht
  eval_succ := fun _ _ _ ht => by
    simpa using (evaluates_natUnary (ctx := plusCtx) (name := "succ") (f := Nat.succ)
      (Peano.Model.succOp (ctx := plusCtx)) ht)

def plusLoopTerm (x : Nat) (t : Term heapCtx) : Term heapCtx := .call "plusLoop" [Term.nat x, t]

def plusAddTerm (x : Nat) (t : Term heapCtx) : Term heapCtx := .op "add" [Term.nat x, t]

def plusLoopStatement (x y : Nat) : Pr (Term heapCtx) :=
  .eq [] Peano.NatTy (plusLoopTerm x (Term.nat y)) (plusAddTerm x (Term.nat y))

def plusLoopPredicate (x : Nat) : Pr (Term heapCtx) :=
  .eq [] Peano.NatTy (plusLoopTerm x (.var "n")) (plusAddTerm x (.var "n"))

attribute [local simp] plusLoopTerm plusAddTerm plusLoopStatement plusLoopPredicate

theorem plusLoopStatement_eq (x y : Nat) :
    plusLoopStatement x y = Pr.Induction.instantiate "n" (Term.nat y) (plusLoopPredicate x) := rfl

theorem plusLoopTerm_hasType {varCtx : VarCtx} {x : Nat} {t : Term heapCtx}
    (ht : Term.hasType plusCtx varCtx t Peano.NatTy) :
    Term.hasType plusCtx varCtx (plusLoopTerm x t) Peano.NatTy :=
  Term.hasType.call (ctx := plusCtx) (varCtx := varCtx) (name := "plusLoop")
    (args := [Term.nat x, t]) (block := plusBlocks[1].2) rfl rfl (by
      intro idx
      cases idx using Fin.cases with
      | zero => exact Term.hasType.prim _
      | succ idx =>
          cases idx using Fin.cases with
          | zero => exact ht
          | succ idx => exact Fin.elim0 idx)

theorem plusAddTerm_hasType {varCtx : VarCtx} {x : Nat} {t : Term heapCtx}
    (ht : Term.hasType plusCtx varCtx t Peano.NatTy) :
    Term.hasType plusCtx varCtx (plusAddTerm x t) Peano.NatTy :=
  Term.hasType.binOp (argTy := Peano.NatTy) rfl (Term.hasType.prim _) ht

/-- The statement `plusLoop x t = x + t`, for any `t` that evaluates to a `Nat`. -/
theorem plusLoop_eq_of_arg_nat (x : Nat) {t : Term heapCtx}
    (ht : Term.hasType plusCtx [] t Peano.NatTy)
    (heval : ∀ env : Env heapCtx, env.Models [] → ∃ n : Nat,
      EvaluatesTo plusCtx env t (Val.nat n)) :
    Term.eq plusCtx [] Peano.NatTy (plusLoopTerm x t) (plusAddTerm x t) :=
  term_eq_nat_of_eval (plusLoopTerm_hasType ht) (plusAddTerm_hasType ht) fun env henv =>
    match heval env henv with
    | ⟨n, hn⟩ =>
        let hnatx : EvaluatesTo plusCtx env (Term.nat x) (Val.nat x) :=
          Pr.Induction.eval_natLit (ctx := plusCtx) env x
        let hblock : plusCtx.blockCtx.get? "plusLoop" = some plusBlocks[1].2 := by
          set_option linter.unusedSimpArgs false in
            simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, plusCtx, plusBlocks]
        ⟨x + n,
          by
            unfold plusLoopTerm
            exact EvaluatesTo.call (block := plusBlocks[1].2)
              (hcall := plusLoop_eval x n) hblock
              (EvaluatesToAll.cons hnatx (EvaluatesToAll.cons hn EvaluatesToAll.nil)),
          by
            unfold plusAddTerm
            exact evaluates_natBinary (ctx := plusCtx) (name := "add") (f := Nat.add)
              (Peano.Model.addOp (ctx := plusCtx)) hnatx hn⟩

theorem plusLoopBaseProvable (x : Nat) :
    Pr.Provable plusCtx [] [] (Pr.Induction.instantiate "n" (Term.nat 0) (plusLoopPredicate x)) := by
  rw [← plusLoopStatement_eq x 0]
  refine Pr.Provable.ofProof ?_
  exact_reflected plusLoop_eq_of_arg_nat x (Term.hasType.prim _)
    (fun env _ => ⟨0, Pr.Induction.eval_natLit (ctx := plusCtx) env 0⟩)

theorem plusLoopStepProvable (x : Nat) :
    Pr.Provable plusCtx [] [] (Pr.Induction.natStepGoal "n" "n_next" "succ" (plusLoopPredicate x)) := by
  open_reflected_provable
  intro nTerm hn y hy hsucc _ih
  exact_reflected plusLoop_eq_of_arg_nat x hy
    (eval_nat_of_reflected_natUnary_eq (ctx := plusCtx) (name := "succ") (f := Nat.succ)
      rfl hsucc)

def plusLoopInductionProgram (x y : Nat) :
    PrRefinement plusCtx [] [] (plusLoopStatement x y) :=
  Pr.Induction.natInductionWithPredicate "succ" plusSuccSpec (plusLoopStatement x y)
    (plusLoopPredicate x) "n" "n_next" y (by decide) (by rfl)
    (by
      change ¬ ("n_next" ∈ (["n", "n"] : List String))
      decide)
    (plusLoopStatement_eq x y)

theorem plusLoopProvable (x y : Nat) : Pr.Provable plusCtx [] [] (plusLoopStatement x y) := by
  applyRefinement (plusLoopInductionProgram x y)
  · cases plusLoopBaseProvable x with | ofProof proof => exact proof
  · cases plusLoopStepProvable x with | ofProof proof => exact proof

example : Pr.Provable plusCtx [] [] (plusLoopStatement 7 100) := plusLoopProvable 7 100

end Zag.Test.Autocorres.Examples
