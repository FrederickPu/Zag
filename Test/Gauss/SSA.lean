import Test.Gauss.Rec

/-!
The standalone `Lang.SSA` frontend used by this test was removed when blocks became the core IR.
This file keeps the old Gauss SSA proof surface by treating the block term as the SSA expression
that frontend used to lower to.
-/

namespace Zag.Test.Gauss.SSA

open Zag Zag.Lib.Peano
open Zag.Test.Gauss

abbrev SSAExpr (primCtx : PrimitiveCtx) := Term primCtx

abbrev lhsSSA (n : Nat) : SSAExpr natCtx := Rec.lhsProgram n

abbrev lhsProgram (n : Nat) : Term natCtx := lhsSSA n

abbrev rhsTerm (n : Nat) : Term natCtx := Rec.rhsTerm n

abbrev gaussStatement (n : Nat) : Pr (Term natCtx) := Rec.gaussStatement n

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType gaussCtx [] (lhsProgram n) NatTy :=
  Rec.lhsProgram_hasType n

theorem lhsProgram_eval_rhs (n : Nat) (env : Env natCtx) :
    EvaluatesTo gaussCtx env (lhsProgram n) (Val.nat (Rec.closedForm n)) :=
  Rec.lhsProgram_eval_rhs n env

theorem gaussProvable (n : Nat) :
    Pr.Provable gaussCtx [] [] (gaussStatement n) :=
  Rec.gaussProvable n

example : Pr.Provable gaussCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

/-! ### SSA proposition compatibility -/

def gaussGoalSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  gaussStatement n

theorem gaussGoalSSA_toTerm (n : Nat) :
    (gaussGoalSSA n).toTerm? = some (gaussStatement n) := rfl

theorem gaussProvableSSA (n : Nat) : Language.Provable gaussCtx [] [] (gaussGoalSSA n) :=
  ⟨gaussStatement n, rfl, gaussProvable n⟩

def gaussConjunctionSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  .and (gaussGoalSSA n) (gaussGoalSSA n)

example (n : Nat) :
    Language.Provable gaussCtx [] [] (gaussConjunctionSSA n) := by
  refine ⟨.and (gaussStatement n) (gaussStatement n), rfl, ?_⟩
  cases gaussProvable n with
  | ofProof proof => exact Pr.Provable.ofProof ⟨proof, proof⟩

end Zag.Test.Gauss.SSA
