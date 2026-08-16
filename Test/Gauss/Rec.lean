import Test.Gauss
import Meta.Eval

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

theorem loop_eval (i acc : Nat) :
    EvaluatesCall gaussCtx "loop" ([Val.nat i, Val.nat acc] : List (Val natCtx))
      (Val.nat (acc + sumTo i)) := by
  induction i generalizing acc with
  | zero =>
      simp [sumTo]
      evaluates_call 300 [natOpCtx, gaussBlocks]
  | succ i ih =>
      have hrec : EvaluatesCall gaussCtx "loop"
          ([Val.nat i, Val.nat (acc + (i + 1))] : List (Val natCtx))
          (Val.nat (acc + sumTo (i + 1))) := by
        simpa [sumTo, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (acc + (i + 1))
      refine EvaluatesCall.of_evaluatesFrom ?_
      intro env base
      set_option linter.unusedSimpArgs false in
        simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
          BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
          natOpCtx, gaussBlocks]
      refine EvaluatesFrom.trans_stepN (fuel₀ := 9)
        (mid := (⟨.eval (.call "loop"
            [Term.op "sub" [Term.var "i", Term.nat 1],
             Term.op "add" [Term.var "acc", Term.var "i"]]),
          [("i", Val.nat (i + 1)), ("acc", Val.nat acc), ("cond", Val.bool true)],
            Frame.opBody (fun thenVal =>
              Op.Body.next false fun _ =>
                match thenVal with
                | some value => Op.Body.done value
                | none => Op.Body.fail)
              [Term.var "acc"]
              [("i", Val.nat (i + 1)), ("acc", Val.nat acc), ("cond", Val.bool true)] ::
            Frame.call "loop" env :: base⟩ : EvalState natCtx)) ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
            EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
            BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
            Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
            Term.nat, Term.bool, Term.ite, natOpCtx, gaussBlocks] <;>
            (first | rfl | funext z <;> cases z <;> rfl)
      refine EvaluatesFrom.call_then (block := gaussBlocks[1].2) (hcall := hrec) ?_ ?_ ?_
      · set_option linter.unusedSimpArgs false in
          simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
            EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
            Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
            Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
            natOpCtx, gaussBlocks] <;> rfl
      · evaluates_to_all 300 [natOpCtx, gaussBlocks]
      · intro scope
        refine EvaluatesFrom.trans_stepN (fuel₀ := 2)
          (mid := (⟨.ret (Val.nat (acc + sumTo (i + 1))), env, base⟩ : EvalState natCtx)) ?_ ?_
        · set_option linter.unusedSimpArgs false in
            simp +arith [EvalState.stepN, EvalState.step, EvalState.driveOp,
              EvalState.enterInstrs, EvalState.enterBlock, OpCtx.get?, BlockCtx.get?,
              BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Peano.opCtx, Op.natBinary,
              Op.natUnary, Op.compare, Op.eq, Op.ite, Op.ofVals, Op.Body.eager,
              Term.nat, Term.bool, Term.ite, natOpCtx, gaussBlocks] <;> rfl
        exact EvaluatesFrom.done

theorem gauss_eval (n : Nat) :
    EvaluatesCall gaussCtx "gauss" ([Val.nat n] : List (Val natCtx)) (Val.nat (sumTo n)) := by
  refine EvaluatesCall.of_evaluatesFrom ?_
  intro env base
  set_option linter.unusedSimpArgs false in
    simp +arith [EvalState.enterInstrs, EvalState.enterBlock, BlockCtx.get?,
      BlockCtx.Raw.get?, Scope.get?, Block.entryEnv, Term.nat, Term.bool, Term.ite,
      natOpCtx, gaussBlocks]
  have hloop : EvaluatesCall gaussCtx "loop"
      ([Val.nat n, Val.nat 0] : List (Val natCtx)) (Val.nat (sumTo n)) := by
    simpa using loop_eval n 0
  refine EvaluatesFrom.call_then (block := gaussBlocks[1].2) (hcall := hloop) ?_ ?_ ?_
  · set_option linter.unusedSimpArgs false in
      simp +arith [EvalState.step, EvalState.driveOp, EvalState.enterInstrs,
        EvalState.enterBlock, OpCtx.get?, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?,
        Block.entryEnv, Peano.opCtx, Op.natBinary, Op.natUnary, Op.compare,
        Op.eq, Op.ite, Op.ofVals, Op.Body.eager, Term.nat, Term.bool, Term.ite,
        natOpCtx, gaussBlocks] <;> rfl
  · evaluates_to_all 300 [natOpCtx, gaussBlocks]
  · intro scope
    refine EvaluatesFrom.step
      (next := (⟨.ret (Val.nat (sumTo n)), env, base⟩ : EvalState natCtx)) ?_
      EvaluatesFrom.done
    simp [EvalState.step]

theorem lhsProgram_eval_sumTo (n : Nat) (env : Env natCtx) :
    EvaluatesTo gaussCtx env (lhsProgram n) (Val.nat (sumTo n)) := by
  unfold lhsProgram
  refine EvaluatesTo.call (block := gaussBlocks[0].2) (hcall := gauss_eval n) ?_ ?_
  · rfl
  · evaluates_to_all 20 [natOpCtx, gaussBlocks]

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
  evaluates 100 [natOpCtx, gaussBlocks]

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
