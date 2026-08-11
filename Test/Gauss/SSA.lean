import Lang.SSA
import Test.Gauss.Rec
import Lib.Peano

namespace Zag.Test.Gauss.SSA

open Zag.Lang.SSA
open Zag.Test.Gauss.Rec
open Zag.Lib.Peano

abbrev stateTys : List Ty := [NatTy, NatTy]
abbrev stateTy : Ty := .struct stateTys
abbrev bodyCtx : VarCtx := [stateTy, .func [stateTy] NatTy]

def iIdx : Fin stateTys.length := Fin.mk 0 (by decide)
def accIdx : Fin stateTys.length := Fin.mk 1 (by decide)

def iTerm : Term natCtx := .app (.structProj stateTys iIdx) [.var 0]
def accTerm : Term natCtx := .app (.structProj stateTys accIdx) [.var 0]
def condTerm : Term natCtx := .op "gt" [iTerm, Term.nat 0]
def nextITerm : Term natCtx := .app (.primFunc "sub") [iTerm, Term.nat 1]
def nextAccTerm : Term natCtx := .app (.primFunc "add") [accTerm, iTerm]
def nextStateTerm : Term natCtx := .app (.mkStruct stateTys) [nextITerm, nextAccTerm]
def yieldTerm : Term natCtx := .app (.var 1) [nextStateTerm]
def bodyTerm : Term natCtx := .ite condTerm yieldTerm accTerm

def loopTerm (i acc : Nat) : Term natCtx :=
  .recurse NatTy (.app (.mkStruct stateTys) [Term.nat i, Term.nat acc]) bodyTerm

def lhsSSA (n : Nat) : SSAExpr natCtx :=
  ssa% {
    zero := prim(0 : Nat);
    one := prim(1 : Nat);
    start := prim(n : Nat);
    acc0 := prim(0 : Nat);
    loop (i : Nat := start, acc : Nat := acc0) : Nat {
      cond := gt i zero;
      if cond {
        nextI := call sub [i, one];
        nextAcc := call add [acc, i];
        yield nextI, nextAcc
      } else {
        acc
      }
    }
  }

def lhsProgram (n : Nat) : Term natCtx :=
  (lhsSSA n).toTerm

def gaussStatement (n : Nat) : Pr (Term natCtx) :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)

def stateFields (i acc : Nat) : (idx : Fin stateTys.length) → Ty.type natCtx stateTys[idx]
| ⟨0, _⟩ => Ty.ofNat natCtx i
| ⟨1, _⟩ => Ty.ofNat natCtx acc
| ⟨n + 2, h⟩ => by
    have : n + 2 < 2 := by simpa [stateTys] using h
    omega

def stateVal (i acc : Nat) : Val natCtx :=
  Val.mk stateTy (cast (Ty.type.eq_5 natCtx stateTys).symm (stateFields i acc))

theorem evalMkStruct_state (i acc : Nat) :
    Term.evalMkStruct stateTys [Val.nat i, Val.nat acc] = some (stateVal i acc) := by
  simp [Term.evalMkStruct, valsAs?, stateVal, stateTys, finPiOption]
  congr
  funext idx
  cases idx with
  | mk val isLt =>
      cases val with
      | zero => rfl
      | succ val =>
          cases val with
          | zero => rfl
          | succ val => omega

def loopEnv (i acc : Nat) (env : List (Val natCtx)) : List (Val natCtx) :=
  env ++ [stateVal i acc, Term.motiveVal stateTy NatTy]

def loopRecCtx (env : List (Val natCtx)) : Term.MotiveCtx natCtx :=
  { body := bodyTerm, env := env, stateTy := stateTy, resultTy := NatTy }

noncomputable def loopBodyEval (i acc : Nat) : Option (Val natCtx) :=
  Term.evalGo peanoCtx [loopRecCtx []] (loopEnv i acc []) bodyTerm

theorem lhsProgram_shape (n : Nat) :
    lhsProgram n = loopTerm n 0 := by
  rfl

theorem bodyTerm_hasType : Term.hasType peanoCtx bodyCtx bodyTerm NatTy := by
  unfold bodyTerm yieldTerm nextStateTerm nextAccTerm nextITerm condTerm accTerm iTerm
    accIdx iIdx Term.ite Term.nat
  has_type

theorem loopTerm_hasType (i acc : Nat) : Term.hasType peanoCtx [] (loopTerm i acc) NatTy := by
  unfold loopTerm bodyTerm yieldTerm nextStateTerm nextAccTerm nextITerm condTerm accTerm
    iTerm accIdx iIdx Term.ite Term.nat
  has_type

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType peanoCtx [] (lhsProgram n) NatTy := by
  rw [lhsProgram_shape]
  exact loopTerm_hasType n 0

theorem loopTerm_eval_unfold (i acc : Nat) :
    Term.eval peanoCtx [] (loopTerm i acc) = loopBodyEval i acc := by
  conv =>
    lhs
    simp [loopTerm, stateTys, Term.eval, Term.evalGo, Term.evalList, Term.motiveVal,
      Term.nat, evalMkStruct_state]
  simp [loopBodyEval, loopEnv, loopRecCtx, Term.motiveVal, stateVal]

private theorem iTerm_eval (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv i acc []) iTerm = some (Val.nat i) := by
  unfold iTerm iIdx loopEnv
  rw [Term.evalGo.eq_def]
  simp [Term.evalGo, stateVal, stateFields, stateTy, stateTys, Val.as?, Val.nat, Ty.ofNat]

private theorem accTerm_eval (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv i acc []) accTerm = some (Val.nat acc) := by
  unfold accTerm accIdx loopEnv
  rw [Term.evalGo.eq_def]
  simp [Term.evalGo, stateVal, stateFields, stateTy, stateTys, Val.as?, Val.nat, Ty.ofNat]

private theorem get_gt : peanoCtx.opCtx.get? "gt" = some (Op.compare Val.primGt?) := by
  exact Peano.Model.gtOp

theorem cond_eval_zero (acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 acc []) condTerm =
      some (Val.bool false) := by
  unfold condTerm
  have h := Term.evalGo_op_compare (ctx := peanoCtx)
    (motives := [loopRecCtx []]) (env := loopEnv 0 acc [])
    (name := "gt") (cmp := Val.primGt?) (a := iTerm) (b := Term.nat 0)
    (va := Val.nat 0) (vb := Val.nat 0) get_gt (iTerm_eval 0 acc)
    (by simp [Term.evalGo, Term.nat]) rfl
  rw [h]
  simp [Val.primGt?, Val.primLt?, Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]

theorem cond_eval_succ (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) acc []) condTerm =
      some (Val.bool true) := by
  unfold condTerm
  have h := Term.evalGo_op_compare (ctx := peanoCtx)
    (motives := [loopRecCtx []]) (env := loopEnv (i + 1) acc [])
    (name := "gt") (cmp := Val.primGt?) (a := iTerm) (b := Term.nat 0)
    (va := Val.nat (i + 1)) (vb := Val.nat 0) get_gt (iTerm_eval (i + 1) acc)
    (by simp [Term.evalGo, Term.nat]) rfl
  rw [h]
  simp [Val.primGt?, Val.primLt?, Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]

private theorem nextITerm_eval_succ (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) acc []) nextITerm =
      some (Val.nat i) := by
  unfold nextITerm
  rw [Term.evalGo.eq_def]
  simp only
  rw [Term.evalList.eq_def]
  simp only [List.mapM, List.mapM.loop]
  rw [iTerm_eval]
  simp [Term.evalGo, Term.nat, PrimFunc.apply, PrimFunc.outTy, PrimFuncCtx.get?, peanoCtx,
    natFuncCtx, natBinaryFunc]

private theorem nextAccTerm_eval_succ (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) acc []) nextAccTerm =
      some (Val.nat (acc + (i + 1))) := by
  unfold nextAccTerm
  rw [Term.evalGo.eq_def]
  simp only
  rw [Term.evalList.eq_def]
  simp only [List.mapM, List.mapM.loop]
  rw [accTerm_eval, iTerm_eval]
  simp [PrimFunc.apply, PrimFunc.outTy, PrimFuncCtx.get?, peanoCtx, natFuncCtx, natBinaryFunc]

private theorem nextStateTerm_eval_succ (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) acc []) nextStateTerm =
      some (stateVal i (acc + (i + 1))) := by
  unfold nextStateTerm
  rw [Term.evalGo.eq_def]
  simp only
  rw [Term.evalList.eq_def]
  simp only [List.mapM, List.mapM.loop]
  rw [nextITerm_eval_succ, nextAccTerm_eval_succ]
  exact evalMkStruct_state i (acc + (i + 1))

theorem yield_eval_succ (i acc : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) acc []) yieldTerm =
      (do
        let result ← loopBodyEval i (acc + (i + 1))
        let resultRaw ← result.as? NatTy
        some (Val.mk NatTy resultRaw)) := by
  unfold yieldTerm
  rw [Term.evalGo.eq_def]
  simp only
  rw [show Term.MotiveCtx.findMotive (primCtx := natCtx) 1 [loopRecCtx []] =
      some (loopRecCtx [], [loopRecCtx []]) by
    simp [Term.MotiveCtx.findMotive, loopRecCtx]]
  rw [nextStateTerm_eval_succ]
  simp [Val.as?, stateVal, stateTy]
  change (loopBodyEval i (acc + (i + 1))).bind
      (fun result => (Val.as? NatTy result).bind fun resultRaw => some (Val.mk NatTy resultRaw)) = _
  rfl

theorem loopTerm_eval_sumTo (i acc : Nat) :
    Term.eval peanoCtx [] (loopTerm i acc) = some (Val.nat (acc + sumTo i)) := by
  induction i generalizing acc with
  | zero =>
      rw [loopTerm_eval_unfold]
      unfold loopBodyEval bodyTerm
      rw [Term.evalGo_ite, cond_eval_zero]
      simpa [sumTo] using accTerm_eval 0 acc
  | succ i ih =>
      rw [loopTerm_eval_unfold]
      unfold loopBodyEval bodyTerm
      rw [Term.evalGo_ite, cond_eval_succ]
      rw [yield_eval_succ]
      rw [← loopTerm_eval_unfold, ih]
      simp [sumTo]
      apply congrArg Val.nat
      omega

theorem lhsProgram_eval_sumTo (n : Nat) :
    Term.eval peanoCtx [] (lhsProgram n) = some (Val.nat (sumTo n)) := by
  rw [lhsProgram_shape, loopTerm_eval_sumTo]
  simp

theorem lhsProgram_eval_rhs (n : Nat) :
    Term.eval peanoCtx [] (lhsProgram n) = some (Val.nat (n * (n + 1) / 2)) := by
  rw [lhsProgram_eval_sumTo n, sumTo_eq_closed n]

theorem lhsProgram_subst_nil (n : Nat) :
    Term.subst [] (lhsProgram n) = lhsProgram n := by
  rw [lhsProgram_shape]
  simp [loopTerm, bodyTerm, condTerm, yieldTerm, nextStateTerm, nextITerm, nextAccTerm,
    iTerm, accTerm, stateTys, Term.nat]

theorem gaussProvable (n : Nat) :
    Pr.Provable peanoCtx [] [] (gaussStatement n) := by
  refine Pr.Provable.ofProof ?_
  change Term.eq peanoCtx [] (Ty.subst [] NatTy)
    (Term.subst [] (lhsProgram n)) (Term.subst [] (rhsTerm n))
  rw [lhsProgram_subst_nil n, rhsTerm_subst_nil n]
  simp [NatTy]
  exact Term.eq.mk
    (lhsProgram_hasType n)
    (rhsTerm_hasType n)
    (by
      intro env henv
      have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
      subst env
      rw [lhsProgram_eval_rhs n]
      rw [rhsTerm_eval_rhs n])

example : Pr.Provable peanoCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

/-! ### ssa proposition -/

def gaussGoalSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  .eq [] NatTy (lhsSSA n) (.ret (.raw (rhsTerm n)))

theorem gaussGoalSSA_toTerm (n : Nat) :
    (gaussGoalSSA n).toTerm? = some (gaussStatement n) := rfl

theorem gaussProvableSSA (n : Nat) : Language.Provable peanoCtx [] [] (gaussGoalSSA n) :=
  ⟨gaussStatement n, rfl, gaussProvable n⟩

def gaussStructuralSSA (n : Nat) :
    Refinement peanoCtx [] [] (gaussGoalSSA n) :=
  Tactic.raise (Pr.Refinement.structural (ctx := peanoCtx) (ctxTy := []) (ctxTerm := []))
    (gaussGoalSSA n)

def gaussConjunctionSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  .and (gaussGoalSSA n) (gaussGoalSSA n)

def inductionSSA : Tactic peanoCtx [] [] (SSAExpr natCtx) :=
  Tactic?.toTactic <| Tactic?.raise <|
    Pr.Induction.simpleInduction (ctxTy := []) (ctxTerm := []) succName succ_spec

def gaussInductionSSA (n : Nat) : Refinement peanoCtx [] [] (gaussGoalSSA n) :=
  inductionSSA (gaussGoalSSA n)

example (n : Nat) :
    (gaussStructuralSSA n).goals =
      [.eq [] NatTy (.ret (.raw (lhsProgram n))) (.ret (.raw (rhsTerm n)))] :=
  rfl

example (n : Nat) :
    (Tactic.raise (Pr.Refinement.structural (ctx := peanoCtx) (ctxTy := []) (ctxTerm := []))
      (gaussConjunctionSSA n)).goals.length = 2 := rfl

example (n : Nat) : (gaussInductionSSA n).goals.length = 2 := rfl

def nonInductiveSSA : Pr (SSAExpr natCtx) :=
  .hasType [] (.ret (.raw (Term.nat 0))) NatTy

example : (inductionSSA nonInductiveSSA).goals = [nonInductiveSSA] := rfl

def invalidSSA : SSAExpr natCtx := .yield []

def invalidGoalSSA : Pr (SSAExpr natCtx) := .hasType [] invalidSSA NatTy

example : invalidGoalSSA.toTerm? = none := rfl

example :
    (Tactic.raise (Pr.Refinement.structural (ctx := peanoCtx) (ctxTy := []) (ctxTerm := []))
      invalidGoalSSA).goals = [invalidGoalSSA] := rfl

example :
    Tactic?.raise (Pr.Induction.simpleInduction (ctx := peanoCtx) (ctxTy := []) (ctxTerm := [])
      succName succ_spec) invalidGoalSSA = none := rfl

end Zag.Test.Gauss.SSA
