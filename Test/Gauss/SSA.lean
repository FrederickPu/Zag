import Lang.SSA
import Test.Gauss.Rec

namespace Zag.Test.Gauss.SSA

open Zag.Lang.SSA
open Zag.Test.Gauss.Rec

abbrev stateTys : List Ty := [NatTy, NatTy]
abbrev stateTy : Ty := .struct stateTys
abbrev bodyCtx : VarCtx := [stateTy, .func [stateTy] NatTy]

def iIdx : Fin stateTys.length := Fin.mk 0 (by decide)
def accIdx : Fin stateTys.length := Fin.mk 1 (by decide)

def iTerm : Term natCtx := .app (.structProj stateTys iIdx) [.var 0]
def accTerm : Term natCtx := .app (.structProj stateTys accIdx) [.var 0]
def condTerm : Term natCtx := .primGt iTerm (Term.nat 0)
def nextITerm : Term natCtx := .app (.primFunc "sub") [iTerm, Term.nat 1]
def nextAccTerm : Term natCtx := .app (.primFunc "add") [accTerm, iTerm]
def nextStateTerm : Term natCtx := .app (.mkStruct stateTys) [nextITerm, nextAccTerm]
def yieldTerm : Term natCtx := .app (.var 1) [nextStateTerm]
def bodyTerm : Term natCtx := .ite condTerm yieldTerm accTerm

def loopTerm (i acc : Nat) : Term natCtx :=
  .recurse NatTy (.app (.mkStruct stateTys) [Term.nat i, Term.nat acc]) bodyTerm

def lhsProgram (n : Nat) : Term natCtx :=
  (ssa% {
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
  } : SSAExpr natCtx).toTerm

def gaussStatement (n : Nat) : Pr natCtx :=
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

def loopRecCtx (env : List (Val natCtx)) : Term.RecCtx natCtx :=
  { body := bodyTerm, env := env, stateTy := stateTy, resultTy := NatTy }

noncomputable def loopBodyEval (i acc : Nat) : Option (Val natCtx) :=
  Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv i acc []) bodyTerm

theorem lhsProgram_shape (n : Nat) :
    lhsProgram n = loopTerm n 0 := by
  rfl

theorem bodyTerm_hasType : Term.hasType natCtx natFuncCtx bodyCtx bodyTerm NatTy := by
  let program := Zag.Pr.MetaProgram.iterate (primCtx := natCtx) (primFuncCtx := natFuncCtx)
    (ctxTy := []) (ctxTerm := []) 30 (fun goal => Zag.Pr.MetaProgram.unifyType goal)
    (.hasType bodyCtx bodyTerm NatTy)
  have hclosed : program.goals = [] := by
    exact List.eq_nil_of_length_eq_zero (by native_decide +revert : program.goals.length = 0)
  have hprov := Zag.Pr.MetaProgram.toProvable program hclosed
  cases hprov with
  | ofProof proof =>
      simpa [Pr.interp, bodyTerm, condTerm, yieldTerm, nextStateTerm, nextITerm,
        nextAccTerm, iTerm, accTerm, stateTy, stateTys, Term.subst, Term.nat, Ty.subst]
        using proof

theorem loopTerm_hasType (i acc : Nat) : Term.hasType natCtx natFuncCtx [] (loopTerm i acc) NatTy := by
  unfold loopTerm
  refine Term.hasType.recurse ?_ bodyTerm_hasType
  refine Term.hasType.app Term.hasType.mkStruct rfl ?_
  intro idx
  cases idx with
  | mk val isLt =>
      cases val with
      | zero => exact natType i
      | succ val =>
          cases val with
          | zero => exact natType acc
          | succ _ =>
              simp at isLt
              omega

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType natCtx natFuncCtx [] (lhsProgram n) NatTy := by
  rw [lhsProgram_shape]
  exact loopTerm_hasType n 0

theorem loopTerm_eval_unfold (i acc : Nat) :
    Term.eval natCtx natFuncCtx [] (loopTerm i acc) = loopBodyEval i acc := by
  conv =>
    lhs
    simp [loopTerm, stateTys, Term.eval, Term.evalGo, Term.evalList, Term.motiveVal,
      Term.nat, evalMkStruct_state]
  simp [loopBodyEval, loopEnv, loopRecCtx, Term.motiveVal, stateVal]

theorem cond_eval_zero (acc : Nat) :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv 0 acc []) condTerm =
      some (Val.bool false) := by
  simp [loopEnv, condTerm, iTerm, stateTys, iIdx, Term.evalGo, Term.nat,
    Val.primGt?, Val.primLt?, stateVal, stateFields]

theorem cond_eval_succ (i acc : Nat) :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (i + 1) acc []) condTerm =
      some (Val.bool true) := by
  simp [loopEnv, condTerm, iTerm, stateTys, iIdx, Term.evalGo, Term.nat,
    Val.primGt?, Val.primLt?, stateVal, stateFields]

theorem yield_eval_succ (i acc : Nat) :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (i + 1) acc []) yieldTerm =
      (do
        let result ← loopBodyEval i (acc + (i + 1))
        let resultRaw ← result.as? NatTy
        some (Val.mk NatTy resultRaw)) := by
  conv =>
    lhs
    simp [loopEnv, yieldTerm, nextStateTerm, nextITerm, nextAccTerm, iTerm, accTerm,
      stateTys, iIdx, accIdx, Term.eval, Term.evalGo, Term.evalList,
      PrimFunc.apply, PrimFuncCtx.get?, natFuncCtx, natBinaryFunc, Term.nat,
      evalMkStruct_state, stateVal, stateFields]
  simp [loopBodyEval, loopEnv, loopRecCtx, natFuncCtx, natBinaryFunc, stateVal]

theorem loopTerm_eval_sumTo (i acc : Nat) :
    Term.eval natCtx natFuncCtx [] (loopTerm i acc) = some (Val.nat (acc + sumTo i)) := by
  induction i generalizing acc with
  | zero =>
      rw [loopTerm_eval_unfold]
      change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv 0 acc [])
        (.ite condTerm yieldTerm accTerm) = _
      simp [Term.evalGo, cond_eval_zero acc]
      simp [Term.evalGo, loopEnv, accTerm, stateTys, accIdx, stateVal, stateFields, sumTo]
  | succ i ih =>
      rw [loopTerm_eval_unfold]
      change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (i + 1) acc [])
        (.ite condTerm yieldTerm accTerm) = _
      simp [Term.evalGo, cond_eval_succ i acc]
      rw [yield_eval_succ]
      have hbody : loopBodyEval i (acc + (i + 1)) =
          some (Val.nat ((acc + (i + 1)) + sumTo i)) := by
        rw [← loopTerm_eval_unfold]
        exact ih (acc + (i + 1))
      rw [hbody]
      simp [sumTo, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem lhsProgram_eval_sumTo (n : Nat) :
    Term.eval natCtx natFuncCtx [] (lhsProgram n) = some (Val.nat (sumTo n)) := by
  rw [lhsProgram_shape, loopTerm_eval_sumTo]
  simp

theorem lhsProgram_eval_rhs (n : Nat) :
    Term.eval natCtx natFuncCtx [] (lhsProgram n) = some (Val.nat (n * (n + 1) / 2)) := by
  rw [lhsProgram_eval_sumTo n, sumTo_eq_closed n]

theorem lhsProgram_subst_nil (n : Nat) :
    Term.subst [] (lhsProgram n) = lhsProgram n := by
  rw [lhsProgram_shape]
  simp [loopTerm, bodyTerm, condTerm, yieldTerm, nextStateTerm, nextITerm, nextAccTerm,
    iTerm, accTerm, stateTys, Term.nat]

theorem gaussProvable (n : Nat) :
    Pr.Provable natCtx natFuncCtx [] [] (gaussStatement n) := by
  refine Pr.Provable.ofProof ?_
  change Term.eq natCtx natFuncCtx [] (Ty.subst [] NatTy)
    (Term.subst [] (lhsProgram n)) (Term.subst [] (rhsTerm n))
  rw [lhsProgram_subst_nil n, rhsTerm_subst_nil n]
  simp [NatTy, Ty.subst]
  exact Term.eq.mk
    (lhsProgram_hasType n)
    (rhsTerm_hasType n)
    (by
      intro env henv
      have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
      subst env
      rw [lhsProgram_eval_rhs n]
      rw [rhsTerm_eval_rhs n])

example : Pr.Provable natCtx natFuncCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

end Zag.Test.Gauss.SSA
