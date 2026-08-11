import Meta.Induction
import Meta.UnifyType
import Lib.Peano

namespace Zag.Test.Gauss.Rec

open Zag.Lib.Peano

def sumTo : Nat → Nat
| 0 => 0
| n + 1 => sumTo n + (n + 1)

theorem natType {varCtx : VarCtx} (n : Nat) :
    Term.hasType peanoCtx varCtx (Term.nat n) NatTy :=
  Term.hasType.prim (Ty.ofNat peanoCtx.primCtx n)

abbrev bodyCtx : VarCtx := [NatTy, .func [NatTy] NatTy]

def iTerm : Term natCtx := term% { var(0) }
def condTerm : Term natCtx := term% { primGt raw(iTerm) nat(0) }
def prevTerm : Term natCtx := term% { call func(sub) [raw(iTerm), nat(1)] }
def recurseTerm : Term natCtx := term% { call var(1) [raw(prevTerm)] }
def stepTerm : Term natCtx := term% { call func(add) [raw(recurseTerm), raw(iTerm)] }
def bodyTerm : Term natCtx := term% { if raw(condTerm) { raw(stepTerm) } else { nat(0) } }

def lhsProgram (n : Nat) : Term natCtx :=
  term% { recurse Nat from nat(n) { raw(bodyTerm) } }

def rhsTerm (n : Nat) : Term natCtx :=
  term% { call func(div) [call func(mul) [nat(n), call func(add) [nat(n), nat(1)]], nat(2)] }

def gaussStatement (n : Nat) : Pr (Term natCtx) :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)

def loopEnv (i : Nat) (env : List (Val natCtx)) : List (Val natCtx) :=
  env ++ [Val.nat i, Term.motiveVal NatTy NatTy]

def loopRecCtx (env : List (Val natCtx)) : Term.MotiveCtx natCtx :=
  { body := bodyTerm, env := env, stateTy := NatTy, resultTy := NatTy }

noncomputable def loopBodyEval (i : Nat) (env : List (Val natCtx)) : Option (Val natCtx) :=
  Term.evalGo peanoCtx [loopRecCtx env] (loopEnv i env) bodyTerm

private theorem addFunc_hasType_aux {varCtx : VarCtx} :
    Term.hasType peanoCtx varCtx (.primFunc "add") (.func [NatTy, NatTy] NatTy) := by
  exact Term.hasType.primFunc (idx := ⟨0, by decide⟩)

theorem bodyTerm_hasType : Term.hasType peanoCtx bodyCtx bodyTerm NatTy := by
  unfold bodyTerm stepTerm recurseTerm prevTerm condTerm iTerm Term.ite Term.nat
  has_type

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType peanoCtx [] (lhsProgram n) NatTy := by
  unfold lhsProgram bodyTerm stepTerm recurseTerm prevTerm condTerm iTerm Term.ite Term.nat
  has_type

theorem addFunc_hasType {varCtx : VarCtx} :
    Term.hasType peanoCtx varCtx (.primFunc "add") (.func [NatTy, NatTy] NatTy) :=
  addFunc_hasType_aux

theorem mulFunc_hasType {varCtx : VarCtx} :
    Term.hasType peanoCtx varCtx (.primFunc "mul") (.func [NatTy, NatTy] NatTy) := by
  exact Term.hasType.primFunc (idx := ⟨2, by decide⟩)

theorem divFunc_hasType {varCtx : VarCtx} :
    Term.hasType peanoCtx varCtx (.primFunc "div") (.func [NatTy, NatTy] NatTy) := by
  exact Term.hasType.primFunc (idx := ⟨3, by decide⟩)

theorem natBinaryApp_hasType {varCtx : VarCtx} {fn lhs rhs : Term natCtx}
    (hfn : Term.hasType peanoCtx varCtx fn (.func [NatTy, NatTy] NatTy))
    (hlhs : Term.hasType peanoCtx varCtx lhs NatTy)
    (hrhs : Term.hasType peanoCtx varCtx rhs NatTy) :
    Term.hasType peanoCtx varCtx (.app fn [lhs, rhs]) NatTy := by
  refine Term.hasType.app hfn rfl ?_
  intro idx
  cases idx using Fin.cases with
  | zero => exact hlhs
  | succ idx =>
      cases idx using Fin.cases with
      | zero => exact hrhs
      | succ idx => exact Fin.elim0 idx

theorem rhsTerm_hasType (n : Nat) :
    Term.hasType peanoCtx [] (rhsTerm n) NatTy := by
  unfold rhsTerm Term.nat
  has_type

theorem lhsProgram_subst_nil (n : Nat) :
    Term.subst [] (lhsProgram n) = lhsProgram n := by
  simp [lhsProgram, bodyTerm, stepTerm, recurseTerm, prevTerm, condTerm, iTerm, Term.nat]

theorem rhsTerm_subst_nil (n : Nat) :
    Term.subst [] (rhsTerm n) = rhsTerm n := by
  simp [rhsTerm, Term.nat]

theorem lhsProgram_eval_unfold (i : Nat) :
    Term.eval peanoCtx [] (lhsProgram i) = loopBodyEval i [] := by
  conv =>
    lhs
    simp [lhsProgram, Term.eval, Term.evalGo, Term.motiveVal, Term.nat]
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv i []) bodyTerm =
    loopBodyEval i []
  rfl

private theorem get_gt : peanoCtx.opCtx.get? "gt" = some (Op.compare Val.primGt?) := by
  exact Peano.Model.gtOp

theorem cond_eval_zero :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 []) condTerm =
      some (Val.bool false) := by
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 [])
      (.op "gt" [.var 0, Term.nat 0]) = some (Val.bool false)
  have ha : Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 []) (.var 0) =
      some (Val.nat 0) := by simp [Term.evalGo, loopEnv]
  have hb : Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 []) (Term.nat 0) =
      some (Val.nat 0) := by simp [Term.evalGo, Term.nat, loopEnv]
  have h := Term.evalGo_op_compare (ctx := peanoCtx)
    (motives := [loopRecCtx []]) (env := loopEnv 0 [])
    (name := "gt") (cmp := Val.primGt?) (a := .var 0) (b := Term.nat 0)
    (va := Val.nat 0) (vb := Val.nat 0) get_gt ha hb rfl
  rw [h]
  simp [Val.primGt?, Val.primLt?, Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]

theorem cond_eval_succ (i : Nat) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) []) condTerm =
      some (Val.bool true) := by
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) [])
      (.op "gt" [.var 0, Term.nat 0]) = some (Val.bool true)
  have ha : Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) []) (.var 0) =
      some (Val.nat (i + 1)) := by simp [Term.evalGo, loopEnv]
  have hb : Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) []) (Term.nat 0) =
      some (Val.nat 0) := by simp [Term.evalGo, Term.nat, loopEnv]
  have h := Term.evalGo_op_compare (ctx := peanoCtx)
    (motives := [loopRecCtx []]) (env := loopEnv (i + 1) [])
    (name := "gt") (cmp := Val.primGt?) (a := .var 0) (b := Term.nat 0)
    (va := Val.nat (i + 1)) (vb := Val.nat 0) get_gt ha hb rfl
  rw [h]
  simp [Val.primGt?, Val.primLt?, Val.asNat?, Val.as?, Val.nat, Ty.toNat, Ty.ofNat]

theorem recurse_eval_succ (i V : Nat)
    (hbody : loopBodyEval i [] = some (Val.nat V)) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) []) recurseTerm =
      some (Val.nat V) := by
  change Term.evalGo peanoCtx [loopRecCtx []]
      [Val.nat (i + 1), Term.motiveVal NatTy NatTy]
      (.app (.var 1) [prevTerm]) = some (Val.nat V)
  unfold prevTerm iTerm loopRecCtx
  rw [Term.evalGo.eq_def]
  simp [Term.evalGo, Term.evalList, PrimFunc.apply, PrimFunc.outTy, PrimFuncCtx.get?, peanoCtx,
    natFuncCtx, natBinaryFunc, Term.nat, List.mapM, List.mapM.loop]
  change (loopBodyEval i []).bind
      (fun result => (Val.as? NatTy result).bind fun resultRaw => some (Val.mk NatTy resultRaw)) =
    some (Val.nat V)
  rw [hbody]
  simp

theorem step_eval_succ (i V : Nat)
    (hbody : loopBodyEval i [] = some (Val.nat V)) :
    Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (i + 1) []) stepTerm =
      some (Val.nat (V + (i + 1))) := by
  have hrec := recurse_eval_succ i V hbody
  unfold stepTerm iTerm
  rw [Term.evalGo.eq_def]
  simp only
  rw [Term.evalList.eq_def]
  simp only
  simp only [List.mapM, List.mapM.loop]
  rw [hrec]
  simp [loopEnv, Term.evalGo, PrimFunc.apply, PrimFunc.outTy, PrimFuncCtx.get?, peanoCtx,
    natFuncCtx, natBinaryFunc]

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

theorem sumTo_eq_closed (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  have h2 : Not ((2 : Nat) = 0) := by decide
  exact Nat.eq_div_of_mul_eq_right h2 (two_mul_sumTo n)

theorem closedForm_succ (k : Nat) :
    k * (k + 1) / 2 + (k + 1) = (k + 1) * (k + 2) / 2 := by
  rw [← sumTo_eq_closed k, ← sumTo_eq_closed (k + 1)]
  rfl

theorem gaussEq_provable_iff {lhs rhs : Term natCtx} :
    Pr.Provable peanoCtx [] [] (.eq [] NatTy lhs rhs) ↔
      Term.eq peanoCtx [] NatTy lhs rhs := by
  constructor
  · intro h
    cases h with
    | ofProof proof => simpa [Pr.interp, NatTy, Ty.subst] using proof
  · intro h
    exact Pr.Provable.ofProof (by simpa [Pr.interp, NatTy, Ty.subst] using h)

theorem rhsTerm_eval_rhs (n : Nat) :
    Term.eval peanoCtx [] (rhsTerm n) = some (Val.nat (n * (n + 1) / 2)) := by
  simp [rhsTerm, Term.eval, Term.evalGo, Term.evalList,
    PrimFunc.apply, PrimFunc.outTy, PrimFuncCtx.get?, natFuncCtx, natBinaryFunc, Term.nat]
  rfl

def lhsProgramOf (t : Term natCtx) : Term natCtx :=
  .recurse NatTy t bodyTerm

def rhsTermOf (t : Term natCtx) : Term natCtx :=
  term% { call func(div) [call func(mul) [raw(t), call func(add) [raw(t), nat(1)]], nat(2)] }

theorem lhsProgram_eq_lhsProgramOf (n : Nat) : lhsProgram n = lhsProgramOf (Term.nat n) := rfl

theorem rhsTerm_eq_rhsTermOf (n : Nat) : rhsTerm n = rhsTermOf (Term.nat n) := rfl

theorem lhsProgramOf_hasType {t : Term natCtx} (ht : Term.hasType peanoCtx [] t NatTy) :
    Term.hasType peanoCtx [] (lhsProgramOf t) NatTy := by
  unfold lhsProgramOf
  exact Term.hasType.recurse ht bodyTerm_hasType

theorem rhsTermOf_hasType {t : Term natCtx} (ht : Term.hasType peanoCtx [] t NatTy) :
    Term.hasType peanoCtx [] (rhsTermOf t) NatTy := by
  unfold rhsTermOf
  exact natBinaryApp_hasType divFunc_hasType
    (natBinaryApp_hasType mulFunc_hasType ht
      (natBinaryApp_hasType addFunc_hasType ht (natType 1)))
    (natType 2)

theorem lhsProgramOf_eval_unfold {t : Term natCtx} {k : Nat}
    (ht : Term.eval peanoCtx [] t = some (Val.nat k)) :
    Term.eval peanoCtx [] (lhsProgramOf t) = loopBodyEval k [] := by
  have ht' : Term.evalGo peanoCtx [] [] t = some (Val.nat k) := ht
  conv =>
    lhs
    simp [lhsProgramOf, Term.eval, Term.evalGo, Term.motiveVal, ht']
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv k []) bodyTerm =
    loopBodyEval k []
  rfl

theorem lhsProgramOf_congr {a b : Term natCtx}
    (h : Term.evalGo peanoCtx [] [] a = Term.evalGo peanoCtx [] [] b) :
    Term.eval peanoCtx [] (lhsProgramOf a) = Term.eval peanoCtx [] (lhsProgramOf b) := by
  unfold lhsProgramOf Term.eval
  simp only [Term.evalGo, h]

theorem rhsTermOf_congr {a b : Term natCtx}
    (h : Term.evalGo peanoCtx [] [] a = Term.evalGo peanoCtx [] [] b) :
    Term.eval peanoCtx [] (rhsTermOf a) = Term.eval peanoCtx [] (rhsTermOf b) := by
  unfold rhsTermOf Term.eval
  simp [Term.evalGo, Term.evalList, h]

theorem gaussEq_provable_congr {a b : Term natCtx}
    (hta : Term.hasType peanoCtx [] a NatTy)
    (hab : Term.evalGo peanoCtx [] [] a = Term.evalGo peanoCtx [] [] b)
    (h : Pr.Provable peanoCtx [] [] (.eq [] NatTy (lhsProgramOf b) (rhsTermOf b))) :
    Pr.Provable peanoCtx [] [] (.eq [] NatTy (lhsProgramOf a) (rhsTermOf a)) := by
  rw [gaussEq_provable_iff] at h ⊢
  refine Term.eq.mk (lhsProgramOf_hasType hta) (rhsTermOf_hasType hta) ?_
  intro env henv
  have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
  subst hnil
  rw [lhsProgramOf_congr hab, rhsTermOf_congr hab, h.eq [] rfl]

def gaussPredicate : Pr (Term natCtx) :=
  .eq [] NatTy
    (.recurse NatTy (.var 0) (Pr.Induction.weakenTermAt 0 bodyTerm))
    (.app (.primFunc "div")
      [(.app (.primFunc "mul") [(.var 0), (.app (.primFunc "add") [(.var 0), Term.nat 1])]),
       Term.nat 2])

theorem gaussPredicate_instantiate_eq (t : Term natCtx) :
    Pr.Induction.instantiateTermAt 0 gaussPredicate t =
      .eq [] NatTy (lhsProgramOf t) (rhsTermOf t) := by
  simp [gaussPredicate, lhsProgramOf, rhsTermOf,
    Pr.Induction.instantiateTermAt, Pr.Induction.instantiateTermInTerm,
    Pr.Induction.instantiateTermInTerm_weakenTermAt, Term.nat]

theorem gaussStatement_eq (n : Nat) :
    gaussStatement n = Pr.Induction.instantiateTermAt 0 gaussPredicate (Term.nat n) := by
  rw [gaussPredicate_instantiate_eq, gaussStatement, lhsProgram_eq_lhsProgramOf,
    rhsTerm_eq_rhsTermOf]

theorem gaussPredicate_quantifierFree :
    Pr.Induction.quantifierFree gaussPredicate = true := rfl

theorem gaussPredicate_congr {t : Term natCtx} {k : Nat}
    (ht : Term.hasType peanoCtx [] t (.prim "Nat"))
    (hte : Term.eval peanoCtx [] t = some (Val.nat k)) :
    Pr.Provable peanoCtx [] []
        (Pr.Induction.instantiateTermAt 0 gaussPredicate t) ↔
      Pr.Provable peanoCtx [] [] (gaussStatement k) := by
  rw [gaussPredicate_instantiate_eq, gaussStatement, lhsProgram_eq_lhsProgramOf,
    rhsTerm_eq_rhsTermOf]
  have hte' : Term.evalGo peanoCtx [] [] t = some (Val.nat k) := hte
  have hnat' : Term.evalGo peanoCtx [] [] (Term.nat k) = some (Val.nat k) := by
    simp [Term.evalGo, Term.nat]
  constructor
  · exact gaussEq_provable_congr (natType k) (hnat'.trans hte'.symm)
  · exact gaussEq_provable_congr ht (hte'.trans hnat'.symm)

theorem gaussBaseCase :
    Pr.Provable peanoCtx [] [] (gaussStatement 0) := by
  rw [gaussStatement, gaussEq_provable_iff]
  refine Term.eq.mk (lhsProgram_hasType 0) (rhsTerm_hasType 0) ?_
  intro env henv
  have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
  subst hnil
  rw [lhsProgram_eval_unfold]
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv 0 [])
    (Term.ite condTerm stepTerm (Term.nat 0)) = Term.eval peanoCtx [] (rhsTerm 0)
  rw [rhsTerm_eval_rhs, Term.evalGo_ite, cond_eval_zero]
  simp [Term.evalGo, Term.nat]

theorem gaussLiteralStep (k : Nat) :
    Pr.Provable peanoCtx [] [] (gaussStatement k) →
    Pr.Provable peanoCtx [] [] (gaussStatement (k + 1)) := by
  rw [gaussStatement, gaussStatement, gaussEq_provable_iff, gaussEq_provable_iff]
  intro hprevEq
  have hprevVal : Term.eval peanoCtx [] (lhsProgram k) =
      some (Val.nat (k * (k + 1) / 2)) := by
    rw [hprevEq.eq [] rfl, rhsTerm_eval_rhs]
  refine Term.eq.mk (lhsProgram_hasType (k + 1)) (rhsTerm_hasType (k + 1)) ?_
  intro env henv
  have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
  subst hnil
  have hbody : loopBodyEval k [] = some (Val.nat (k * (k + 1) / 2)) := by
    rw [← lhsProgram_eval_unfold]
    exact hprevVal
  rw [lhsProgram_eval_unfold]
  change Term.evalGo peanoCtx [loopRecCtx []] (loopEnv (k + 1) [])
    (Term.ite condTerm stepTerm (Term.nat 0)) = Term.eval peanoCtx [] (rhsTerm (k + 1))
  rw [rhsTerm_eval_rhs, Term.evalGo_ite, cond_eval_succ k, step_eval_succ k _ hbody]
  simp [closedForm_succ]

theorem gaussInductionStepProvable :
    Pr.Provable peanoCtx [] [] (Pr.Induction.natStepGoal 0 succName gaussPredicate) :=
  Pr.Induction.natStepGoal_of_literal_step succ_spec gaussPredicate_quantifierFree
    (fun _t k ht hte => (gaussStatement_eq k) ▸ gaussPredicate_congr ht hte)
    (fun k => (gaussStatement_eq (k + 1)) ▸ (gaussStatement_eq k) ▸ gaussLiteralStep k)

theorem gaussBaseProvable :
    Pr.Provable peanoCtx [] []
      (Pr.Induction.instantiateTermAt 0 gaussPredicate (Term.nat 0)) := by
  rw [← gaussStatement_eq 0]
  exact gaussBaseCase

def gaussInductionProgram (n : Nat) :
    Refinement peanoCtx [] [] (gaussStatement n) :=
  Pr.Induction.natInductionWithPredicate succName succ_spec _ gaussPredicate n (gaussStatement_eq n)
    gaussPredicate_quantifierFree

theorem gaussProvable (n : Nat) :
    Pr.Provable peanoCtx [] [] (gaussStatement n) := by
  applyRefinement (gaussInductionProgram n)
  · cases gaussBaseProvable with
    | ofProof proof => exact proof
  · cases gaussInductionStepProvable with
    | ofProof proof => exact proof

example : Pr.Provable peanoCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

end Zag.Test.Gauss.Rec
