import Zag.Meta

namespace Zag.Test.Gauss.Rec

abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev NatTy : Ty := ty% { Nat }

def natBinaryFunc (op : Nat → Nat → Nat) : PrimFunc natCtx where
  args := ["Nat", "Nat"]
  out := "Nat"
  hprim := by
    intro x hx
    simp at hx
    simp [natCtx]
    exact Or.inl hx
  interp := fun
    | [lhsVal, rhsVal] => do
        let lhs ← lhsVal.asNat?
        let rhs ← rhsVal.asNat?
        some (Val.nat (op lhs rhs))
    | _ => none

abbrev natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add)
  , ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul)
  , ("div", natBinaryFunc Nat.div)
  ]

def sumTo : Nat -> Nat
| 0 => 0
| n + 1 => sumTo n + (n + 1)

def natType {varCtx : VarCtx} (n : Nat) :
    Term.hasType natCtx natFuncCtx varCtx (Term.nat n) NatTy := by
  exact Term.hasType.prim (Ty.ofNat natCtx n)

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

def gaussStatement (n : Nat) : Pr natCtx :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)

def loopEnv (i : Nat) (env : List (Val natCtx)) : List (Val natCtx) :=
  env ++ [Val.nat i, Term.motiveVal NatTy NatTy]

def loopRecCtx (env : List (Val natCtx)) : Term.RecCtx natCtx :=
  { body := bodyTerm, env := env, stateTy := NatTy, resultTy := NatTy }

noncomputable def loopBodyEval (i : Nat) (env : List (Val natCtx)) : Option (Val natCtx) :=
  Term.evalGo natCtx natFuncCtx (some (loopRecCtx env)) (loopEnv i env) bodyTerm

theorem bodyTerm_hasType : Term.hasType natCtx natFuncCtx bodyCtx bodyTerm NatTy := by
  let program := Zag.Pr.MetaProgram.iterate (primCtx := natCtx) (primFuncCtx := natFuncCtx)
    (ctxTy := []) (ctxTerm := []) 20 (fun goal => Zag.Pr.MetaProgram.unifyType goal)
    (.hasType bodyCtx bodyTerm NatTy)
  have hclosed : program.goals = [] := by
    exact List.eq_nil_of_length_eq_zero (by native_decide : program.goals.length = 0)
  have hprov := Zag.Pr.MetaProgram.toProvable program hclosed
  cases hprov with
  | ofProof proof =>
      simpa [Pr.interp, bodyTerm, condTerm, stepTerm, recurseTerm, prevTerm, iTerm,
        Term.subst, Term.nat, Ty.subst] using proof

theorem lhsProgram_hasType (n : Nat) :
    Term.hasType natCtx natFuncCtx [] (lhsProgram n) NatTy := by
  unfold lhsProgram
  exact Term.hasType.recurse (natType n) bodyTerm_hasType

theorem addFunc_hasType {varCtx : VarCtx} :
    Term.hasType natCtx natFuncCtx varCtx (.primFunc "add") (.func [NatTy, NatTy] NatTy) := by
  have hf := @Term.hasType.primFunc natCtx natFuncCtx varCtx ⟨0, by decide⟩
  simpa [natFuncCtx, natBinaryFunc, PrimFunc.ty, NatTy] using hf

theorem mulFunc_hasType {varCtx : VarCtx} :
    Term.hasType natCtx natFuncCtx varCtx (.primFunc "mul") (.func [NatTy, NatTy] NatTy) := by
  have hf := @Term.hasType.primFunc natCtx natFuncCtx varCtx ⟨2, by decide⟩
  simpa [natFuncCtx, natBinaryFunc, PrimFunc.ty, NatTy] using hf

theorem divFunc_hasType {varCtx : VarCtx} :
    Term.hasType natCtx natFuncCtx varCtx (.primFunc "div") (.func [NatTy, NatTy] NatTy) := by
  have hf := @Term.hasType.primFunc natCtx natFuncCtx varCtx ⟨3, by decide⟩
  simpa [natFuncCtx, natBinaryFunc, PrimFunc.ty, NatTy] using hf

theorem natBinaryApp_hasType {varCtx : VarCtx} {fn lhs rhs : Term natCtx}
    (hfn : Term.hasType natCtx natFuncCtx varCtx fn (.func [NatTy, NatTy] NatTy))
    (hlhs : Term.hasType natCtx natFuncCtx varCtx lhs NatTy)
    (hrhs : Term.hasType natCtx natFuncCtx varCtx rhs NatTy) :
    Term.hasType natCtx natFuncCtx varCtx (.app fn [lhs, rhs]) NatTy := by
  refine Term.hasType.app hfn rfl ?_
  intro idx
  cases idx with
  | mk val isLt =>
      cases val with
      | zero => exact hlhs
      | succ val =>
          cases val with
          | zero => exact hrhs
          | succ _ =>
              simp at isLt
              omega

theorem rhsTerm_hasType (n : Nat) :
    Term.hasType natCtx natFuncCtx [] (rhsTerm n) NatTy := by
  unfold rhsTerm
  exact natBinaryApp_hasType divFunc_hasType
    (natBinaryApp_hasType mulFunc_hasType (natType n)
      (natBinaryApp_hasType addFunc_hasType (natType n) (natType 1)))
    (natType 2)

theorem lhsProgram_subst_nil (n : Nat) :
    Term.subst [] (lhsProgram n) = lhsProgram n := by
  simp

theorem rhsTerm_subst_nil (n : Nat) :
    Term.subst [] (rhsTerm n) = rhsTerm n := by
  simp

theorem lhsProgram_eval_unfold (i : Nat) :
    Term.eval natCtx natFuncCtx [] (lhsProgram i) = loopBodyEval i [] := by
  conv =>
    lhs
    simp [lhsProgram, Term.eval, Term.evalGo, Term.motiveVal, Term.nat]
  change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv i []) bodyTerm =
    loopBodyEval i []
  rfl

theorem cond_eval_zero :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv 0 []) condTerm =
      some (Val.bool false) := by
  unfold condTerm iTerm loopEnv
  simp [Term.evalGo, Term.nat, Val.primGt?, Val.primLt?]

theorem cond_eval_succ (i : Nat) :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (i + 1) []) condTerm =
      some (Val.bool true) := by
  unfold condTerm iTerm loopEnv
  simp [Term.evalGo, Term.nat, Val.primGt?, Val.primLt?]

/-- Genuinely inductive: `lhsProgram (i + 1)`'s value is computed *from* `loopBodyEval i`'s
  value `V` (not independently recomputed) — this is the mechanical one-step unfolding that
  the induction step below chains from a hypothesis instead of re-deriving from scratch. -/
theorem step_eval_succ (i V : Nat)
    (hbody : loopBodyEval i [] = some (Val.nat V)) :
    Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (i + 1) []) stepTerm =
      some (Val.nat (V + (i + 1))) := by
  have hrec : Term.evalGo natCtx natFuncCtx
      (some (loopRecCtx [])) (loopEnv (i + 1) []) recurseTerm =
        some (Val.nat V) := by
    change Term.evalGo natCtx natFuncCtx (some (loopRecCtx []))
        [Val.nat (i + 1), Term.motiveVal NatTy NatTy]
        (.app (.var 1) [prevTerm]) = some (Val.nat V)
    unfold prevTerm iTerm loopRecCtx
    simp [Term.evalGo, Term.evalList, PrimFunc.apply, PrimFuncCtx.get?,
      natFuncCtx, natBinaryFunc, Term.nat]
    change (loopBodyEval i []).bind
        (fun result => (Val.as? NatTy result).bind fun resultRaw => some (Val.mk NatTy resultRaw)) =
      some (Val.nat V)
    rw [hbody]
    simp
  conv =>
    lhs
    simp [loopEnv, stepTerm, iTerm, Term.evalGo, Term.evalList, PrimFunc.apply,
      PrimFuncCtx.get?, natFuncCtx]
  rw [show Term.evalGo natCtx natFuncCtx (some (loopRecCtx []))
      [Val.nat (i + 1), Term.motiveVal NatTy NatTy] recurseTerm =
        some (Val.nat V) by simpa [loopEnv] using hrec]
  simp [natBinaryFunc]

theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
      calc
        2 * sumTo (n + 1)
            = 2 * (sumTo n + (n + 1)) := by simp [sumTo]
        _ = 2 * sumTo n + 2 * (n + 1) := by rw [Nat.left_distrib]
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 2) * (n + 1) := by rw [(Nat.add_mul n 2 (n + 1)).symm]
        _ = (n + 1) * (n + 2) := by rw [Nat.mul_comm]

theorem sumTo_eq_closed (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  have h2 : Not ((2 : Nat) = 0) := by decide
  exact Nat.eq_div_of_mul_eq_right h2 (two_mul_sumTo n)

/-- The closed-form value at `k + 1` is the closed-form value at `k` plus `k + 1` — pure
  arithmetic, needed by the induction step to relate consecutive closed-form values without
  re-deriving either one from scratch. -/
theorem closedForm_succ (k : Nat) :
    k * (k + 1) / 2 + (k + 1) = (k + 1) * (k + 2) / 2 := by
  rw [← sumTo_eq_closed k, ← sumTo_eq_closed (k + 1)]
  rfl

/-- General-purpose unwrap for `.eq` goals under the empty context: `Pr.Provable` of a
  `.eq [] NatTy lhs rhs` is just `Term.eq ... NatTy lhs rhs` once `Term.subst []`/`Ty.subst []`
  are stripped — this pattern otherwise repeats at the start of every such proof. -/
theorem gaussEq_provable_iff {lhs rhs : Term natCtx} :
    Pr.Provable natCtx natFuncCtx [] [] (.eq [] NatTy lhs rhs) ↔
      Term.eq natCtx natFuncCtx [] NatTy lhs rhs := by
  constructor
  · intro h
    cases h with
    | ofProof proof => simpa [Pr.interp, NatTy, Ty.subst] using proof
  · intro h
    exact Pr.Provable.ofProof (by simpa [Pr.interp, NatTy, Ty.subst] using h)

theorem rhsTerm_eval_rhs (n : Nat) :
    Term.eval natCtx natFuncCtx [] (rhsTerm n) = some (Val.nat (n * (n + 1) / 2)) := by
  simp [rhsTerm, Term.eval, Term.evalGo, Term.evalList,
    PrimFunc.apply, PrimFuncCtx.get?, natFuncCtx, natBinaryFunc, Term.nat]
  rfl

def lhsProgramOf (t : Term natCtx) : Term natCtx :=
  .recurse NatTy t bodyTerm

def rhsTermOf (t : Term natCtx) : Term natCtx :=
  term% { call func(div) [call func(mul) [raw(t), call func(add) [raw(t), nat(1)]], nat(2)] }

theorem lhsProgram_eq_lhsProgramOf (n : Nat) : lhsProgram n = lhsProgramOf (Term.nat n) := rfl

theorem rhsTerm_eq_rhsTermOf (n : Nat) : rhsTerm n = rhsTermOf (Term.nat n) := rfl

theorem lhsProgramOf_hasType {t : Term natCtx} (ht : Term.hasType natCtx natFuncCtx [] t NatTy) :
    Term.hasType natCtx natFuncCtx [] (lhsProgramOf t) NatTy := by
  unfold lhsProgramOf
  exact Term.hasType.recurse ht bodyTerm_hasType

theorem rhsTermOf_hasType {t : Term natCtx} (ht : Term.hasType natCtx natFuncCtx [] t NatTy) :
    Term.hasType natCtx natFuncCtx [] (rhsTermOf t) NatTy := by
  unfold rhsTermOf
  exact natBinaryApp_hasType divFunc_hasType
    (natBinaryApp_hasType mulFunc_hasType ht
      (natBinaryApp_hasType addFunc_hasType ht (natType 1)))
    (natType 2)

theorem lhsProgramOf_eval_unfold {t : Term natCtx} {k : Nat}
    (ht : Term.eval natCtx natFuncCtx [] t = some (Val.nat k)) :
    Term.eval natCtx natFuncCtx [] (lhsProgramOf t) = loopBodyEval k [] := by
  have ht' : Term.evalGo natCtx natFuncCtx none [] t = some (Val.nat k) := ht
  conv =>
    lhs
    simp [lhsProgramOf, Term.eval, Term.evalGo, Term.motiveVal, ht']
  change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv k []) bodyTerm =
    loopBodyEval k []
  rfl

/-- `lhsProgramOf`'s evaluated value only depends on its argument's evaluated value, not its
  syntax — this is what lets a term `x` and the literal `nat k` it evaluates to stand in for
  each other freely. -/
theorem lhsProgramOf_congr {a b : Term natCtx}
    (h : Term.evalGo natCtx natFuncCtx none [] a = Term.evalGo natCtx natFuncCtx none [] b) :
    Term.eval natCtx natFuncCtx [] (lhsProgramOf a) = Term.eval natCtx natFuncCtx [] (lhsProgramOf b) := by
  unfold lhsProgramOf Term.eval
  simp only [Term.evalGo, h]

theorem rhsTermOf_congr {a b : Term natCtx}
    (h : Term.evalGo natCtx natFuncCtx none [] a = Term.evalGo natCtx natFuncCtx none [] b) :
    Term.eval natCtx natFuncCtx [] (rhsTermOf a) = Term.eval natCtx natFuncCtx [] (rhsTermOf b) := by
  unfold rhsTermOf Term.eval
  simp [Term.evalGo, Term.evalList, h]

/-- Transports provability of `gaussStatement`'s underlying equation across any two terms
  `a, b` with the same evaluated value — the one genuinely predicate-specific fact `hcongr`
  needs, since `lhsProgramOf`/`rhsTermOf`'s *shape* (not just value) could in principle matter
  to a less well-behaved predicate. -/
theorem gaussEq_provable_congr {a b : Term natCtx}
    (hta : Term.hasType natCtx natFuncCtx [] a NatTy)
    (hab : Term.evalGo natCtx natFuncCtx none [] a = Term.evalGo natCtx natFuncCtx none [] b)
    (h : Pr.Provable natCtx natFuncCtx [] [] (.eq [] NatTy (lhsProgramOf b) (rhsTermOf b))) :
    Pr.Provable natCtx natFuncCtx [] [] (.eq [] NatTy (lhsProgramOf a) (rhsTermOf a)) := by
  rw [gaussEq_provable_iff] at h ⊢
  refine Term.eq.mk (lhsProgramOf_hasType hta) (rhsTermOf_hasType hta) ?_
  intro env henv
  have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
  subst hnil
  rw [lhsProgramOf_congr hab, rhsTermOf_congr hab, h.eq [] rfl]

def gaussPredicate : Pr natCtx :=
  .eq [] NatTy
    (.recurse NatTy (.var 0) (Pr.MetaProgram.weakenTermAt 0 bodyTerm))
    (.app (.primFunc "div")
      [(.app (.primFunc "mul") [(.var 0), (.app (.primFunc "add") [(.var 0), Term.nat 1])]),
       Term.nat 2])

theorem gaussPredicate_instantiate_eq (t : Term natCtx) :
    Pr.MetaProgram.instantiateTermAt 0 gaussPredicate t =
      .eq [] NatTy (lhsProgramOf t) (rhsTermOf t) := by
  simp [gaussPredicate, lhsProgramOf, rhsTermOf,
    Pr.MetaProgram.instantiateTermAt, Pr.MetaProgram.instantiateTermInTerm,
    Pr.MetaProgram.instantiateTermInTerm_weakenTermAt, Term.nat]

theorem gaussStatement_eq (n : Nat) :
    gaussStatement n = Pr.MetaProgram.instantiateTermAt 0 gaussPredicate (Term.nat n) := by
  rw [gaussPredicate_instantiate_eq, gaussStatement, lhsProgram_eq_lhsProgramOf,
    rhsTerm_eq_rhsTermOf]

theorem gaussPredicate_quantifierFree :
    Pr.MetaProgram.quantifierFree gaussPredicate = true := rfl

/-- The eval-congruence bridge `natStepGoal_of_literal_step` needs: provability of
  `gaussPredicate` instantiated at any Nat-typed term `t` is the same as provability of
  `gaussStatement k`, given `t` evaluates to `k`. -/
theorem gaussPredicate_congr {t : Term natCtx} {k : Nat}
    (ht : Term.hasType natCtx natFuncCtx [] t (.prim "Nat"))
    (hte : Term.eval natCtx natFuncCtx [] t = some (Val.nat k)) :
    Pr.Provable natCtx natFuncCtx [] []
        (Pr.MetaProgram.instantiateTermAt 0 gaussPredicate t) ↔
      Pr.Provable natCtx natFuncCtx [] [] (gaussStatement k) := by
  rw [gaussPredicate_instantiate_eq, gaussStatement, lhsProgram_eq_lhsProgramOf,
    rhsTerm_eq_rhsTermOf]
  have hte' : Term.evalGo natCtx natFuncCtx none [] t = some (Val.nat k) := hte
  have hnat' : Term.evalGo natCtx natFuncCtx none [] (Term.nat k) = some (Val.nat k) := by
    simp [Term.evalGo, Term.nat]
  constructor
  · exact gaussEq_provable_congr (natType k) (hnat'.trans hte'.symm)
  · exact gaussEq_provable_congr ht (hte'.trans hnat'.symm)

/-- Base case: `gaussStatement 0` holds directly by evaluation — the loop condition is false
  at `i = 0`, so both sides reduce to `0`. No induction needed for the base case. -/
theorem gaussBaseCase :
    Pr.Provable natCtx natFuncCtx [] [] (gaussStatement 0) := by
  rw [gaussStatement, gaussEq_provable_iff]
  refine Term.eq.mk (lhsProgram_hasType 0) (rhsTerm_hasType 0) ?_
  intro env henv
  have hnil : env = [] := List.eq_nil_of_length_eq_zero henv
  subst hnil
  rw [lhsProgram_eval_unfold]
  change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv 0 [])
    (.ite condTerm stepTerm (Term.nat 0)) = Term.eval natCtx natFuncCtx [] (rhsTerm 0)
  rw [rhsTerm_eval_rhs]
  simp [Term.evalGo, cond_eval_zero, Term.nat]

/-- The genuine induction step: `lhsProgram (k + 1)`'s value is derived *from*
  `lhsProgram k`'s value (extracted from the hypothesis via `rhsTerm_eval_rhs`, which
  fixes it to `k * (k + 1) / 2`) by chaining exactly one loop iteration
  (`cond_eval_succ` + `step_eval_succ`) — it is never independently recomputed. -/
theorem gaussLiteralStep (k : Nat) :
    Pr.Provable natCtx natFuncCtx [] [] (gaussStatement k) →
    Pr.Provable natCtx natFuncCtx [] [] (gaussStatement (k + 1)) := by
  rw [gaussStatement, gaussStatement, gaussEq_provable_iff, gaussEq_provable_iff]
  intro hprevEq
  have hprevVal : Term.eval natCtx natFuncCtx [] (lhsProgram k) =
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
  change Term.evalGo natCtx natFuncCtx (some (loopRecCtx [])) (loopEnv (k + 1) [])
    (.ite condTerm stepTerm (Term.nat 0)) = Term.eval natCtx natFuncCtx [] (rhsTerm (k + 1))
  rw [rhsTerm_eval_rhs]
  simp [Term.evalGo, cond_eval_succ k, step_eval_succ k _ hbody, closedForm_succ]

theorem gaussInductionStepProvable :
    Pr.Provable natCtx natFuncCtx [] [] (Pr.MetaProgram.natStepGoal 0 gaussPredicate) :=
  Pr.MetaProgram.natStepGoal_of_literal_step gaussPredicate_quantifierFree
    (fun _t k ht hte => (gaussStatement_eq k) ▸ gaussPredicate_congr ht hte)
    (fun k => (gaussStatement_eq (k + 1)) ▸ (gaussStatement_eq k) ▸ gaussLiteralStep k)

theorem gaussBaseProvable :
    Pr.Provable natCtx natFuncCtx [] []
      (Pr.MetaProgram.instantiateTermAt 0 gaussPredicate (Term.nat 0)) := by
  rw [← gaussStatement_eq 0]
  exact gaussBaseCase

def gaussInductionProgram (n : Nat) :
    Pr.MetaProgram natCtx natFuncCtx [] [] (gaussStatement n) :=
  Pr.MetaProgram.natInductionWithPredicate _ gaussPredicate n (gaussStatement_eq n)
    gaussPredicate_quantifierFree

-- gaussInductionProgram n produces exactly two goals:
--   Base case: gaussStatement 0
--   Induction step: ∀ x y, isSuccPr 0 (at x, y) → gaussPredicate[x] → gaussPredicate[y]

theorem gaussProvable (n : Nat) :
    Pr.Provable natCtx natFuncCtx [] [] (gaussStatement n) :=
  (gaussInductionProgram n).prove fun _subgoal hsubgoal => by
    cases hsubgoal with
    | head => exact gaussBaseProvable
    | tail _ htail =>
        cases htail with
        | head => exact gaussInductionStepProvable
        | tail _ hrest => cases hrest

example : Pr.Provable natCtx natFuncCtx [] [] (gaussStatement 100) :=
  gaussProvable 100

end Zag.Test.Gauss.Rec
