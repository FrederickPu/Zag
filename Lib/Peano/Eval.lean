import Zag.Eval
import Lib.Peano.Defs

/-!
# Concretization rules for the Peano operators

`Zag/Eval.lean` supplies one equation per *term* former. This file supplies one equation per
Peano *operator*, so that concretizing a term against an environment is a single `simp` pass.

Each equation is unconditional and its operator lookup comes from `Peano.Model`, so the rules
are `@[simp]` and apply in any context that models Peano -- no per-program plumbing.
-/

namespace Zag

namespace Val

variable {primCtx : PrimitiveCtx} [Peano.Types primCtx]

theorem eq_nat_of_asNat? {v : Val primCtx} {n : Nat} (h : v.asNat? = some n) :
    v = Val.nat n := by
  cases v with
  | mk ty val =>
      unfold Val.asNat? Val.as? at h
      by_cases hty : ty = Peano.NatTy
      case pos =>
        cases hty
        simp at h
        cases h
        simp [Val.nat, Ty.toNat, Ty.ofNat]
      case neg => simp [hty] at h

theorem asNat?_eq_none_iff {v : Val primCtx} : v.asNat? = none ↔ v.ty ≠ Peano.NatTy := by
  cases v with
  | mk ty val =>
      by_cases hty : ty = Peano.NatTy
      case pos => cases hty; simp [Val.asNat?, Val.as?]
      case neg => simp [Val.asNat?, Val.as?, hty]

theorem exists_nat_of_ty {v : Val primCtx} (h : v.ty = Peano.NatTy) : ∃ n, v = Val.nat n := by
  refine ⟨Ty.toNat primCtx (cast (congrArg (Ty.type primCtx) h) v.val), ?_⟩
  cases v with
  | mk ty val => cases h; simp [Val.nat, Ty.toNat, Ty.ofNat]

theorem eq_bool_of_asBool? {v : Val primCtx} {b : Bool} (h : v.asBool? = some b) :
    v = Val.bool b := by
  cases v with
  | mk ty val =>
      unfold Val.asBool? Val.as? at h
      by_cases hty : ty = Peano.BoolTy
      case pos =>
        cases hty
        simp at h
        cases h
        simp [Val.bool, Ty.toBool, Ty.ofBool]
      case neg => simp [hty] at h

@[simp] theorem ty_nat (n : Nat) : (Val.nat (primCtx := primCtx) n).ty = Peano.NatTy := rfl

@[simp] theorem ty_bool (b : Bool) : (Val.bool (primCtx := primCtx) b).ty = Peano.BoolTy := rfl

/- Concretization ends at a `Val`, so an answer is compared as a `Val`. These let the caller
  state the arithmetic obligation in `Nat` and `Bool` instead. -/
@[simp] theorem nat_inj {m n : Nat} :
    (Val.nat (primCtx := primCtx) m = Val.nat n) ↔ m = n := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa using congrArg Val.asNat? h

@[simp] theorem bool_inj {a b : Bool} :
    (Val.bool (primCtx := primCtx) a = Val.bool b) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa using congrArg Val.asBool? h

end Val

namespace Term

variable {ctx : Ctx}

/-- Every fixed-signature Peano operator over one `Nat` reads its operand with `asNat?`. -/
theorem eval_natUnary [Peano.Types ctx.primCtx] {env : Env ctx.primCtx} {name : String}
    {f : Nat → Nat} {a : Term ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f)) :
    Term.eval ctx env (.op name [a]) = (do
      let m ← (← Term.eval ctx env a).asNat?
      some (Val.nat (f m))) := by
  rw [eval_op_ofVals (argTys := [Peano.NatTy]) (outTy := Peano.NatTy) hop rfl]
  cases ha : Term.eval ctx env a with
  | none => simp [ha]
  | some va =>
      cases hm : va.asNat? with
      | none => simp [ha, hm, Val.asNat?_eq_none_iff.mp hm]
      | some m =>
          have hva : va = Val.nat m := Val.eq_nat_of_asNat? hm
          subst hva
          simp [ha]

/-- Every fixed-signature Peano operator over two `Nat`s reads its operands with `asNat?`. -/
theorem eval_natBinary [Peano.Types ctx.primCtx] {env : Env ctx.primCtx} {name : String}
    {f : Nat → Nat → Nat} {a b : Term ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natBinary (primCtx := ctx.primCtx) f)) :
    Term.eval ctx env (.op name [a, b]) = (do
      let m ← (← Term.eval ctx env a).asNat?
      let n ← (← Term.eval ctx env b).asNat?
      some (Val.nat (f m n))) := by
  rw [eval_op_ofVals (argTys := [Peano.NatTy, Peano.NatTy]) (outTy := Peano.NatTy) hop rfl]
  cases ha : Term.eval ctx env a with
  | none => simp [ha]
  | some va =>
      cases hb : Term.eval ctx env b with
      | none => simp [ha, hb]
      | some vb =>
          cases hm : va.asNat? with
          | none => simp [ha, hb, hm, Val.asNat?_eq_none_iff.mp hm]
          | some m =>
              have hva : va = Val.nat m := Val.eq_nat_of_asNat? hm
              subst hva
              cases hn : vb.asNat? with
              | none => simp [ha, hb, hn, Val.asNat?_eq_none_iff.mp hn]
              | some n =>
                  have hvb : vb = Val.nat n := Val.eq_nat_of_asNat? hn
                  subst hvb
                  simp [ha, hb]

/-- `eq`, `lt` and `gt` share one shape: evaluate both operands, compare when the types agree. -/
theorem eval_compare [Peano.Types ctx.primCtx] {env : Env ctx.primCtx} {name : String}
    {cmp : Val ctx.primCtx → Val ctx.primCtx → Option Bool} {a b : Term ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.compare cmp)) :
    Term.eval ctx env (.op name [a, b]) = (do
      let va ← Term.eval ctx env a
      let vb ← Term.eval ctx env b
      if va.ty = vb.ty then (cmp va vb).map Val.bool else none) := by
  cases ha : Term.eval ctx env a with
  | none =>
      rw [Term.eval, Term.evalGo_op, hop]
      simp [Op.compare, show Term.evalGo ctx env a = none from ha]
  | some va =>
      cases hb : Term.eval ctx env b with
      | none =>
          rw [Term.eval, Term.evalGo_op, hop]
          simp [Op.compare, show Term.evalGo ctx env a = some va from ha,
            show Term.evalGo ctx env b = none from hb]
      | some vb =>
          by_cases hty : va.ty = vb.ty
          case pos =>
            rw [Term.eval,
              Term.evalGo_op_compare hop (show Term.evalGo ctx env a = some va from ha)
                (show Term.evalGo ctx env b = some vb from hb) hty]
            simp [hty]
          case neg =>
            rw [Term.eval, Term.evalGo_op, hop]
            simp [Op.compare, show Term.evalGo ctx env a = some va from ha,
              show Term.evalGo ctx env b = some vb from hb, hty]

/-- `ite` is the lazy operator: only the selected branch is evaluated, which is what lets a
  block recurse through it without diverging. -/
@[simp] theorem eval_ite [Peano.Model ctx] {env : Env ctx.primCtx}
    (cond thenTerm elseTerm : Term ctx.primCtx) :
    Term.eval ctx env (no_index (Term.ite cond thenTerm elseTerm)) = (do
      let b ← (← Term.eval ctx env cond).asBool?
      if b then Term.eval ctx env thenTerm else Term.eval ctx env elseTerm) := by
  rw [Term.eval, Term.evalGo_ite]
  cases hcond : Term.evalGo ctx env cond with
  | none => simp [Term.eval, hcond]
  | some value =>
      cases hraw : value.as? Peano.BoolTy with
      | none => simp [Term.eval, hcond, Val.asBool?, hraw]
      | some raw => simp [Term.eval, hcond, Val.asBool?, hraw]

/-! Comparing two `Nat` values is the case every program hits; state it so `simp` gets a `Bool`
  literal rather than a `primEq?` application. -/

@[simp] theorem _root_.Zag.Val.primEq?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (m n : Nat) :
    Val.primEq? (Val.nat (primCtx := primCtx) m) (Val.nat n) = some (decide (m = n)) := by
  simp [Val.primEq?]

@[simp] theorem _root_.Zag.Val.primLt?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (m n : Nat) :
    Val.primLt? (Val.nat (primCtx := primCtx) m) (Val.nat n) = some (decide (m < n)) := by
  simp [Val.primLt?]

@[simp] theorem _root_.Zag.Val.primGt?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (m n : Nat) :
    Val.primGt? (Val.nat (primCtx := primCtx) m) (Val.nat n) = some (decide (n < m)) := by
  simp [Val.primGt?, Val.primLt?]

@[simp] theorem eval_natLit [Peano.Types ctx.primCtx] (env : Env ctx.primCtx) (n : Nat) :
    Term.eval ctx env (no_index (Term.nat n)) = some (Val.nat n) := by
  simp [Term.nat]

@[simp] theorem eval_boolLit [Peano.Types ctx.primCtx] (env : Env ctx.primCtx) (b : Bool) :
    Term.eval ctx env (no_index (Term.bool b)) = some (Val.bool b) := by
  simp [Term.bool]

/-! ### the standard operators of a Peano model

  Each is `@[simp]`, so a term built from them concretizes with no configuration. -/

variable [Peano.Model ctx] {env : Env ctx.primCtx} {a b cond : Term ctx.primCtx}

@[simp] theorem eval_add :
    Term.eval ctx env (no_index (Term.op "add" [a, b])) = (do
      let m ← (← Term.eval ctx env a).asNat?
      let n ← (← Term.eval ctx env b).asNat?
      some (Val.nat (m + n))) := eval_natBinary Peano.Model.addOp

@[simp] theorem eval_sub :
    Term.eval ctx env (no_index (Term.op "sub" [a, b])) = (do
      let m ← (← Term.eval ctx env a).asNat?
      let n ← (← Term.eval ctx env b).asNat?
      some (Val.nat (m - n))) := eval_natBinary Peano.Model.subOp

@[simp] theorem eval_mul :
    Term.eval ctx env (no_index (Term.op "mul" [a, b])) = (do
      let m ← (← Term.eval ctx env a).asNat?
      let n ← (← Term.eval ctx env b).asNat?
      some (Val.nat (m * n))) := eval_natBinary Peano.Model.mulOp

@[simp] theorem eval_div :
    Term.eval ctx env (no_index (Term.op "div" [a, b])) = (do
      let m ← (← Term.eval ctx env a).asNat?
      let n ← (← Term.eval ctx env b).asNat?
      some (Val.nat (m / n))) := eval_natBinary Peano.Model.divOp

@[simp] theorem eval_succ :
    Term.eval ctx env (no_index (Term.op "succ" [a])) = (do
      let m ← (← Term.eval ctx env a).asNat?
      some (Val.nat (m + 1))) := eval_natUnary Peano.Model.succOp

@[simp] theorem eval_eq :
    Term.eval ctx env (no_index (Term.op "eq" [a, b])) = (do
      let va ← Term.eval ctx env a
      let vb ← Term.eval ctx env b
      if va.ty = vb.ty then (Val.primEq? va vb).map Val.bool else none) :=
  eval_compare Peano.Model.eqOp

@[simp] theorem eval_lt :
    Term.eval ctx env (no_index (Term.op "lt" [a, b])) = (do
      let va ← Term.eval ctx env a
      let vb ← Term.eval ctx env b
      if va.ty = vb.ty then (Val.primLt? va vb).map Val.bool else none) :=
  eval_compare Peano.Model.ltOp

@[simp] theorem eval_gt :
    Term.eval ctx env (no_index (Term.op "gt" [a, b])) = (do
      let va ← Term.eval ctx env a
      let vb ← Term.eval ctx env b
      if va.ty = vb.ty then (Val.primGt? va vb).map Val.bool else none) :=
  eval_compare Peano.Model.gtOp

end Term

/-! ### from evaluation to `Term.eq`

  `Term.eq` quantifies over every environment modelling the scope, so proving two terms equal at
  `Nat` means concretizing both under an arbitrary such environment. -/

theorem term_eq_nat_of_eval {ctx : Ctx} [Peano.Types ctx.primCtx]
    {lhs rhs : Term ctx.primCtx}
    (hlhs : Term.hasType ctx [] lhs Peano.NatTy)
    (hrhs : Term.hasType ctx [] rhs Peano.NatTy)
    (heval : ∀ env : Env ctx.primCtx, env.Models [] →
      ∃ n : Nat, Term.eval ctx env lhs = some (Val.nat n) ∧
        Term.eval ctx env rhs = some (Val.nat n)) :
    Term.eq ctx [] Peano.NatTy lhs rhs := by
  refine Term.eq.mk hlhs hrhs ?_
  intro env henv
  obtain ⟨n, hl, hr⟩ := heval env henv
  rw [hl, hr]

/-! ### from a reflected equation back to evaluation

  `Pr.Induction`'s step goal hands the proof an equation `succ x = y` reflected into Zag. Both
  sides must be `Nat`-valued for the induction to say anything, and that is what this recovers. -/

theorem eval_nat_of_eq_natUnary_true {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {name : String} {arg rhs : Term ctx.primCtx} {f : Nat → Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (h : Term.eval ctx env (.op "eq" [.op name [arg], rhs]) = some (Val.bool true)) :
    ∃ n : Nat, Term.eval ctx env rhs = some (Val.nat n) := by
  rw [Term.eval_eq, Term.eval_natUnary hop] at h
  cases hrhs : Term.eval ctx env rhs with
  | none => simp [hrhs] at h
  | some rhsVal =>
      by_cases hty : rhsVal.ty = Peano.NatTy
      case pos =>
        obtain ⟨n, hn⟩ := Val.exists_nat_of_ty hty
        exact ⟨n, by rw [hn]⟩
      case neg =>
        cases harg : Term.eval ctx env arg with
        | none => simp [harg] at h
        | some argVal =>
            cases hm : argVal.asNat? with
            | none => simp [harg, hm] at h
            | some m => simp [harg, hm, hrhs, Ne.symm hty] at h

theorem eval_nat_of_reflected_natUnary_eq {ctx : Ctx} [Peano.Model ctx]
    {name : String} {f : Nat → Nat} {arg rhs : Term ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (heq : Term.eq ctx [] Peano.BoolTy (.op "eq" [.op name [arg], rhs]) (Term.bool true)) :
    ∀ env : Env ctx.primCtx, env.Models [] →
      ∃ n : Nat, Term.eval ctx env rhs = some (Val.nat n) := by
  intro env henv
  refine eval_nat_of_eq_natUnary_true (arg := arg) hop ?_
  simpa using heq.eq env henv

end Zag
