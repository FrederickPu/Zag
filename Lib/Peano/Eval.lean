import Zag.EvalSpecs
import Zag.Refinement
import Lib.Peano.Defs

/-!
# Small-step Peano evaluation lemmas

These are relational facts over `EvaluatesTo`, not rewrite rules for the old big-step evaluator.
-/

namespace Zag

/- Peano's evaluation-relevant definitions. Tagged here rather than in `Lib/Peano/Defs.lean` so
  that the pure definition layer keeps its minimal imports. -/
/- `Val.nat`/`Val.bool` are deliberately absent: `Val.mk_ofNat`/`mk_ofBool` are `@[simp]` and fold
  *into* them, so tagging them here would make `simp [eval_step]` loop. They are the normal form.
  `Term.nat`/`Term.bool` do have to be unfolded -- `step` matches on `Term.prim` -- so they are
  tagged here and folded back by `Term.prim_nat`/`prim_bool` once stepping is done. -/
attribute [eval_step]
  Op.compare Op.eq Op.ite Op.natBinary Op.natUnary
  Peano.opCtx Term.nat Term.bool Term.ite Lib.Peano.natOpCtx
  Val.asNat?_nat Val.asBool?_bool

attribute [spec] Term.nat Term.bool

/-- Restore `Term.nat n` in a goal the machine stopped short of. Not `@[eval_step]`: paired with
  the `Term.nat` tag above in one `simp` call these two loop. -/
@[eval_fold] theorem Term.prim_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    (Term.prim Peano.NatTy (Ty.ofNat primCtx n) : Term primCtx) = Term.nat n := rfl

@[eval_fold] theorem Term.prim_bool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) :
    (Term.prim Peano.BoolTy (Ty.ofBool primCtx b) : Term primCtx) = Term.bool b := rfl


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
  | blockRef n a o => simp [Val.asNat?, Val.as?] at h
  | opRef n c a o => simp [Val.asNat?, Val.as?] at h

theorem asNat?_eq_none_iff {v : Val primCtx} : v.asNat? = none ↔ v.ty ≠ Peano.NatTy := by
  cases v with
  | mk ty val =>
      by_cases hty : ty = Peano.NatTy
      case pos => cases hty; simp [Val.asNat?, Val.as?]
      case neg => simp [Val.asNat?, Val.as?, hty]
  | blockRef n a o => simp [Val.asNat?, Val.as?, Val.ty, Peano.NatTy]
  | opRef n c a o => simp [Val.asNat?, Val.as?, Val.ty, Peano.NatTy]

theorem exists_nat_of_ty {v : Val primCtx} (h : v.ty = Peano.NatTy) : ∃ n, v = Val.nat n := by
  cases v with
  | mk ty val =>
      cases h
      exact ⟨Ty.toNat primCtx val, by simp [Val.nat, Ty.toNat, Ty.ofNat]⟩
  | blockRef n a o => simp [Val.ty, Peano.NatTy] at h
  | opRef n c a o => simp [Val.ty, Peano.NatTy] at h

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
  | blockRef n a o => simp [Val.asBool?, Val.as?] at h
  | opRef n c a o => simp [Val.asBool?, Val.as?] at h

@[simp] theorem ty_nat (n : Nat) : (Val.nat (primCtx := primCtx) n).ty = Peano.NatTy := rfl

@[simp] theorem ty_bool (b : Bool) : (Val.bool (primCtx := primCtx) b).ty = Peano.BoolTy := rfl

/- Concretization ends at a `Val`, so an answer is compared as a `Val`. These let the caller
  state the arithmetic obligation in `Nat` and `Bool` instead. -/
@[simp, eval_finish] theorem nat_inj {m n : Nat} :
    (Val.nat (primCtx := primCtx) m = Val.nat n) ↔ m = n := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa using congrArg Val.asNat? h

@[simp, eval_finish] theorem bool_inj {a b : Bool} :
    (Val.bool (primCtx := primCtx) a = Val.bool b) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  simpa using congrArg Val.asBool? h

end Val

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

/-! ### small-step Peano operator specs -/

namespace EvalTriple.Exact

@[eval_semantic, zspec] theorem evaluates_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (n : Nat) :
    EvaluatesTo ctx env (Term.nat n) (Val.nat n) := by
  simpa [Term.nat] using
    (EvaluatesTo.prim (ctx := ctx) (env := env) Peano.NatTy (Ty.ofNat ctx.primCtx n))

@[eval_semantic, zspec] theorem evaluates_bool {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (b : Bool) :
    EvaluatesTo ctx env (Term.bool b) (Val.bool b) := by
  simpa [Term.bool] using
    (EvaluatesTo.prim (ctx := ctx) (env := env) Peano.BoolTy (Ty.ofBool ctx.primCtx b))

theorem evaluates_natUnary {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat} {a : Term ctx.primCtx}
    {m : Nat} (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (ha : EvaluatesTo ctx env a (Val.nat m)) :
    EvaluatesTo ctx env (.op name [a]) (Val.nat (f m)) := by
  refine EvaluatesTo.op_applyVals hop (EvaluatesList.cons ha EvaluatesList.nil) ?_
  simp [Op.applyValsAt, Op.fixed, Op.natUnary, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

theorem evaluates_natBinary {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat → Nat}
    {a b : Term ctx.primCtx} {m n : Nat}
    (hop : ctx.opCtx.get? name = some (Op.natBinary (primCtx := ctx.primCtx) f))
    (ha : EvaluatesTo ctx env a (Val.nat m))
    (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op name [a, b]) (Val.nat (f m n)) := by
  refine EvaluatesTo.op_applyVals hop
    (EvaluatesList.cons ha (EvaluatesList.cons hb EvaluatesList.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, Op.natBinary, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

@[eval_semantic, zspec] theorem evaluates_succ_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a : Term ctx.primCtx} {m : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) :
    EvaluatesTo ctx env (.op "succ" [a]) (Val.nat (m + 1)) := by
  simpa only [Nat.succ_eq_add_one] using
    (evaluates_natUnary (Peano.Model.succOp (ctx := ctx)) ha)

namespace Op.Body

private def resume? {primCtx : PrimitiveCtx} :
    Op.Body primCtx → Option (Val primCtx) → Op.Body primCtx
| .next _ resume => resume
| _ => fun _ => .fail

end Op.Body

@[eval_semantic, zspec] theorem evaluates_ite_false {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {conditionTerm thenTerm elseTerm : Term ctx.primCtx}
    {value : Val ctx.primCtx}
    (hcondition : EvaluatesTo ctx env conditionTerm (Val.bool false))
    (helse : EvaluatesTo ctx env elseTerm value) :
    EvaluatesTo ctx env (Term.ite conditionTerm thenTerm elseTerm) value := by
  intro base
  let oper := Op.ite (primCtx := ctx.primCtx) (M := ctx.M)
  let firstResume := Op.Body.resume?
    ((oper.body "ite" 3).getD (Op.Body.fail : Op.Body ctx.primCtx))
  let firstBase := Frame.opBody firstResume (Op.Arg.ofTerms [thenTerm, elseTerm]) env :: base
  have hopId := Exact.idView_get?_of_get? hM (Peano.Model.iteOp (ctx := ctx))
  apply EvaluatesFrom.pureStep (next := ⟨.eval conditionTerm, env, firstBase⟩)
  · simp [Machine.step, Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
      Term.ite, hopId, firstBase, firstResume, oper, Op.Body.resume?, Op.ite,
      Op.fixed, Machine.driveOp]
  apply EvaluatesFrom.bind (hcondition firstBase)
  intro conditionScope
  let secondResume := Op.Body.resume?
    ((Op.Body.resume? (firstResume (some (Val.bool false)))) none)
  let secondBase := Frame.opBody secondResume [] env :: base
  apply EvaluatesFrom.pureStep (next := ⟨.eval elseTerm, env, secondBase⟩)
  · simp [Machine.step, Machine.resumeFrame, Machine.ofOption, Machine.driveOp, firstBase,
      firstResume, secondBase, secondResume, oper, Op.Body.resume?, Op.ite, Op.fixed]
  apply EvaluatesFrom.bind (helse secondBase)
  intro valueScope
  apply EvaluatesFrom.pureStep (next := ⟨.ret value, env, base⟩)
  · simp [Machine.step, Machine.resumeFrame, Machine.ofOption, Machine.driveOp, secondBase,
      secondResume, firstResume, oper, Op.Body.resume?, Op.ite, Op.fixed]
  exact EvaluatesFrom.done

@[eval_semantic, zspec] theorem evaluates_add_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "add" [a, b]) (Val.nat (m + n)) :=
  evaluates_natBinary (Peano.Model.addOp (ctx := ctx)) ha hb

@[eval_semantic, zspec] theorem evaluates_sub_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "sub" [a, b]) (Val.nat (m - n)) :=
  evaluates_natBinary (Peano.Model.subOp (ctx := ctx)) ha hb

@[eval_semantic, zspec] theorem evaluates_mul_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "mul" [a, b]) (Val.nat (m * n)) :=
  evaluates_natBinary (Peano.Model.mulOp (ctx := ctx)) ha hb

@[eval_semantic, zspec] theorem evaluates_div_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "div" [a, b]) (Val.nat (m / n)) :=
  evaluates_natBinary (Peano.Model.divOp (ctx := ctx)) ha hb

theorem evaluates_natUnary_literal_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat} {a : Nat}
    {expected : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f)) :
    EvaluatesTo ctx env (.op name [Term.nat a]) expected ↔
      Val.nat (f a) = expected := by
  apply EvaluatesTo.iff_eq_of
  exact evaluates_natUnary hop (evaluates_nat env a)

theorem evaluates_natBinary_literals_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat → Nat} {a b : Nat}
    {expected : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natBinary (primCtx := ctx.primCtx) f)) :
    EvaluatesTo ctx env (.op name [Term.nat a, Term.nat b]) expected ↔
      Val.nat (f a b) = expected := by
  apply EvaluatesTo.iff_eq_of
  exact evaluates_natBinary hop (evaluates_nat env a) (evaluates_nat env b)

theorem evaluates_compare {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String}
    {cmp : Val ctx.primCtx → Val ctx.primCtx → Option Bool}
    {a b : Term ctx.primCtx} {va vb : Val ctx.primCtx} {result : Bool}
    (hop : ctx.opCtx.get? name = some (Op.compare cmp))
    (ha : EvaluatesTo ctx env a va) (hb : EvaluatesTo ctx env b vb)
    (hty : va.ty = vb.ty) (hcmp : cmp va vb = some result) :
    EvaluatesTo ctx env (.op name [a, b]) (Val.bool result) := by
  refine EvaluatesTo.op_applyVals hop
    (EvaluatesList.cons ha (EvaluatesList.cons hb EvaluatesList.nil)) ?_
  rw [Op.applyVals_compare name cmp va vb hty, hcmp]
  rfl

theorem evaluates_compare_nat_literals_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String}
    {cmp : Val ctx.primCtx → Val ctx.primCtx → Option Bool}
    {a b : Nat} {result expected : Bool}
    (hop : ctx.opCtx.get? name = some (Op.compare cmp))
    (hcmp : cmp (Val.nat a) (Val.nat b) = some result) :
    EvaluatesTo ctx env (.op name [Term.nat a, Term.nat b]) (Val.bool expected) ↔
      result = expected := by
  simpa only [Val.bool_inj] using
    (EvaluatesTo.iff_eq_of (expected := Val.bool expected)
      (evaluates_compare hop (evaluates_nat env a) (evaluates_nat env b) rfl hcmp))

@[eval_semantic, zspec] theorem evaluates_eq_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "eq" [a, b]) (Val.bool (decide (m = n))) := by
  exact evaluates_compare (by simpa only [Op.eq] using Peano.Model.eqOp (ctx := ctx))
    ha hb rfl (Val.primEq?_nat m n)

@[eval_semantic, zspec] theorem evaluates_lt_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "lt" [a, b]) (Val.bool (decide (m < n))) := by
  exact evaluates_compare (Peano.Model.ltOp (ctx := ctx)) ha hb rfl (Val.primLt?_nat m n)

@[eval_semantic, zspec] theorem evaluates_gt_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat m)) (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "gt" [a, b]) (Val.bool (decide (n < m))) := by
  exact evaluates_compare (Peano.Model.gtOp (ctx := ctx)) ha hb rfl (Val.primGt?_nat m n)

theorem evaluates_succ_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a expected : Nat} :
    EvaluatesTo ctx env (.op "succ" [Term.nat a]) (Val.nat expected) ↔
      a + 1 = expected := by
  simpa only [Val.nat_inj, Nat.succ_eq_add_one] using
    (evaluates_natUnary_literal_iff (env := env) (a := a) (expected := Val.nat expected)
      (Peano.Model.succOp (ctx := ctx)))

theorem evaluates_add_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b expected : Nat} :
    EvaluatesTo ctx env (.op "add" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a + b = expected := by
  change EvaluatesTo ctx env (.op "add" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
    Nat.add a b = expected
  simpa only [Val.nat_inj] using
    (evaluates_natBinary_literals_iff (env := env) (a := a) (b := b)
      (expected := Val.nat expected) (Peano.Model.addOp (ctx := ctx)))

theorem evaluates_sub_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b expected : Nat} :
    EvaluatesTo ctx env (.op "sub" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a - b = expected := by
  change EvaluatesTo ctx env (.op "sub" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
    Nat.sub a b = expected
  simpa only [Val.nat_inj] using
    (evaluates_natBinary_literals_iff (env := env) (a := a) (b := b)
      (expected := Val.nat expected) (Peano.Model.subOp (ctx := ctx)))

theorem evaluates_mul_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b expected : Nat} :
    EvaluatesTo ctx env (.op "mul" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a * b = expected := by
  change EvaluatesTo ctx env (.op "mul" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
    Nat.mul a b = expected
  simpa only [Val.nat_inj] using
    (evaluates_natBinary_literals_iff (env := env) (a := a) (b := b)
      (expected := Val.nat expected) (Peano.Model.mulOp (ctx := ctx)))

theorem evaluates_div_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b expected : Nat} :
    EvaluatesTo ctx env (.op "div" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
      a / b = expected := by
  change EvaluatesTo ctx env (.op "div" [Term.nat a, Term.nat b]) (Val.nat expected) ↔
    Nat.div a b = expected
  simpa only [Val.nat_inj] using
    (evaluates_natBinary_literals_iff (env := env) (a := a) (b := b)
      (expected := Val.nat expected) (Peano.Model.divOp (ctx := ctx)))

theorem evaluates_eq_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Nat} {expected : Bool} :
    EvaluatesTo ctx env (.op "eq" [Term.nat a, Term.nat b]) (Val.bool expected) ↔
      decide (a = b) = expected := by
  simpa only [Op.eq, Val.primEq?_nat] using
    (evaluates_compare_nat_literals_iff (env := env) (a := a) (b := b)
      (expected := expected) (by simpa only [Op.eq] using Peano.Model.eqOp (ctx := ctx))
      (Val.primEq?_nat a b))

theorem evaluates_lt_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Nat} {expected : Bool} :
    EvaluatesTo ctx env (.op "lt" [Term.nat a, Term.nat b]) (Val.bool expected) ↔
      decide (a < b) = expected := by
  simpa only [Val.primLt?_nat] using
    (evaluates_compare_nat_literals_iff (env := env) (a := a) (b := b)
      (expected := expected) (Peano.Model.ltOp (ctx := ctx)) (Val.primLt?_nat a b))

theorem evaluates_gt_nat_iff {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Nat} {expected : Bool} :
    EvaluatesTo ctx env (.op "gt" [Term.nat a, Term.nat b]) (Val.bool expected) ↔
      decide (b < a) = expected := by
  simpa only [Val.primGt?_nat] using
    (evaluates_compare_nat_literals_iff (env := env) (a := a) (b := b)
      (expected := expected) (Peano.Model.gtOp (ctx := ctx)) (Val.primGt?_nat a b))

theorem evaluates_eq_same_nat_true {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat n))
    (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "eq" [a, b]) (Val.bool true) := by
  refine EvaluatesTo.op_applyVals (Peano.Model.eqOp (ctx := ctx))
    (EvaluatesList.cons ha (EvaluatesList.cons hb EvaluatesList.nil)) ?_
  simpa [Op.eq, Op.applyValsAt, Op.compare, Op.fixed, Val.primEq?] using
    (Op.applyVals_compare (primCtx := ctx.primCtx) (M := ctx.M) "eq" Val.primEq?
      (Val.nat (primCtx := ctx.primCtx) n) (Val.nat n) rfl)

/-! ### from evaluation to `Term.eq`

  `Term.eq` quantifies over every environment modelling the scope, so proving two terms equal at
  `Nat` means concretizing both under an arbitrary such environment. -/

theorem term_eq_nat_of_eval {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {lhs rhs : Term ctx.primCtx}
    (hlhs : Term.hasType ctx [] lhs Peano.NatTy)
    (hrhs : Term.hasType ctx [] rhs Peano.NatTy)
    (heval : ∀ env : Env ctx.primCtx, env.Models [] →
      ∃ n : Nat, EvaluatesTo ctx env lhs (Val.nat n) ∧
        EvaluatesTo ctx env rhs (Val.nat n)) :
    Term.eq ctx [] Peano.NatTy lhs rhs := by
  refine Term.eq.mk hlhs hrhs ?_
  intro env henv value
  obtain ⟨n, hl, hr⟩ := heval env henv
  constructor
  · intro hvalue
    have hsame : value = Val.nat (primCtx := ctx.primCtx) n := EvaluatesTo.unique hvalue hl
    subst value
    exact hr
  · intro hvalue
    have hsame : value = Val.nat (primCtx := ctx.primCtx) n := EvaluatesTo.unique hvalue hr
    subst value
    exact hl

/-! ### from a reflected equation back to evaluation

  `Pr.Induction`'s step goal hands the proof an equation `succ x = y` reflected into Zag. Both
  sides must be `Nat`-valued for the induction to say anything, and that is what this recovers. -/

private theorem evaluates_natUnary_result_nat {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {name : String} {arg : Term ctx.primCtx} {f : Nat → Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    {value : Val ctx.primCtx}
    (h : EvaluatesTo ctx env (.op name [arg]) value) :
    ∃ n : Nat, value = Val.nat (f n) := by
  let resume := Op.Body.resume?
    (((Op.natUnary (primCtx := ctx.primCtx) (M := ctx.M) f).body name 1).getD
      (Op.Body.fail : Op.Body ctx.primCtx))
  let base : List (Frame ctx.primCtx) := [Frame.opBody resume [] env]
  have hopId := Exact.idView_get?_of_get? hM hop
  have hbodyId : (Exact.idOp ctx hM
      (Op.natUnary (primCtx := ctx.primCtx) (M := ctx.M) f)).body name 1 =
      (Op.natUnary (primCtx := ctx.primCtx) (M := ctx.M) f).body name 1 :=
    Exact.idOp_property ctx hM _
      (fun _ oper => oper.body name 1 =
        (Op.natUnary (primCtx := ctx.primCtx) (M := ctx.M) f).body name 1) rfl
  have hfrom : EvaluatesFrom ctx (Machine.start env (.op name [arg])) value [] := by
    simpa [Machine.start] using h []
  have hprefix : Id.run (Machine.nsteps (Exact.idView ctx hM) 1
      (Machine.start env (.op name [arg]))).run =
      some (Machine.appendStack (Machine.start env arg) base) := by
    simp only [Machine.nsteps, Machine.start, Machine.step, Machine.evalTerm,
      hopId, Machine.driveSelectedOp]
    simp only [List.length_cons, List.length_nil]
    rw [hbodyId]
    simp [Machine.ofOption, Machine.driveOp, Machine.appendStack, base, resume, Op.Body.resume?,
      Op.natUnary, Op.ofVals, Op.Body.eager, Op.fixed, Id.run,
      Pure.pure, Bind.bind, OptionT.mk, OptionT.bind, OptionT.pure, OptionT.run]
  have hfromArgState := EvaluatesFrom.afterNsteps hprefix hfrom
  have hfromArgStateSaved := hfromArgState
  obtain ⟨argVal, hargFrom⟩ := EvaluatesFrom.existsOfAppendOpBodies
    (ctx := ctx) (state := Machine.start env arg) (base := base)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [base])
    (by simpa [Machine.start, Machine.appendStack] using hfromArgState)
  have harg : EvaluatesTo ctx env arg argVal := EvaluatesTo.ofEvaluatesFrom hargFrom
  obtain ⟨argFuel, argScope, hargSteps⟩ := EvaluatesFrom.toNsteps (harg base) trivial
  have hfromRetArg := EvaluatesFrom.afterNsteps hargSteps hfromArgStateSaved
  cases hm : argVal.asNat? with
  | none =>
      obtain ⟨next, hnext⟩ := EvaluatesFrom.existsPureStep
        (hnotDone := by intros; simp [base]) hfromRetArg
      simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
        base, resume, Op.Body.resume?, Op.natUnary, Op.ofVals, Op.Body.eager,
        Op.fixed, hm] at hnext
      have hfalse := congrArg (fun action => Id.run action.run) hnext
      simp at hfalse
  | some n =>
      have hargNat : argVal = Val.nat n := Val.eq_nat_of_asNat? hm
      subst argVal
      have hstepRet : Machine.step (Exact.idView ctx hM)
          ⟨.ret (Val.nat (primCtx := ctx.primCtx) n), argScope, base⟩ =
          Machine.ofOption (Exact.idView ctx hM)
            (some ⟨.ret (Val.nat (primCtx := ctx.primCtx) (f n)), env, []⟩) := by
        simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
          base, resume, Op.Body.resume?, Op.natUnary, Op.ofVals, Op.Body.eager,
          Op.fixed]
      have hfromResult := EvaluatesFrom.afterPureStep
        (hnotDone := by intros; simp [base]) hstepRet hfromRetArg
      have hvalue := EvaluatesFrom.retEmptyEq hfromResult
      exact ⟨n, hvalue⟩

theorem eval_nat_of_eq_natUnary_true {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {name : String} {arg rhs : Term ctx.primCtx} {f : Nat → Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (h : EvaluatesTo ctx env (.op "eq" [.op name [arg], rhs]) (Val.bool true)) :
    ∃ n : Nat, EvaluatesTo ctx env rhs (Val.nat n) := by
  let lhs := Term.op name [arg]
  let firstResume := Op.Body.resume?
    (((Op.eq (primCtx := ctx.primCtx) (M := ctx.M)).body "eq" 2).getD
      (Op.Body.fail : Op.Body ctx.primCtx))
  let firstBase : List (Frame ctx.primCtx) :=
    [Frame.opBody firstResume (Op.Arg.ofTerms [rhs]) env]
  have heqId := Exact.idView_get?_of_get? hM (Peano.Model.eqOp (ctx := ctx))
  have heqBodyId : (Exact.idOp ctx hM
      (Op.eq (primCtx := ctx.primCtx) (M := ctx.M))).body "eq" 2 =
      (Op.eq (primCtx := ctx.primCtx) (M := ctx.M)).body "eq" 2 :=
    Exact.idOp_property ctx hM _
      (fun _ oper => oper.body "eq" 2 =
        (Op.eq (primCtx := ctx.primCtx) (M := ctx.M)).body "eq" 2) rfl
  have hfrom : EvaluatesFrom ctx (Machine.start env (.op "eq" [lhs, rhs]))
      (Val.bool true) [] := by
    simpa [Machine.start, lhs] using h []
  have hprefix : Id.run (Machine.nsteps (Exact.idView ctx hM) 1
      (Machine.start env (.op "eq" [lhs, rhs]))).run =
      some (Machine.appendStack (Machine.start env lhs) firstBase) := by
    simp only [Machine.nsteps, Machine.start, Machine.step, Machine.evalTerm,
      heqId, Machine.driveSelectedOp]
    simp only [List.length_cons, List.length_nil]
    rw [heqBodyId]
    simp [Machine.ofOption, Machine.driveOp, Machine.appendStack, firstBase, firstResume, lhs,
      Op.Body.resume?, Op.eq, Op.compare, Op.fixed, Id.run, Pure.pure,
      Bind.bind, OptionT.mk, OptionT.bind, OptionT.pure, OptionT.run]
  have hfromLhsState := EvaluatesFrom.afterNsteps hprefix hfrom
  have hfromLhsStateSaved := hfromLhsState
  obtain ⟨lhsVal, hlhsFrom⟩ := EvaluatesFrom.existsOfAppendOpBodies
    (ctx := ctx) (state := Machine.start env lhs) (base := firstBase)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [firstBase])
    (by simpa [Machine.start, Machine.appendStack] using hfromLhsState)
  have hlhs : EvaluatesTo ctx env lhs lhsVal := EvaluatesTo.ofEvaluatesFrom hlhsFrom
  obtain ⟨m, hlhsVal⟩ := evaluates_natUnary_result_nat (ctx := ctx) (env := env)
    (name := name) (arg := arg) (f := f) hop (value := lhsVal) hlhs
  subst lhsVal
  let secondResume := Op.Body.resume? (firstResume (some (Val.nat (primCtx := ctx.primCtx) (f m))))
  let secondBase : List (Frame ctx.primCtx) := [Frame.opBody secondResume [] env]
  obtain ⟨lhsEvalFuel, lhsEvalScope, hlhsEvalSteps⟩ :=
    EvaluatesFrom.toNsteps (hlhs firstBase) trivial
  have hfromRetLhs := EvaluatesFrom.afterNsteps hlhsEvalSteps hfromLhsStateSaved
  have hstepLhsRet : Machine.step (Exact.idView ctx hM)
      ⟨.ret (Val.nat (primCtx := ctx.primCtx) (f m)), lhsEvalScope, firstBase⟩ =
      Machine.ofOption (Exact.idView ctx hM)
        (some (Machine.appendStack (Machine.start env rhs) secondBase)) := by
    simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
      Machine.appendStack, Machine.start, firstBase, secondBase, firstResume,
      secondResume, Op.Body.resume?, Op.eq, Op.compare, Op.fixed]
  have hfromRhsState := EvaluatesFrom.afterPureStep
    (hnotDone := by intros; simp [firstBase]) hstepLhsRet hfromRetLhs
  have hfromRhsStateSaved := hfromRhsState
  obtain ⟨rhsVal, hrhsFrom⟩ := EvaluatesFrom.existsOfAppendOpBodies
    (ctx := ctx) (state := Machine.start env rhs) (base := secondBase)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [secondBase])
    (by simpa [Machine.start, Machine.appendStack] using hfromRhsState)
  have hrhs : EvaluatesTo ctx env rhs rhsVal := EvaluatesTo.ofEvaluatesFrom hrhsFrom
  obtain ⟨rhsEvalFuel, rhsEvalScope, hrhsEvalSteps⟩ :=
    EvaluatesFrom.toNsteps (hrhs secondBase) trivial
  have hfromRetRhs := EvaluatesFrom.afterNsteps hrhsEvalSteps hfromRhsStateSaved
  by_cases hty : (Val.nat (primCtx := ctx.primCtx) (f m)).ty = rhsVal.ty
  · have hrhsTy : rhsVal.ty = Peano.NatTy := by simpa using hty.symm
    obtain ⟨n, hn⟩ := Val.exists_nat_of_ty hrhsTy
    exact ⟨n, by simpa [hn] using hrhs⟩
  · obtain ⟨next, hnext⟩ := EvaluatesFrom.existsPureStep
      (hnotDone := by intros; simp [secondBase]) hfromRetRhs
    simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
      secondBase, secondResume, firstResume, Op.Body.resume?, Op.eq, Op.compare,
      Op.fixed, show ¬ Peano.NatTy = rhsVal.ty by simpa using hty] at hnext
    have hfalse := congrArg (fun action => Id.run action.run) hnext
    simp at hfalse

theorem eval_nat_of_reflected_natUnary_eq {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {name : String} {f : Nat → Nat} {arg rhs : Term ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (heq : Term.eq ctx [] Peano.BoolTy (.op "eq" [.op name [arg], rhs]) (Term.bool true)) :
    ∀ env : Env ctx.primCtx, env.Models [] →
      ∃ n : Nat, EvaluatesTo ctx env rhs (Val.nat n) := by
  intro env henv
  refine eval_nat_of_eq_natUnary_true (arg := arg) hop ?_
  have htrue : EvaluatesTo ctx env (Term.bool true) (Val.bool true) := by
    simpa [Term.bool] using
      (EvaluatesTo.prim (ctx := ctx) (env := env) Peano.BoolTy
        (Ty.ofBool ctx.primCtx true))
  exact (heq.eq env henv (Val.bool true)).mpr htrue

end EvalTriple.Exact

export EvalTriple.Exact (evaluates_nat evaluates_bool evaluates_natUnary evaluates_natBinary
  evaluates_succ_nat evaluates_add_nat evaluates_sub_nat evaluates_mul_nat evaluates_div_nat
  evaluates_natUnary_literal_iff evaluates_natBinary_literals_iff evaluates_compare
  evaluates_compare_nat_literals_iff evaluates_eq_nat evaluates_lt_nat evaluates_gt_nat
  evaluates_succ_nat_iff evaluates_add_nat_iff evaluates_sub_nat_iff evaluates_mul_nat_iff
  evaluates_div_nat_iff evaluates_eq_nat_iff evaluates_lt_nat_iff evaluates_gt_nat_iff
  evaluates_eq_same_nat_true term_eq_nat_of_eval eval_nat_of_eq_natUnary_true
  eval_nat_of_reflected_natUnary_eq)

/-! ### continuation-passing `while` -/

namespace Peano

namespace Exact

open EvalTriple.Exact

variable {primCtx : PrimitiveCtx} [Peano.Types primCtx]

def whileCondRef (condName : String) (stateTys : List Ty) : Val primCtx :=
  .blockRef condName stateTys Peano.BoolTy

def whileBodyRef (bodyName : String) (stateTys : List Ty) (resultTy : Ty) : Val primCtx :=
  .blockRef bodyName (stateTys ++ [.func stateTys resultTy]) resultTy

def whileRef (opName condName bodyName : String) (stateTys : List Ty) (resultTy : Ty) :
    Val primCtx :=
  .opRef opName [whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy]
    stateTys resultTy

private theorem while_apply_continue {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {args : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hheadTy : stateTys.head? = some resultTy)
    (htys : args.map Val.ty = stateTys)
    (hcond : EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true))
    (hbody : EvalTriple.Exact.EvaluatesCallValues ctx bodyName
      (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult) :
    EvalTriple.Exact.EvaluatesApply ctx
      (whileRef opName condName bodyName stateTys resultTy) args loopResult := by
  have hne : args ≠ [] := by
    intro hnil
    subst args
    simp at htys
    simp [htys] at hheadTy
  obtain ⟨head, tail, hargs⟩ : ∃ head tail, args = head :: tail := by
    cases args with
    | nil => exact (hne rfl).elim
    | cons head tail => exact ⟨head, tail, rfl⟩
  have hhead : args.head? = some head := by simp [hargs]
  have hcondApply : EvalTriple.Exact.EvaluatesApply ctx
      (whileCondRef condName stateTys) args (Val.bool true) :=
    EvalTriple.Exact.EvaluatesApply.blockRef hcond
  have hbodyApply : EvalTriple.Exact.EvaluatesApply ctx
      (whileBodyRef bodyName stateTys resultTy)
      (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult :=
    EvalTriple.Exact.EvaluatesApply.blockRef hbody
  apply EvalTriple.Exact.EvaluatesApply.opRef
    (body := Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
      (2 + args.length) []) hop
  · rfl
  · have hthree : 3 ≤ 2 + args.length := by
      cases args with
      | nil => exact (hne rfl).elim
      | cons => simp; omega
    change (if 3 ≤ 2 + args.length then
      some (Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
        (2 + args.length) []) else none) = _
    rw [if_pos hthree]
  · intro env base
    have hout : Op.whileResultTy? (primCtx := ctx.primCtx)
        (.func stateTys Peano.BoolTy ::
          .func (stateTys ++ [.func stateTys resultTy]) resultTy :: stateTys) =
          some resultTy := by
      simp [Op.whileResultTy?, hheadTy]
    obtain ⟨bodyStart, hbodyDrive, hbodyFrom⟩ :=
      EvalTriple.Exact.EvaluatesFrom.driveOp_apply
        (env := env) (stack := base) (operands := [])
        (resume := fun value => .done value) hbodyApply
        (hdrive := by simp [Machine.driveOp])
        (EvalTriple.Exact.EvaluatesFrom.done
          (ctx := ctx) (value := loopResult) (scope := env) (base := base))
    obtain ⟨condStart, hcondDrive, hcondFrom⟩ :=
      EvalTriple.Exact.EvaluatesFrom.driveOp_apply
        (env := env) (stack := base) (operands := [])
        (resume := fun condition =>
          match condition.asBool? with
          | some false => .done head
          | some true =>
              .apply (whileBodyRef bodyName stateTys resultTy)
                (args ++ [whileRef opName condName bodyName stateTys resultTy]) .done
          | none => .fail) hcondApply
        (hdrive := by
          simpa only [Val.asBool?_bool] using hbodyDrive) hbodyFrom
    refine ⟨condStart, ?_, hcondFrom⟩
    have hlen :
        ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ args).length =
          2 + args.length := by simp; omega
    rw [Machine.driveOp_collect _ _ _ hlen]
    have hfinish :
        Op.whileBodyFromValues (primCtx := ctx.primCtx) opName
            ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ args) =
          .apply (whileCondRef condName stateTys) args (fun condition =>
            match condition.asBool? with
            | some false => .done head
            | some true =>
                .apply (whileBodyRef bodyName stateTys resultTy)
                  (args ++ [whileRef opName condName bodyName stateTys resultTy]) .done
            | none => .fail) := by
      simp [Op.whileBodyFromValues, hout, hhead, htys,
        whileCondRef, whileBodyRef, whileRef]
      funext condition
      unfold Op.whileAfterCondition
      rw [htys]
      rfl
    simp only [List.nil_append]
    rw [hfinish]
    exact hcondDrive

private theorem while_apply_exit {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {args : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hheadTy : stateTys.head? = some resultTy)
    (htys : args.map Val.ty = stateTys)
    (hcond : EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false))
    (hhead : args.head? = some loopResult) :
    EvalTriple.Exact.EvaluatesApply ctx
      (whileRef opName condName bodyName stateTys resultTy) args loopResult := by
  have hne : args ≠ [] := by
    intro hnil
    subst args
    simp at hhead
  have hcondApply : EvalTriple.Exact.EvaluatesApply ctx
      (whileCondRef condName stateTys) args (Val.bool false) :=
    EvalTriple.Exact.EvaluatesApply.blockRef hcond
  apply EvalTriple.Exact.EvaluatesApply.opRef
    (body := Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
      (2 + args.length) []) hop
  · rfl
  · have hthree : 3 ≤ 2 + args.length := by
      cases args with
      | nil => exact (hne rfl).elim
      | cons => simp; omega
    change (if 3 ≤ 2 + args.length then
      some (Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
        (2 + args.length) []) else none) = _
    rw [if_pos hthree]
  · intro env base
    have hout : Op.whileResultTy? (primCtx := ctx.primCtx)
        (.func stateTys Peano.BoolTy ::
          .func (stateTys ++ [.func stateTys resultTy]) resultTy :: stateTys) =
          some resultTy := by
      simp [Op.whileResultTy?, hheadTy]
    obtain ⟨condStart, hcondDrive, hcondFrom⟩ :=
      EvalTriple.Exact.EvaluatesFrom.driveOp_apply
        (env := env) (stack := base) (operands := [])
        (resume := fun condition =>
          match condition.asBool? with
          | some false => .done loopResult
          | some true =>
              .apply (whileBodyRef bodyName stateTys resultTy)
                (args ++ [whileRef opName condName bodyName stateTys resultTy]) .done
          | none => .fail) hcondApply
        (hdrive := by simp only [Val.asBool?_bool, Machine.driveOp])
        (EvalTriple.Exact.EvaluatesFrom.done
          (ctx := ctx) (value := loopResult) (scope := env) (base := base))
    refine ⟨condStart, ?_, hcondFrom⟩
    have hlen :
        ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ args).length =
          2 + args.length := by simp; omega
    rw [Machine.driveOp_collect _ _ _ hlen]
    have hfinish :
        Op.whileBodyFromValues (primCtx := ctx.primCtx) opName
            ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ args) =
          .apply (whileCondRef condName stateTys) args (fun condition =>
            match condition.asBool? with
            | some false => .done loopResult
            | some true =>
                .apply (whileBodyRef bodyName stateTys resultTy)
                  (args ++ [whileRef opName condName bodyName stateTys resultTy]) .done
            | none => .fail) := by
      simp [Op.whileBodyFromValues, hout, hhead, htys,
        whileCondRef, whileBodyRef, whileRef]
      funext condition
      unfold Op.whileAfterCondition
      rw [htys]
      rfl
    simp only [List.nil_append]
    rw [hfinish]
    exact hcondDrive

/- A finite invariant rule for the ordinary `while` operator. `N` is the total-correctness
  termination witness: the rule proves exactly `N` true-condition iterations followed by the
  false-condition exit, rather than taking a separate decreasing variant function. One body call
  receives the loop continuation as its final argument. Its premise is continuation-parametric:
  after proving the simultaneous next state satisfies the invariant, the body may use the supplied
  application specification and return the recursive answer through its own call frame. -/
theorem while_invariant {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hheadTy : stateTys.head? = some resultTy)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = stateTys)
    (preserved : ∀ n args, n < N → I n args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvalTriple.Exact.EvaluatesApply ctx
            (whileRef opName condName bodyName stateTys resultTy)
            nextArgs loopResult) →
        EvalTriple.Exact.EvaluatesCallValues ctx bodyName
          (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult))
    (exits : ∀ args, I N args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false) ∧
        args.head? = some loopResult) :
    EvalTriple.Exact.EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
      initial loopResult := by
  apply EvalTriple.Exact.EvaluatesApply.loop init
  · intro n args hn hI hnext
    obtain ⟨hcond, hbody⟩ := preserved n args hn hI
    exact while_apply_continue hop hheadTy (typed n args hI) hcond (hbody hnext)
  · intro args hI
    obtain ⟨hcond, hhead⟩ := exits args hI
    exact while_apply_exit hop hheadTy (typed N args hI) hcond hhead

/- A variant-style rule matching `Std.Do.WhileInvariant`/`WhileVariant`. The condition/body pair is
  still Zag's continuation-passing operator step: a true condition calls the body with the loop
  continuation, and the body may use the recursive hypothesis only at strictly smaller variants. -/
theorem while_variant {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    (measure : Std.Do.WhileVariant (List (Val ctx.primCtx)) .pure)
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure)
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hheadTy : stateTys.head? = some resultTy)
    (init : (inv.1 (.inl initial)).down)
    (typed : ∀ args, (inv.1 (.inl args)).down → args.map Val.ty = stateTys)
    (step : ∀ args ma,
      (Std.Do.WhileVariant.eval measure args ma).down →
      (inv.1 (.inl args)).down →
        (EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true) ∧
          ((∀ nextArgs ma',
              (Std.Do.WhileVariant.eval measure nextArgs ma').down →
              ma' < ma →
              (inv.1 (.inl nextArgs)).down →
              EvalTriple.Exact.EvaluatesApply ctx
                (whileRef opName condName bodyName stateTys resultTy)
                nextArgs loopResult) →
            EvalTriple.Exact.EvaluatesCallValues ctx bodyName
              (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult)) ∨
        (EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false) ∧
          args.head? = some loopResult ∧ (inv.1 (.inr loopResult)).down)) :
    EvalTriple.Exact.EvaluatesApply ctx
      (whileRef opName condName bodyName stateTys resultTy) initial loopResult := by
  suffices hloop : ∀ ma args,
      (Std.Do.WhileVariant.eval measure args ma).down →
      (inv.1 (.inl args)).down →
      EvalTriple.Exact.EvaluatesApply ctx
        (whileRef opName condName bodyName stateTys resultTy) args loopResult by
    exact hloop (measure initial).down initial (by simp [Std.Do.WhileVariant.eval]) init
  intro ma
  induction ma using Nat.strongRecOn with
  | ind ma ih =>
      intro args hmeasure hI
      cases step args ma hmeasure hI with
      | inl hcontinue =>
          obtain ⟨hcond, hbody⟩ := hcontinue
          exact while_apply_continue hop hheadTy (typed args hI) hcond (hbody (fun nextArgs ma' hma' hlt hnextI =>
            ih ma' hlt nextArgs hma' hnextI))
      | inr hexit =>
          obtain ⟨hcond, hhead, _hdone⟩ := hexit
          exact while_apply_exit hop hheadTy (typed args hI) hcond hhead

/- The term-level entry rule for a registered while operator. The initial operands are evaluated by
the enclosing operator; recursive iterations use the continuation specification from
`while_invariant`. -/
theorem while_evaluatesToWithOpName {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {operands : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hargs : EvalTriple.Exact.EvaluatesList ctx env operands
      ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ initial))
    (hheadTy : stateTys.head? = some resultTy)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = stateTys)
    (preserved : ∀ n args, n < N → I n args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvalTriple.Exact.EvaluatesApply ctx
            (whileRef opName condName bodyName stateTys resultTy)
            nextArgs loopResult) →
        EvalTriple.Exact.EvaluatesCallValues ctx bodyName
          (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult))
    (exits : ∀ args, I N args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false) ∧
        args.head? = some loopResult) :
    EvalTriple.Exact.EvaluatesTo ctx env (.op opName operands) loopResult := by
  have htys := typed 0 initial init
  have hne : initial ≠ [] := by
    intro hnil
    subst initial
    simp at htys
    simp [htys] at hheadTy
  have hone : 1 ≤ initial.length := by
    cases initial with
    | nil => exact (hne rfl).elim
    | cons => simp
  apply EvalTriple.Exact.EvaluatesTo.op_collect_of_opRef
      (captured := [whileCondRef condName stateTys,
        whileBodyRef bodyName stateTys resultTy])
      (args := initial) (argTys := stateTys) (outTy := resultTy)
      (finish := Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
      hop rfl (by simp [Op.whileOp]; omega) hargs
  exact while_invariant (I := I) (N := N) (loopResult := loopResult)
    hop hheadTy init typed preserved exits

/- Public rule for the surface `while [cond, body] (state...)` operator. The conclusion exposes the
condition/body names and state terms, so ordinary theorem application can infer them from the goal.
The finite count `N` is the termination witness. -/
@[zspec] theorem while_evaluatesTo {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {condName bodyName : String} {condBlock bodyBlock : Block ctx.primCtx}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stateTerms : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) := by
      first | rfl | simp)
    (hcondLocal : Scope.get? env condName = none := by
      first | rfl | simp [Scope.get?])
    (hbodyLocal : Scope.get? env bodyName = none := by
      first | rfl | simp [Scope.get?])
    (hcondBlock : ctx.blockCtx.get? condName = some condBlock := by
      first | rfl | simp)
    (hbodyBlock : ctx.blockCtx.get? bodyName = some bodyBlock := by
      first | rfl | simp)
    (hcondOut : condBlock.outTy = Peano.BoolTy := by
      first | rfl | simp)
    (hheadTy : (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy := by
      first | rfl | simp)
    (hbodyParams : bodyBlock.params.map Prod.snd =
      condBlock.params.map Prod.snd ++ [.func (condBlock.params.map Prod.snd) bodyBlock.outTy] := by
      first | rfl | simp)
    (hargs : EvalTriple.Exact.EvaluatesList ctx env stateTerms initial)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = condBlock.params.map Prod.snd)
    (preserved : ∀ n args, n < N → I n args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvalTriple.Exact.EvaluatesApply ctx
            (whileRef "while" condName bodyName (condBlock.params.map Prod.snd) bodyBlock.outTy)
            nextArgs loopResult) →
        EvalTriple.Exact.EvaluatesCallValues ctx bodyName
          (args ++ [whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
            bodyBlock.outTy]) loopResult))
    (exits : ∀ args, I N args →
      EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false) ∧
        args.head? = some loopResult) :
    EvalTriple.Exact.EvaluatesTo ctx env
      (.op "while" (.var condName :: .var bodyName :: stateTerms)) loopResult hM := by
  apply while_evaluatesToWithOpName (opName := "while") (condName := condName)
    (bodyName := bodyName) (stateTys := condBlock.params.map Prod.snd)
    (resultTy := bodyBlock.outTy) (I := I) (N := N) (initial := initial)
    (loopResult := loopResult)
  · exact hop
  · exact EvalTriple.Exact.EvaluatesList.cons
      (EvalTriple.Exact.EvaluatesTo.of_eq
        (EvalTriple.Exact.EvaluatesTo.var_block hcondLocal hcondBlock)
        (by simp [whileCondRef, hcondOut]))
      (EvalTriple.Exact.EvaluatesList.cons
        (EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.EvaluatesTo.var_block hbodyLocal hbodyBlock)
          (by simp [whileBodyRef, hbodyParams]))
        hargs)
  · exact hheadTy
  · exact init
  · exact typed
  · exact preserved
  · exact exits

theorem while_evaluatesTo_variant {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {condName bodyName : String} {condBlock bodyBlock : Block ctx.primCtx}
    (measure : Std.Do.WhileVariant (List (Val ctx.primCtx)) .pure)
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure)
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stateTerms : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) := by
      first | rfl | simp)
    (hcondLocal : Scope.get? env condName = none := by
      first | rfl | simp [Scope.get?])
    (hbodyLocal : Scope.get? env bodyName = none := by
      first | rfl | simp [Scope.get?])
    (hcondBlock : ctx.blockCtx.get? condName = some condBlock := by
      first | rfl | simp)
    (hbodyBlock : ctx.blockCtx.get? bodyName = some bodyBlock := by
      first | rfl | simp)
    (hcondOut : condBlock.outTy = Peano.BoolTy := by
      first | rfl | simp)
    (hheadTy : (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy := by
      first | rfl | simp)
    (hbodyParams : bodyBlock.params.map Prod.snd =
      condBlock.params.map Prod.snd ++ [.func (condBlock.params.map Prod.snd) bodyBlock.outTy] := by
      first | rfl | simp)
    (hargs : EvalTriple.Exact.EvaluatesList ctx env stateTerms initial)
    (init : (inv.1 (.inl initial)).down)
    (typed : ∀ args,
      (inv.1 (.inl args)).down → args.map Val.ty = condBlock.params.map Prod.snd)
    (step : ∀ args ma,
      (Std.Do.WhileVariant.eval measure args ma).down →
      (inv.1 (.inl args)).down →
        (EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool true) ∧
          ((∀ nextArgs ma',
              (Std.Do.WhileVariant.eval measure nextArgs ma').down →
              ma' < ma →
              (inv.1 (.inl nextArgs)).down →
              EvalTriple.Exact.EvaluatesApply ctx
                (whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
                  bodyBlock.outTy)
                nextArgs loopResult hM) →
            EvalTriple.Exact.EvaluatesCallValues ctx bodyName
              (args ++ [whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
                bodyBlock.outTy]) loopResult hM)) ∨
        (EvalTriple.Exact.EvaluatesCallValues ctx condName args (Val.bool false) ∧
          args.head? = some loopResult ∧ (inv.1 (.inr loopResult)).down)) :
    EvalTriple.Exact.EvaluatesTo ctx env
      (.op "while" (.var condName :: .var bodyName :: stateTerms)) loopResult hM := by
  have htys := typed initial init
  have hne : initial ≠ [] := by
    intro hnil
    subst initial
    simp at htys
    simp [htys] at hheadTy
  have hone : 1 ≤ initial.length := by
    cases initial with
    | nil => exact (hne rfl).elim
    | cons => simp
  apply EvalTriple.Exact.EvaluatesTo.op_collect_of_opRef
      (captured := [whileCondRef condName (condBlock.params.map Prod.snd),
        whileBodyRef bodyName (condBlock.params.map Prod.snd) bodyBlock.outTy])
      (args := initial) (argTys := condBlock.params.map Prod.snd) (outTy := bodyBlock.outTy)
      (finish := Op.whileBodyFromValues (primCtx := ctx.primCtx) "while")
      hop rfl (by simp [Op.whileOp]; omega)
  · exact EvalTriple.Exact.EvaluatesList.cons
      (EvalTriple.Exact.EvaluatesTo.of_eq
        (EvalTriple.Exact.EvaluatesTo.var_block hcondLocal hcondBlock)
        (by simp [whileCondRef, hcondOut]))
      (EvalTriple.Exact.EvaluatesList.cons
        (EvalTriple.Exact.EvaluatesTo.of_eq
          (EvalTriple.Exact.EvaluatesTo.var_block hbodyLocal hbodyBlock)
          (by simp [whileBodyRef, hbodyParams]))
        hargs)
  · exact while_variant (ctx := ctx) (hM := hM) (opName := "while")
      (condName := condName) (bodyName := bodyName)
      (stateTys := condBlock.params.map Prod.snd) (resultTy := bodyBlock.outTy)
      measure inv hop hheadTy init typed step

@[spec] theorem eval?_nat_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (n : Nat)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (Term.nat n) hM)
      (Q.1 (some (Val.nat n))) Q := by
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo (evaluates_nat env n) Q

@[spec] theorem eval?_bool_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    (env : Env ctx.primCtx) (b : Bool)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (Term.bool b) hM)
      (Q.1 (some (Val.bool b))) Q := by
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo (evaluates_bool env b) Q

@[spec] theorem eval?_add_nat_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "add" [a, b]) hM)
      ((Std.Do.wp (EvalTriple.Exact.eval? ctx env a hM)).apply
        (EvalTriple.somePost fun aValue =>
          (Std.Do.wp (EvalTriple.Exact.eval? ctx env b hM)).apply
            (EvalTriple.somePost fun bValue => Std.Do.SPred.pure
              (∃ m n : Nat, aValue = Val.nat m ∧ bValue = Val.nat n ∧
                (Q.1 (some (Val.nat (m + n)))).down)))) Q := by
  change _ → _
  intro hpre
  obtain ⟨aValue, ha, hbWp⟩ := EvalTriple.Exact.eval?_some_of_wp hpre
  obtain ⟨bValue, hb, hpost⟩ := EvalTriple.Exact.eval?_some_of_wp hbWp
  obtain ⟨m, n, haValue, hbValue, hQ⟩ := hpost
  subst aValue
  subst bValue
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo
    (evaluates_add_nat ha hb) Q hQ

@[spec] theorem eval?_sub_nat_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "sub" [a, b]) hM)
      ((Std.Do.wp (EvalTriple.Exact.eval? ctx env a hM)).apply
        (EvalTriple.somePost fun aValue =>
          (Std.Do.wp (EvalTriple.Exact.eval? ctx env b hM)).apply
            (EvalTriple.somePost fun bValue => Std.Do.SPred.pure
              (∃ m n : Nat, aValue = Val.nat m ∧ bValue = Val.nat n ∧
                (Q.1 (some (Val.nat (m - n)))).down)))) Q := by
  change _ → _
  intro hpre
  obtain ⟨aValue, ha, hbWp⟩ := EvalTriple.Exact.eval?_some_of_wp hpre
  obtain ⟨bValue, hb, hpost⟩ := EvalTriple.Exact.eval?_some_of_wp hbWp
  obtain ⟨m, n, haValue, hbValue, hQ⟩ := hpost
  subst aValue
  subst bValue
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo
    (evaluates_sub_nat ha hb) Q hQ

@[spec] theorem eval?_gt_nat_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx}
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "gt" [a, b]) hM)
      ((Std.Do.wp (EvalTriple.Exact.eval? ctx env a hM)).apply
        (EvalTriple.somePost fun aValue =>
          (Std.Do.wp (EvalTriple.Exact.eval? ctx env b hM)).apply
            (EvalTriple.somePost fun bValue => Std.Do.SPred.pure
              (∃ m n : Nat, aValue = Val.nat m ∧ bValue = Val.nat n ∧
                (Q.1 (some (Val.bool (decide (n < m))))).down)))) Q := by
  change _ → _
  intro hpre
  obtain ⟨aValue, ha, hbWp⟩ := EvalTriple.Exact.eval?_some_of_wp hpre
  obtain ⟨bValue, hb, hpost⟩ := EvalTriple.Exact.eval?_some_of_wp hbWp
  obtain ⟨m, n, haValue, hbValue, hQ⟩ := hpost
  subst aValue
  subst bValue
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo
    (evaluates_gt_nat ha hb) Q hQ

theorem eval?_add_nat_eq_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : Std.Do.Triple (EvalTriple.Exact.eval? ctx env a hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat m)))
    (hb : Std.Do.Triple (EvalTriple.Exact.eval? ctx env b hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat n))) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "add" [a, b]) hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat (m + n))) := by
  exact EvalTriple.Exact.eval?_eq_triple_of_evaluatesTo
    (evaluates_add_nat
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple ha)
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple hb))

theorem eval?_sub_nat_eq_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : Std.Do.Triple (EvalTriple.Exact.eval? ctx env a hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat m)))
    (hb : Std.Do.Triple (EvalTriple.Exact.eval? ctx env b hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat n))) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "sub" [a, b]) hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat (m - n))) := by
  exact EvalTriple.Exact.eval?_eq_triple_of_evaluatesTo
    (evaluates_sub_nat
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple ha)
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple hb))

theorem eval?_gt_nat_eq_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {m n : Nat}
    (ha : Std.Do.Triple (EvalTriple.Exact.eval? ctx env a hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat m)))
    (hb : Std.Do.Triple (EvalTriple.Exact.eval? ctx env b hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.nat n))) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env (.op "gt" [a, b]) hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool (decide (n < m)))) := by
  exact EvalTriple.Exact.eval?_eq_triple_of_evaluatesTo
    (evaluates_gt_nat
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple ha)
      (EvalTriple.Exact.evaluatesTo_of_eval?_triple hb))

theorem eval?_while_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {condName bodyName : String} {condBlock bodyBlock : Block ctx.primCtx}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stateTerms : List (Term ctx.primCtx)}
    (hargs : Std.Do.Triple (EvalTriple.Exact.evalList? ctx env stateTerms hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost initial))
    (hop : ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) := by
      first | rfl | simp)
    (hcondLocal : Scope.get? env condName = none := by
      first | rfl | simp [Scope.get?])
    (hbodyLocal : Scope.get? env bodyName = none := by
      first | rfl | simp [Scope.get?])
    (hcondBlock : ctx.blockCtx.get? condName = some condBlock := by
      first | rfl | simp)
    (hbodyBlock : ctx.blockCtx.get? bodyName = some bodyBlock := by
      first | rfl | simp)
    (hcondOut : condBlock.outTy = Peano.BoolTy := by
      first | rfl | simp)
    (hheadTy : (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy := by
      first | rfl | simp)
    (hbodyParams : bodyBlock.params.map Prod.snd =
      condBlock.params.map Prod.snd ++ [.func (condBlock.params.map Prod.snd) bodyBlock.outTy] := by
      first | rfl | simp)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = condBlock.params.map Prod.snd)
    (preserved : ∀ n args, n < N → I n args →
      Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
        (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool true)) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvalTriple.Exact.EvaluatesApply ctx
            (whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
              bodyBlock.outTy)
            nextArgs loopResult hM) →
        Std.Do.Triple (EvalTriple.Exact.callValues? ctx bodyName
          (args ++ [whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
            bodyBlock.outTy]) hM)
          (Std.Do.SPred.pure True) (EvalTriple.someEqPost loopResult)))
    (exits : ∀ args, I N args →
      Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
        (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool false)) ∧
        args.head? = some loopResult)
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env
        (.op "while" (.var condName :: .var bodyName :: stateTerms)) hM)
      (Q.1 (some loopResult)) Q := by
  have hargsRel := EvalTriple.Exact.evaluatesList_of_evalList?_triple hargs
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo
    (while_evaluatesTo (ctx := ctx) (hM := hM) (condName := condName)
      (bodyName := bodyName) (condBlock := condBlock) (bodyBlock := bodyBlock)
      (I := I) (N := N) (initial := initial) (loopResult := loopResult)
      (env := env) (stateTerms := stateTerms) (hop := hop)
      (hcondLocal := hcondLocal) (hbodyLocal := hbodyLocal)
      (hcondBlock := hcondBlock) (hbodyBlock := hbodyBlock)
      (hcondOut := hcondOut) (hheadTy := hheadTy)
      (hbodyParams := hbodyParams) (hargs := hargsRel) (init := init)
      (typed := typed)
      (preserved := by
        intro n args hn hI
        obtain ⟨hcond, hbody⟩ := preserved n args hn hI
        exact ⟨EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple hcond,
          fun hnext =>
            EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple (hbody hnext)⟩)
      (exits := by
        intro args hI
        obtain ⟨hcond, hhead⟩ := exits args hI
        exact ⟨EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple hcond, hhead⟩)) Q

theorem eval?_while_variant_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    {condName bodyName : String} {condBlock bodyBlock : Block ctx.primCtx}
    (measure : Std.Do.WhileVariant (List (Val ctx.primCtx)) .pure)
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure)
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stateTerms : List (Term ctx.primCtx)}
    (hargs : Std.Do.Triple (EvalTriple.Exact.evalList? ctx env stateTerms hM)
      (Std.Do.SPred.pure True) (EvalTriple.someEqPost initial))
    (hop : ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) := by
      first | rfl | simp)
    (hcondLocal : Scope.get? env condName = none := by
      first | rfl | simp [Scope.get?])
    (hbodyLocal : Scope.get? env bodyName = none := by
      first | rfl | simp [Scope.get?])
    (hcondBlock : ctx.blockCtx.get? condName = some condBlock := by
      first | rfl | simp)
    (hbodyBlock : ctx.blockCtx.get? bodyName = some bodyBlock := by
      first | rfl | simp)
    (hcondOut : condBlock.outTy = Peano.BoolTy := by
      first | rfl | simp)
    (hheadTy : (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy := by
      first | rfl | simp)
    (hbodyParams : bodyBlock.params.map Prod.snd =
      condBlock.params.map Prod.snd ++ [.func (condBlock.params.map Prod.snd) bodyBlock.outTy] := by
      first | rfl | simp)
    (init : (inv.1 (.inl initial)).down)
    (typed : ∀ args,
      (inv.1 (.inl args)).down → args.map Val.ty = condBlock.params.map Prod.snd)
    (step : ∀ args ma,
      (Std.Do.WhileVariant.eval measure args ma).down →
      (inv.1 (.inl args)).down →
        (Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
            (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool true)) ∧
          ((∀ nextArgs ma',
              (Std.Do.WhileVariant.eval measure nextArgs ma').down →
              ma' < ma →
              (inv.1 (.inl nextArgs)).down →
              EvalTriple.Exact.EvaluatesApply ctx
                (whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
                  bodyBlock.outTy)
                nextArgs loopResult hM) →
            Std.Do.Triple (EvalTriple.Exact.callValues? ctx bodyName
              (args ++ [whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
                bodyBlock.outTy]) hM)
              (Std.Do.SPred.pure True) (EvalTriple.someEqPost loopResult))) ∨
        (Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
            (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool false)) ∧
          args.head? = some loopResult ∧ (inv.1 (.inr loopResult)).down))
    (Q : Std.Do.PostCond (Option (Val ctx.primCtx)) .pure) :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env
        (.op "while" (.var condName :: .var bodyName :: stateTerms)) hM)
      (Q.1 (some loopResult)) Q := by
  have hargsRel := EvalTriple.Exact.evaluatesList_of_evalList?_triple hargs
  exact EvalTriple.Exact.eval?_triple_of_evaluatesTo
    (while_evaluatesTo_variant (ctx := ctx) (hM := hM) (condName := condName)
      (bodyName := bodyName) (condBlock := condBlock) (bodyBlock := bodyBlock)
      measure inv (initial := initial) (loopResult := loopResult)
      (env := env) (stateTerms := stateTerms) (hop := hop)
      (hcondLocal := hcondLocal) (hbodyLocal := hbodyLocal)
      (hcondBlock := hcondBlock) (hbodyBlock := hbodyBlock)
      (hcondOut := hcondOut) (hheadTy := hheadTy)
      (hbodyParams := hbodyParams) (hargs := hargsRel) (init := init)
      (typed := typed)
      (step := by
        intro args ma hmeasure hI
        cases step args ma hmeasure hI with
        | inl hcontinue =>
            obtain ⟨hcond, hbody⟩ := hcontinue
            exact Or.inl ⟨EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple hcond,
              fun hnext =>
                EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple (hbody hnext)⟩
        | inr hexit =>
            obtain ⟨hcond, hhead, hdone⟩ := hexit
            exact Or.inr
              ⟨EvalTriple.Exact.evaluatesCallValues_of_callValues?_triple hcond,
                hhead, hdone⟩)) Q

/-- Structural side conditions for the automation-friendly equality-post while wrapper. -/
abbrev evalWhileEqWf {ctx : Ctx} [Peano.Types ctx.primCtx] (env : Env ctx.primCtx)
    (operands : List (Term ctx.primCtx)) : Prop :=
  match operands with
  | .var condName :: .var bodyName :: _ =>
      ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) ∧
      Scope.get? env condName = none ∧
      Scope.get? env bodyName = none ∧
      (match ctx.blockCtx.get? condName, ctx.blockCtx.get? bodyName with
      | some condBlock, some bodyBlock =>
          condBlock.outTy = Peano.BoolTy ∧
          (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy ∧
          bodyBlock.params.map Prod.snd =
            condBlock.params.map Prod.snd ++
              [.func (condBlock.params.map Prod.snd) bodyBlock.outTy]
      | _, _ => False)
  | _ => False

/-- Type-preservation side condition for the equality-post while wrapper. -/
abbrev evalWhileEqTyped {ctx : Ctx}
    (operands : List (Term ctx.primCtx))
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure) : Prop :=
  match operands with
  | .var condName :: .var _ :: _ =>
      match ctx.blockCtx.get? condName with
      | some condBlock =>
          ∀ args, (inv.1 (.inl args)).down → args.map Val.ty = condBlock.params.map Prod.snd
      | none => False
  | _ => False

/-- Step side condition for the equality-post while wrapper. -/
abbrev evalWhileEqStep {ctx : Ctx} [Peano.Types ctx.primCtx] (hM : ctx.M = Id)
    (operands : List (Term ctx.primCtx))
    (measure : Std.Do.WhileVariant (List (Val ctx.primCtx)) .pure)
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure)
    (loopResult : Val ctx.primCtx) : Prop :=
  match operands with
  | .var condName :: .var bodyName :: _ =>
      match ctx.blockCtx.get? condName, ctx.blockCtx.get? bodyName with
      | some condBlock, some bodyBlock =>
          ∀ args ma,
            (Std.Do.WhileVariant.eval measure args ma).down →
            (inv.1 (.inl args)).down →
              (Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
                  (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool true)) ∧
                ((∀ nextArgs ma',
                    (Std.Do.WhileVariant.eval measure nextArgs ma').down →
                    ma' < ma →
                    (inv.1 (.inl nextArgs)).down →
                    EvalTriple.Exact.EvaluatesApply ctx
                      (whileRef "while" condName bodyName (condBlock.params.map Prod.snd)
                        bodyBlock.outTy)
                      nextArgs loopResult hM) →
                  Std.Do.Triple (EvalTriple.Exact.callValues? ctx bodyName
                    (args ++ [whileRef "while" condName bodyName
                      (condBlock.params.map Prod.snd) bodyBlock.outTy]) hM)
                    (Std.Do.SPred.pure True) (EvalTriple.someEqPost loopResult))) ∨
              Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
                (Std.Do.SPred.pure True) (EvalTriple.someEqPost (Val.bool false)) ∧
                args.head? = some loopResult ∧ (inv.1 (.inr loopResult)).down
      | _, _ => False
  | _ => False

/-- Automation-friendly equality-post wrapper for the variant-style while rule. -/
@[spec] theorem eval?_while_eq_spec {ctx : Ctx} {hM : ctx.M = Id} [Peano.Types ctx.primCtx]
    (measure : Std.Do.WhileVariant (List (Val ctx.primCtx)) .pure)
    (inv : Std.Do.WhileInvariant (List (Val ctx.primCtx)) (Val ctx.primCtx) .pure)
    {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {operands : List (Term ctx.primCtx)}
    {wf : evalWhileEqWf (ctx := ctx) env operands}
    {typed : evalWhileEqTyped (ctx := ctx) operands inv}
    {step : evalWhileEqStep (ctx := ctx) hM operands measure inv loopResult} :
    Std.Do.Triple (EvalTriple.Exact.eval? ctx env
        (.op "while" operands) hM)
      ((Std.Do.wp (EvalTriple.Exact.evalList? ctx env (operands.drop 2) hM)).apply
        (EvalTriple.somePost fun initial => inv.1 (.inl initial)))
      (EvalTriple.someEqPost loopResult) := by
  rw [Std.Do.Triple.iff]
  intro hpre
  cases operands with
  | nil =>
      simp [evalWhileEqWf] at wf
  | cons first rest =>
      cases first with
      | var condName =>
          cases rest with
          | nil =>
              simp [evalWhileEqWf] at wf
          | cons second stateTerms =>
              cases second with
              | var bodyName =>
                  cases hcondBlock : ctx.blockCtx.get? condName with
                  | none =>
                      simp [evalWhileEqWf, hcondBlock] at wf
                  | some condBlock =>
                      cases hbodyBlock : ctx.blockCtx.get? bodyName with
                      | none =>
                          simp [evalWhileEqWf, hcondBlock, hbodyBlock] at wf
                      | some bodyBlock =>
                          have hpre' : ((Std.Do.wp
                              (EvalTriple.Exact.evalList? ctx env stateTerms hM)).apply
                              (EvalTriple.somePost fun initial => inv.1 (.inl initial))).down := by
                            simpa using hpre
                          have hwf :
                              ctx.opCtx.get? "while" = some (Op.whileOp (primCtx := ctx.primCtx)) ∧
                              Scope.get? env condName = none ∧
                              Scope.get? env bodyName = none ∧
                              condBlock.outTy = Peano.BoolTy ∧
                              (condBlock.params.map Prod.snd).head? = some bodyBlock.outTy ∧
                              bodyBlock.params.map Prod.snd =
                                condBlock.params.map Prod.snd ++
                                  [.func (condBlock.params.map Prod.snd) bodyBlock.outTy] := by
                            simpa [evalWhileEqWf, hcondBlock, hbodyBlock] using wf
                          obtain ⟨hop, hcondLocal, hbodyLocal, hcondOut, hheadTy, hbodyParams⟩ := hwf
                          have htyped : ∀ args,
                              (inv.1 (.inl args)).down →
                                args.map Val.ty = condBlock.params.map Prod.snd := by
                            simpa [evalWhileEqTyped, hcondBlock] using typed
                          have hstep : ∀ args ma,
                              (Std.Do.WhileVariant.eval measure args ma).down →
                              (inv.1 (.inl args)).down →
                                (Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
                                    (Std.Do.SPred.pure True)
                                    (EvalTriple.someEqPost (Val.bool true)) ∧
                                  ((∀ nextArgs ma',
                                      (Std.Do.WhileVariant.eval measure nextArgs ma').down →
                                      ma' < ma →
                                      (inv.1 (.inl nextArgs)).down →
                                      EvalTriple.Exact.EvaluatesApply ctx
                                        (whileRef "while" condName bodyName
                                          (condBlock.params.map Prod.snd) bodyBlock.outTy)
                                        nextArgs loopResult hM) →
                                    Std.Do.Triple (EvalTriple.Exact.callValues? ctx bodyName
                                      (args ++ [whileRef "while" condName bodyName
                                        (condBlock.params.map Prod.snd) bodyBlock.outTy]) hM)
                                      (Std.Do.SPred.pure True)
                                      (EvalTriple.someEqPost loopResult))) ∨
                                Std.Do.Triple (EvalTriple.Exact.callValues? ctx condName args hM)
                                  (Std.Do.SPred.pure True)
                                  (EvalTriple.someEqPost (Val.bool false)) ∧
                                  args.head? = some loopResult ∧
                                  (inv.1 (.inr loopResult)).down := by
                            simpa [evalWhileEqStep, hcondBlock, hbodyBlock] using step
                          obtain ⟨initial, hargsRel, hinit⟩ :=
                            EvalTriple.Exact.evalList?_some_of_wp hpre'
                          exact (eval?_while_variant_spec (ctx := ctx) (hM := hM)
                            (condName := condName) (bodyName := bodyName)
                            (condBlock := condBlock) (bodyBlock := bodyBlock)
                            measure inv (initial := initial) (loopResult := loopResult)
                            (env := env) (stateTerms := stateTerms)
                            (EvalTriple.Exact.evalList?_eq_triple_of_evaluatesList hargsRel)
                            (hop := hop) (hcondLocal := hcondLocal)
                            (hbodyLocal := hbodyLocal) (hcondBlock := hcondBlock)
                            (hbodyBlock := hbodyBlock) (hcondOut := hcondOut)
                            (hheadTy := hheadTy) (hbodyParams := hbodyParams)
                            (init := hinit) (typed := htyped) (step := hstep)
                            (Q := EvalTriple.someEqPost loopResult)) rfl
              | prim ty value =>
                  simp [evalWhileEqWf] at wf
              | app fn args =>
                  simp [evalWhileEqWf] at wf
              | «op» name args =>
                  simp [evalWhileEqWf] at wf
              | «call» name args =>
                  simp [evalWhileEqWf] at wf
              | «exit» name term =>
                  simp [evalWhileEqWf] at wf
      | prim ty value =>
          simp [evalWhileEqWf] at wf
      | app fn args =>
          simp [evalWhileEqWf] at wf
      | «op» name args =>
          simp [evalWhileEqWf] at wf
      | «call» name args =>
          simp [evalWhileEqWf] at wf
      | «exit» name term =>
          simp [evalWhileEqWf] at wf

end Exact

end Peano

end Zag
