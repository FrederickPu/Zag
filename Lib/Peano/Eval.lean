import Zag.Loop
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

theorem evaluates_natUnary {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat} {a : Term ctx.primCtx}
    {m : Nat} (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (ha : EvaluatesTo ctx env a (Val.nat m)) :
    EvaluatesTo ctx env (.op name [a]) (Val.nat (f m)) := by
  refine EvaluatesTo.op_applyVals hop (EvaluatesToAll.cons ha EvaluatesToAll.nil) ?_
  simp [Op.applyValsAt, Op.fixed, Op.natUnary, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

theorem evaluates_natBinary {ctx : Ctx} [Peano.Types ctx.primCtx]
    {env : Env ctx.primCtx} {name : String} {f : Nat → Nat → Nat}
    {a b : Term ctx.primCtx} {m n : Nat}
    (hop : ctx.opCtx.get? name = some (Op.natBinary (primCtx := ctx.primCtx) f))
    (ha : EvaluatesTo ctx env a (Val.nat m))
    (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op name [a, b]) (Val.nat (f m n)) := by
  refine EvaluatesTo.op_applyVals hop
    (EvaluatesToAll.cons ha (EvaluatesToAll.cons hb EvaluatesToAll.nil)) ?_
  simp [Op.applyValsAt, Op.fixed, Op.natBinary, Op.ofVals, Op.Body.applyVals, Op.Body.eager]

theorem evaluates_eq_same_nat_true {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {a b : Term ctx.primCtx} {n : Nat}
    (ha : EvaluatesTo ctx env a (Val.nat n))
    (hb : EvaluatesTo ctx env b (Val.nat n)) :
    EvaluatesTo ctx env (.op "eq" [a, b]) (Val.bool true) := by
  refine EvaluatesTo.op_applyVals (Peano.Model.eqOp (ctx := ctx))
    (EvaluatesToAll.cons ha (EvaluatesToAll.cons hb EvaluatesToAll.nil)) ?_
  simpa [Op.eq, Op.applyValsAt, Op.compare, Op.fixed, Val.primEq?] using
    (Op.applyVals_compare (primCtx := ctx.primCtx) "eq" Val.primEq?
      (Val.nat (primCtx := ctx.primCtx) n) (Val.nat n) rfl)

/-! ### from evaluation to `Term.eq`

  `Term.eq` quantifies over every environment modelling the scope, so proving two terms equal at
  `Nat` means concretizing both under an arbitrary such environment. -/

theorem term_eq_nat_of_eval {ctx : Ctx} [Peano.Types ctx.primCtx]
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

namespace Op.Body

private def resume? {primCtx : PrimitiveCtx} :
    Op.Body primCtx → Option (Val primCtx) → Op.Body primCtx
| .next _ resume => resume
| _ => fun _ => .fail

end Op.Body

private theorem evaluates_natUnary_result_nat {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {name : String} {arg : Term ctx.primCtx} {f : Nat → Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    {value : Val ctx.primCtx}
    (h : EvaluatesTo ctx env (.op name [arg]) value) :
    ∃ n : Nat, value = Val.nat (f n) := by
  let resume := Op.Body.resume?
    (((Op.natUnary (primCtx := ctx.primCtx) f).body name 1).getD
      (Op.Body.fail : Op.Body ctx.primCtx))
  let base : List (Frame ctx.primCtx) := [Frame.opBody resume [] env]
  have hfrom := EvaluatesFrom.of_evaluatesTo h
  have hprefix : EvalState.stepN ctx 1 (EvalState.start env (.op name [arg])) =
      some (EvalState.appendStack (EvalState.start env arg) base) := by
    simp [EvalState.stepN_succ, EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, EvalState.driveOp,
      EvalState.appendStack, hop, base, resume, Op.Body.resume?, Op.natUnary, Op.ofVals,
      Op.Body.eager, Op.fixed]
  have hfromArgState := EvaluatesFrom.drop_prefix hprefix hfrom
  have hfromArgStateSaved := hfromArgState
  obtain ⟨fuel, scope, hsteps⟩ := hfromArgState
  have hrunArgState :
      (EvalState.run ctx fuel (EvalState.appendStack (EvalState.start env arg) base)).result? =
        some value := by
    rw [EvalState.run_eq_of_stepN hsteps]
    rfl
  obtain ⟨argVal, hargFrom⟩ := EvaluatesFrom.exists_of_run_append_opBodies
    (ctx := ctx) (state := EvalState.start env arg) (base := base)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [base]) hrunArgState
  have harg : EvaluatesTo ctx env arg argVal := EvaluatesTo.of_evaluatesFrom hargFrom
  obtain ⟨argFuel, argScope, hargSteps⟩ := EvaluatesTo.weaken harg base
  have hfromRetArg := EvaluatesFrom.drop_prefix hargSteps hfromArgStateSaved
  cases hm : argVal.asNat? with
  | none =>
      obtain ⟨retFuel, retScope, hretSteps⟩ := hfromRetArg
      cases retFuel with
      | zero => simp [base] at hretSteps
      | succ retFuel =>
          rw [EvalState.stepN_succ] at hretSteps
          simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.driveOp, base, resume, Op.Body.resume?, Op.natUnary,
            Op.ofVals, Op.Body.eager, Op.fixed, hm] at hretSteps
  | some n =>
      have hargNat : argVal = Val.nat n := Val.eq_nat_of_asNat? hm
      subst argVal
      have hstepRet : EvalState.step ctx ⟨.ret (Val.nat (primCtx := ctx.primCtx) n),
          argScope, base⟩ = some ⟨.ret (Val.nat (f n)), env, []⟩ := by
        simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.driveOp, base, resume, Op.Body.resume?, Op.natUnary,
          Op.ofVals, Op.Body.eager, Op.fixed]
      have hfromResult := EvaluatesFrom.drop_prefix
        (ctx := ctx) (fuel₀ := 1) (state := ⟨.ret (Val.nat (primCtx := ctx.primCtx) n),
          argScope, base⟩) (mid := ⟨.ret (Val.nat (f n)), env, []⟩)
        (by simp [EvalState.stepN_succ, hstepRet]) hfromRetArg
      have hvalue := EvaluatesFrom.ret_empty_eq hfromResult
      exact ⟨n, hvalue⟩

theorem eval_nat_of_eq_natUnary_true {ctx : Ctx} [Peano.Model ctx]
    {env : Env ctx.primCtx} {name : String} {arg rhs : Term ctx.primCtx} {f : Nat → Nat}
    (hop : ctx.opCtx.get? name = some (Op.natUnary (primCtx := ctx.primCtx) f))
    (h : EvaluatesTo ctx env (.op "eq" [.op name [arg], rhs]) (Val.bool true)) :
    ∃ n : Nat, EvaluatesTo ctx env rhs (Val.nat n) := by
  let lhs := Term.op name [arg]
  let firstResume := Op.Body.resume?
    (((Op.eq (primCtx := ctx.primCtx)).body "eq" 2).getD
      (Op.Body.fail : Op.Body ctx.primCtx))
  let firstBase : List (Frame ctx.primCtx) :=
    [Frame.opBody firstResume (Op.Arg.ofTerms [rhs]) env]
  have hfrom := EvaluatesFrom.of_evaluatesTo h
  have hprefix : EvalState.stepN ctx 1 (EvalState.start env (.op "eq" [lhs, rhs])) =
      some (EvalState.appendStack (EvalState.start env lhs) firstBase) := by
    simp [EvalState.stepN_succ, EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.start, EvalState.driveOp,
      EvalState.appendStack, Peano.Model.eqOp, firstBase, firstResume, lhs, Op.Body.resume?,
      Op.eq, Op.compare, Op.fixed]
  have hfromLhsState := EvaluatesFrom.drop_prefix hprefix hfrom
  have hfromLhsStateSaved := hfromLhsState
  obtain ⟨lhsFuel, lhsScope, hlhsSteps⟩ := hfromLhsState
  have hrunLhsState :
      (EvalState.run ctx lhsFuel (EvalState.appendStack (EvalState.start env lhs) firstBase)).result? =
        some (Val.bool true) := by
    rw [EvalState.run_eq_of_stepN hlhsSteps]
    rfl
  obtain ⟨lhsVal, hlhsFrom⟩ := EvaluatesFrom.exists_of_run_append_opBodies
    (ctx := ctx) (state := EvalState.start env lhs) (base := firstBase)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [firstBase]) hrunLhsState
  have hlhs : EvaluatesTo ctx env lhs lhsVal := EvaluatesTo.of_evaluatesFrom hlhsFrom
  obtain ⟨m, hlhsVal⟩ := evaluates_natUnary_result_nat (ctx := ctx) (env := env)
    (name := name) (arg := arg) (f := f) hop (value := lhsVal) hlhs
  subst lhsVal
  let secondResume := Op.Body.resume? (firstResume (some (Val.nat (primCtx := ctx.primCtx) (f m))))
  let secondBase : List (Frame ctx.primCtx) := [Frame.opBody secondResume [] env]
  obtain ⟨lhsEvalFuel, lhsEvalScope, hlhsEvalSteps⟩ := EvaluatesTo.weaken hlhs firstBase
  have hfromRetLhs := EvaluatesFrom.drop_prefix hlhsEvalSteps hfromLhsStateSaved
  have hstepLhsRet : EvalState.step ctx ⟨.ret (Val.nat (primCtx := ctx.primCtx) (f m)),
      lhsEvalScope, firstBase⟩ = some (EvalState.appendStack (EvalState.start env rhs) secondBase) := by
    simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.driveOp, EvalState.appendStack, firstBase, secondBase,
      EvalState.start, firstResume, secondResume, Op.Body.resume?, Op.eq, Op.compare, Op.fixed]
  have hfromRhsState := EvaluatesFrom.drop_prefix
    (ctx := ctx) (fuel₀ := 1) (state := ⟨.ret (Val.nat (primCtx := ctx.primCtx) (f m)),
      lhsEvalScope, firstBase⟩) (mid := EvalState.appendStack (EvalState.start env rhs) secondBase)
    (by simp [EvalState.stepN_succ, hstepLhsRet]) hfromRetLhs
  have hfromRhsStateSaved := hfromRhsState
  obtain ⟨rhsFuel, rhsScope, hrhsSteps⟩ := hfromRhsState
  have hrunRhsState :
      (EvalState.run ctx rhsFuel (EvalState.appendStack (EvalState.start env rhs) secondBase)).result? =
        some (Val.bool true) := by
    rw [EvalState.run_eq_of_stepN hrhsSteps]
    rfl
  obtain ⟨rhsVal, hrhsFrom⟩ := EvaluatesFrom.exists_of_run_append_opBodies
    (ctx := ctx) (state := EvalState.start env rhs) (base := secondBase)
    (hbase := Frame.OpBodies.cons Frame.OpBodies.nil) (hne := by simp [secondBase]) hrunRhsState
  have hrhs : EvaluatesTo ctx env rhs rhsVal := EvaluatesTo.of_evaluatesFrom hrhsFrom
  obtain ⟨rhsEvalFuel, rhsEvalScope, hrhsEvalSteps⟩ := EvaluatesTo.weaken hrhs secondBase
  have hfromRetRhs := EvaluatesFrom.drop_prefix hrhsEvalSteps hfromRhsStateSaved
  obtain ⟨retFuel, retScope, hretSteps⟩ := hfromRetRhs
  cases retFuel with
  | zero => simp [secondBase] at hretSteps
  | succ retFuel =>
      rw [EvalState.stepN_succ] at hretSteps
      by_cases hty : (Val.nat (primCtx := ctx.primCtx) (f m)).ty = rhsVal.ty
      · have hrhsTy : rhsVal.ty = Peano.NatTy := by simpa using hty.symm
        obtain ⟨n, hn⟩ := Val.exists_nat_of_ty hrhsTy
        exact ⟨n, by simpa [hn] using hrhs⟩
      · simp [EvalState.step, EvalState.evalStep, EvalState.resumeFrame, EvalState.unwindFrame, EvalState.driveOp, secondBase, secondResume, firstResume,
          Op.Body.resume?, Op.eq, Op.compare, Op.fixed,
          show ¬ Peano.NatTy = rhsVal.ty by simpa using hty]
          at hretSteps

theorem eval_nat_of_reflected_natUnary_eq {ctx : Ctx} [Peano.Model ctx]
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

/-! ### continuation-passing `while` -/

namespace Peano

variable {primCtx : PrimitiveCtx} [Peano.Types primCtx]

def whileCondRef (condName : String) (stateTys : List Ty) : Val primCtx :=
  .blockRef condName stateTys Peano.BoolTy

def whileBodyRef (bodyName : String) (stateTys : List Ty) (resultTy : Ty) : Val primCtx :=
  .blockRef bodyName (stateTys ++ [.func stateTys resultTy]) resultTy

def whileRef (opName condName bodyName : String) (stateTys : List Ty) (resultTy : Ty) :
    Val primCtx :=
  .opRef opName [whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy]
    stateTys resultTy

/- A finite invariant rule for the ordinary `while` operator. One body call receives the loop
  continuation as its final argument. Its premise is continuation-parametric: after proving the
  simultaneous next state satisfies the invariant, the body may use the supplied application
  specification and return the recursive answer through its own call frame. -/
theorem while_invariant {ctx : Ctx} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hheadTy : stateTys.head? = some resultTy)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = stateTys)
    (preserved : ∀ n args, n < N → I n args →
      EvaluatesCall ctx condName args (Val.bool true) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
            nextArgs loopResult) →
        EvaluatesCall ctx bodyName
          (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult))
    (exits : ∀ args, I N args →
      EvaluatesCall ctx condName args (Val.bool false) ∧ args.head? = some loopResult) :
    EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
      initial loopResult := by
  apply EvaluatesApply.loop init
  · intro n args hn hI hnext
    obtain ⟨hcond, hbody⟩ := preserved n args hn hI
    have htys := typed n args hI
    have hne : args ≠ [] := by
      intro hnil
      subst args
      simp at htys
      simpa [htys] using hheadTy
    obtain ⟨head, tail, hargs⟩ : ∃ head tail, args = head :: tail := by
      cases args with
      | nil => exact (hne rfl).elim
      | cons head tail => exact ⟨head, tail, rfl⟩
    have hhead : args.head? = some head := by simp [hargs]
    have hcondApply : EvaluatesApply ctx (whileCondRef condName stateTys) args
        (Val.bool true) := EvaluatesApply.blockRef hcond
    have hbodyApply : EvaluatesApply ctx (whileBodyRef bodyName stateTys resultTy)
        (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult :=
      EvaluatesApply.blockRef (hbody hnext)
    apply EvaluatesApply.opRef
      (body := Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
        (2 + args.length) []) hop
    · have hthree : 3 ≤ 2 + args.length := by
        cases args with
        | nil => exact (hne rfl).elim
        | cons => simp; omega
      simp [Op.whileOp, hthree]
    · intro env base
      have hout : Op.whileResultTy? (primCtx := ctx.primCtx)
          (.func stateTys Peano.BoolTy ::
            .func (stateTys ++ [.func stateTys resultTy]) resultTy :: stateTys) =
            some resultTy := by
        simp [Op.whileResultTy?, hheadTy]
      obtain ⟨bodyStart, hbodyDrive, hbodyFrom⟩ :=
        EvaluatesFrom.driveOp_apply (env := env) (stack := base) (operands := [])
          (resume := fun value => .done value) hbodyApply
          (hdrive := by simp [EvalState.driveOp])
          (EvaluatesFrom.done (ctx := ctx) (value := loopResult) (scope := env) (base := base))
      obtain ⟨condStart, hcondDrive, hcondFrom⟩ :=
        EvaluatesFrom.driveOp_apply (env := env) (stack := base) (operands := [])
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
      rw [EvalState.driveOp_collect _ _ _ hlen]
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
  · intro args hI
    obtain ⟨hcond, hhead⟩ := exits args hI
    have htys := typed N args hI
    have hne : args ≠ [] := by
      intro hnil
      subst args
      simp at hhead
    have hcondApply : EvaluatesApply ctx (whileCondRef condName stateTys) args
        (Val.bool false) := EvaluatesApply.blockRef hcond
    apply EvaluatesApply.opRef
      (body := Op.Body.collect (Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
        (2 + args.length) []) hop
    · have hthree : 3 ≤ 2 + args.length := by
        cases args with
        | nil => exact (hne rfl).elim
        | cons => simp; omega
      simp [Op.whileOp, hthree]
    · intro env base
      have hout : Op.whileResultTy? (primCtx := ctx.primCtx)
          (.func stateTys Peano.BoolTy ::
            .func (stateTys ++ [.func stateTys resultTy]) resultTy :: stateTys) =
            some resultTy := by
        simp [Op.whileResultTy?, hheadTy]
      obtain ⟨condStart, hcondDrive, hcondFrom⟩ :=
        EvaluatesFrom.driveOp_apply (env := env) (stack := base) (operands := [])
          (resume := fun condition =>
            match condition.asBool? with
            | some false => .done loopResult
            | some true =>
                .apply (whileBodyRef bodyName stateTys resultTy)
                  (args ++ [whileRef opName condName bodyName stateTys resultTy]) .done
            | none => .fail) hcondApply
          (hdrive := by simp only [Val.asBool?_bool, EvalState.driveOp])
          (EvaluatesFrom.done (ctx := ctx) (value := loopResult) (scope := env) (base := base))
      refine ⟨condStart, ?_, hcondFrom⟩
      have hlen :
          ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ args).length =
            2 + args.length := by simp; omega
      rw [EvalState.driveOp_collect _ _ _ hlen]
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

/- The term-level entry rule for `while`. The initial operands are evaluated by the enclosing
operator; recursive iterations use the continuation specification from `while_invariant`. -/
theorem while_evaluatesTo {ctx : Ctx} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {operands : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hargs : EvaluatesToAll ctx env operands
      ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ initial))
    (hheadTy : stateTys.head? = some resultTy)
    (init : I 0 initial)
    (typed : ∀ n args, I n args → args.map Val.ty = stateTys)
    (preserved : ∀ n args, n < N → I n args →
      EvaluatesCall ctx condName args (Val.bool true) ∧
      ((∀ nextArgs, I (n + 1) nextArgs →
          EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
            nextArgs loopResult) →
        EvaluatesCall ctx bodyName
          (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult))
    (exits : ∀ args, I N args →
      EvaluatesCall ctx condName args (Val.bool false) ∧ args.head? = some loopResult) :
    EvaluatesTo ctx env (.op opName operands) loopResult := by
  have htys := typed 0 initial init
  have hne : initial ≠ [] := by
    intro hnil
    subst initial
    simp at htys
    simpa [htys] using hheadTy
  have hone : 1 ≤ initial.length := by
    cases initial with
    | nil => exact (hne rfl).elim
    | cons => simp
  apply EvaluatesTo.op_collect_of_opRef
      (captured := [whileCondRef condName stateTys,
        whileBodyRef bodyName stateTys resultTy])
      (args := initial) (argTys := stateTys) (outTy := resultTy)
      (finish := Op.whileBodyFromValues (primCtx := ctx.primCtx) opName)
      hop (by simp [Op.whileOp]; omega) hargs
  exact while_invariant (I := I) (N := N) (loopResult := loopResult)
    hop hheadTy init typed preserved exits

/-- The semantic while rule split into the four obligations exposed by `while_induction`. -/
def whileInduction {ctx : Ctx} [Peano.Types ctx.primCtx]
    {opName condName bodyName : String} {stateTys : List Ty} {resultTy : Ty}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {initial : List (Val ctx.primCtx)} {loopResult : Val ctx.primCtx}
    {env : Env ctx.primCtx} {operands : List (Term ctx.primCtx)}
    (hop : ctx.opCtx.get? opName = some (Op.whileOp (primCtx := ctx.primCtx)))
    (hargs : EvaluatesToAll ctx env operands
      ([whileCondRef condName stateTys, whileBodyRef bodyName stateTys resultTy] ++ initial))
    (hheadTy : stateTys.head? = some resultTy)
    (typed : ∀ n args, I n args → args.map Val.ty = stateTys) :
    PropRefinement (EvaluatesTo ctx env (.op opName operands) loopResult) where
  goals :=
    [ I 0 initial
    , ∀ n args, n < N → I n args → EvaluatesCall ctx condName args (Val.bool true)
    , ∀ n args, n < N → I n args →
        ((∀ nextArgs, I (n + 1) nextArgs →
            EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
              nextArgs loopResult) →
          EvaluatesCall ctx bodyName
            (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult)
    , ∀ args, I N args →
        EvaluatesCall ctx condName args (Val.bool false) ∧ args.head? = some loopResult
    ]
  prove := by
    intro proveSubgoals
    have init : I 0 initial := proveSubgoals _ (by simp)
    have condition : ∀ n args, n < N → I n args →
        EvaluatesCall ctx condName args (Val.bool true) := proveSubgoals _ (by simp)
    have preservation : ∀ n args, n < N → I n args →
        ((∀ nextArgs, I (n + 1) nextArgs →
            EvaluatesApply ctx (whileRef opName condName bodyName stateTys resultTy)
              nextArgs loopResult) →
          EvaluatesCall ctx bodyName
            (args ++ [whileRef opName condName bodyName stateTys resultTy]) loopResult) :=
      proveSubgoals _ (by simp)
    have termination : ∀ args, I N args →
        EvaluatesCall ctx condName args (Val.bool false) ∧ args.head? = some loopResult :=
      proveSubgoals _ (by simp)
    apply while_evaluatesTo (I := I) (N := N) (loopResult := loopResult) hop hargs hheadTy
    · exact init
    · exact typed
    · intro n args hn hinv
      exact ⟨condition n args hn hinv, preservation n args hn hinv⟩
    · exact termination

end Peano

end Zag
