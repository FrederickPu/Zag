import Zag.EvalTriple
import Zag.Refinement

/-! # Continuation-passing operator loops -/

namespace Zag

open scoped Std.Do

namespace Machine

theorem driveOp_collect {ctx : Ctx} (finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx)
    (vals acc : List (Val ctx.primCtx)) {remaining : Nat} {env : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} (hlen : vals.length = remaining) :
    driveOp (Op.Body.collect finish remaining acc) (Op.Arg.ofVals vals) env stack =
      driveOp (finish (acc ++ vals)) [] env stack := by
  induction vals generalizing remaining acc with
  | nil =>
      simp at hlen
      subst remaining
      simp [Op.Body.collect, Op.Arg.ofVals]
  | cons value vals ih =>
      cases remaining with
      | zero => simp at hlen
      | succ remaining =>
          have hlen' : vals.length = remaining := by simpa using hlen
          rw [Op.Body.collect]
          simp only [Op.Arg.ofVals, List.map_cons, driveOp]
          simpa [List.append_assoc] using ih (remaining := remaining)
            (acc := acc ++ [value]) hlen'

end Machine

namespace EvalTriple

namespace EvaluatesApply

/-- Establish an application specification from its actual `Machine.step` successor. -/
theorem of_step {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {P : Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)}
    (h : ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
      ∃ state, Machine.step ctx ⟨.apply fn args, env, base⟩ =
          Machine.ofOption ctx (some state) ∧
        EvaluatesFrom ctx state base P Q) :
    EvaluatesApply ctx fn args P Q := by
  intro env base
  obtain ⟨state, hstep, hfrom⟩ := h env base
  exact hfrom.pureStep hstep

/-- Run an ordinary operator body. The explicit `action = none` premise prevents this rule from
silently replacing an ambient action. -/
theorem opRef {ctx : Ctx} {name : String} {captured args : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {oper : Op ctx.primCtx ctx.M}
    {body : Op.Body ctx.primCtx} {P : Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (hop : ctx.opCtx.get? name = some oper)
    (hpure : oper.action name (captured ++ args) = none)
    (hbody : oper.body name (captured.length + args.length) = some body)
    (hrun : ∀ (env : Env ctx.primCtx) (base : List (Frame ctx.primCtx)),
      ∃ state, Machine.driveOp body (Op.Arg.ofVals (captured ++ args)) env base = some state ∧
        EvaluatesFrom ctx state base P Q) :
    EvaluatesApply ctx (.opRef name captured argTys outTy) args P Q := by
  apply of_step
  intro env base
  obtain ⟨state, hdrive, hfrom⟩ := hrun env base
  refine ⟨state, ?_, hfrom⟩
  have hdrive' : Machine.driveOp body
      (Op.Arg.ofVals captured ++ Op.Arg.ofVals args) env base = some state := by
    simpa [Op.Arg.ofVals, List.map_append] using hdrive
  simp [Machine.step, Machine.applyValue, Machine.driveSelectedOp,
    Machine.ofOption, hop, hpure, hbody, hdrive']

/-- Finite induction for a continuation-passing loop. The invariant is an assertion, so ambient
state and other monadic resources remain explicit at every iteration. -/
theorem loop {ctx : Ctx} {fn : Val ctx.primCtx}
    {I : Nat → List (Val ctx.primCtx) → Assertion ctx}
    {N : Nat} {initial : List (Val ctx.primCtx)}
    {P : Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)}
    (init : P ⊢ₛ I 0 initial)
    (round : ∀ n args, n < N →
      (∀ nextArgs, EvaluatesApply ctx fn nextArgs (I (n + 1) nextArgs) Q) →
      EvaluatesApply ctx fn args (I n args) Q)
    (stop : ∀ args, EvaluatesApply ctx fn args (I N args) Q) :
    EvaluatesApply ctx fn initial P Q := by
  have aux : ∀ k n args, n + k = N → EvaluatesApply ctx fn args (I n args) Q := by
    intro k
    induction k with
    | zero =>
        intro n args hn
        have : n = N := by omega
        subst n
        exact stop args
    | succ k ih =>
        intro n args hn
        apply round n args (by omega)
        intro nextArgs
        exact ih (n + 1) nextArgs (by omega)
  exact (aux N 0 initial (Nat.zero_add N)).consequence init .rfl

end EvaluatesApply

namespace EvaluatesFrom

/-- Run an application and continue from the assertion it establishes. -/
theorem apply_then {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {P : Assertion ctx} {I : Val ctx.primCtx → Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (happly : EvaluatesApply ctx fn args P (I, Q.2))
    (hcont : ∀ value scope,
      EvaluatesFrom ctx ⟨.ret value, scope, stack⟩ base (I value) Q) :
    EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ base P Q :=
  EvaluatesFrom.bind (happly env stack) hcont

/-- Return from an application through the operator frame that suspended it. -/
theorem apply_opBody {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {env frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {rest : List (Op.Arg ctx.primCtx)} {stack base : List (Frame ctx.primCtx)}
    {P : Assertion ctx} {I : Val ctx.primCtx → Assertion ctx}
    {Q : PostCond ctx (Val ctx.primCtx)}
    (happly : EvaluatesApply ctx fn args P (I, Q.2))
    (hnext : ∀ value, ∃ state,
      Machine.driveOp (resume (some value)) rest frameEnv stack = some state ∧
        EvaluatesFrom ctx state base (I value) Q) :
    EvaluatesFrom ctx
      ⟨.apply fn args, env, .opBody resume rest frameEnv :: stack⟩ base P Q := by
  apply EvaluatesFrom.apply_then happly
  intro value scope
  obtain ⟨state, hdrive, hfrom⟩ := hnext value
  apply hfrom.pureStep
  simp [Machine.step, Machine.ofOption, Machine.resumeFrame, hdrive]

/-- Execute an `.apply` node reached by `driveOp`. -/
theorem driveOp_apply {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {resume : Val ctx.primCtx → Op.Body ctx.primCtx}
    {operands : List (Op.Arg ctx.primCtx)} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} {P : Assertion ctx}
    {I : Val ctx.primCtx → Assertion ctx} {Q : PostCond ctx (Val ctx.primCtx)}
    (happly : EvaluatesApply ctx fn args P (I, Q.2))
    (hnext : ∀ value, ∃ state,
      Machine.driveOp (resume value) operands env stack = some state ∧
        EvaluatesFrom ctx state base (I value) Q) :
    ∃ start, Machine.driveOp (.apply fn args resume) operands env stack = some start ∧
      EvaluatesFrom ctx start base P Q := by
  let k : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
    | some result => resume result
    | none => .fail
  refine ⟨⟨.apply fn args, env, .opBody k operands env :: stack⟩, ?_, ?_⟩
  · simp [Machine.driveOp, k]
    funext input
    cases input <;> rfl
  exact EvaluatesFrom.apply_opBody happly (by simpa [k] using hnext)

end EvaluatesFrom

/-! Exact-result specializations used by the Id semantic library. -/

namespace Exact.EvaluatesApply

theorem loop {ctx : Ctx} {fn : Val ctx.primCtx}
    {I : Nat → List (Val ctx.primCtx) → Prop} {N : Nat}
    {result : Val ctx.primCtx} {initial : List (Val ctx.primCtx)} {hM : ctx.M = Id}
    (init : I 0 initial)
    (round : ∀ n args, n < N → I n args →
      (∀ nextArgs, I (n + 1) nextArgs → Exact.EvaluatesApply ctx fn nextArgs result hM) →
      Exact.EvaluatesApply ctx fn args result hM)
    (stop : ∀ args, I N args → Exact.EvaluatesApply ctx fn args result hM) :
    Exact.EvaluatesApply ctx fn initial result hM := by
  have aux : ∀ k n args, n + k = N → I n args →
      Exact.EvaluatesApply ctx fn args result hM := by
    intro k
    induction k with
    | zero =>
        intro n args hn hI
        have : n = N := by omega
        subst n
        exact stop args hI
    | succ k ih =>
        intro n args hn hI
        apply round n args (by omega) hI
        intro nextArgs hnext
        exact ih (n + 1) nextArgs (by omega) hnext
  exact aux N 0 initial (Nat.zero_add N) init

theorem blockRef {ctx : Ctx} {name : String} {args : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {argTys : List Ty} {outTy : Ty}
    {hM : ctx.M = Id} (hcall : Exact.EvaluatesCallValues ctx name args value hM) :
    Exact.EvaluatesApply ctx (.blockRef name argTys outTy) args value hM :=
  Zag.EvaluatesApply.blockRef hcall

theorem opRef {ctx : Ctx} {name : String} {captured args : List (Val ctx.primCtx)}
    {argTys : List Ty} {outTy : Ty} {oper : Op ctx.primCtx ctx.M}
    {body : Op.Body ctx.primCtx} {value : Val ctx.primCtx} {hM : ctx.M = Id}
    (hop : ctx.opCtx.get? name = some oper)
    (hpure : oper.action name (captured ++ args) = none)
    (hbody : oper.body name (captured.length + args.length) = some body)
    (hrun : ∀ env base, ∃ state,
      Machine.driveOp body (Op.Arg.ofVals (captured ++ args)) env base = some state ∧
        Exact.EvaluatesFrom ctx state value base hM) :
    Exact.EvaluatesApply ctx (.opRef name captured argTys outTy) args value hM := by
  apply EvalTriple.EvaluatesApply.opRef (ctx := Exact.idView ctx hM)
      (oper := Exact.idOp ctx hM oper) (body := body)
  · exact Exact.idView_get?_of_get? hM hop
  · exact Exact.idOp_property ctx hM oper
      (fun _ oper => oper.action name (captured ++ args) = none) hpure
  · exact Exact.idOp_property ctx hM oper
      (fun _ oper => oper.body name (captured.length + args.length) = some body) hbody
  exact hrun

end Exact.EvaluatesApply

namespace Exact.EvaluatesFrom

theorem apply_then {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {value final : Val ctx.primCtx} {env : Env ctx.primCtx}
    {stack base : List (Frame ctx.primCtx)} {hM : ctx.M = Id}
    (happly : Exact.EvaluatesApply ctx fn args value hM)
    (hcont : ∀ scope,
      Exact.EvaluatesFrom ctx ⟨.ret value, scope, stack⟩ final base hM) :
    Exact.EvaluatesFrom ctx ⟨.apply fn args, env, stack⟩ final base hM :=
  Exact.EvaluatesFrom.bind (happly env stack) hcont

theorem apply_opBody {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {value final : Val ctx.primCtx} {env frameEnv : Env ctx.primCtx}
    {resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {rest : List (Op.Arg ctx.primCtx)} {stack base : List (Frame ctx.primCtx)}
    {state : Machine.Config ctx.primCtx} {hM : ctx.M = Id}
    (happly : Exact.EvaluatesApply ctx fn args value hM)
    (hdrive : Machine.driveOp (resume (some value)) rest frameEnv stack = some state)
    (hfrom : Exact.EvaluatesFrom ctx state final base hM) :
    Exact.EvaluatesFrom ctx
      ⟨.apply fn args, env, .opBody resume rest frameEnv :: stack⟩ final base hM := by
  apply Exact.EvaluatesFrom.apply_then happly
  intro scope
  apply Exact.EvaluatesFrom.pureStep (next := state)
  · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, hdrive]
  exact hfrom

theorem driveOp_apply {ctx : Ctx} {fn : Val ctx.primCtx} {args : List (Val ctx.primCtx)}
    {resume : Val ctx.primCtx → Op.Body ctx.primCtx}
    {operands : List (Op.Arg ctx.primCtx)} {value final : Val ctx.primCtx}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {state : Machine.Config ctx.primCtx} {hM : ctx.M = Id}
    (happly : Exact.EvaluatesApply ctx fn args value hM)
    (hdrive : Machine.driveOp (resume value) operands env stack = some state)
    (hfrom : Exact.EvaluatesFrom ctx state final base hM) :
    ∃ start, Machine.driveOp (.apply fn args resume) operands env stack = some start ∧
      Exact.EvaluatesFrom ctx start final base hM := by
  let k : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
    | some result => resume result
    | none => .fail
  refine ⟨⟨.apply fn args, env, .opBody k operands env :: stack⟩, ?_, ?_⟩
  · simp [Machine.driveOp, k]
    funext input
    cases input <;> rfl
  exact Exact.EvaluatesFrom.apply_opBody happly (by simpa [k] using hdrive) hfrom

/-- Evaluate collected term operands and continue from the body built from their values. -/
theorem driveOp_collect {ctx : Ctx}
    (finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx)
    {terms : List (Term ctx.primCtx)} {values acc : List (Val ctx.primCtx)}
    {env : Env ctx.primCtx} {stack base : List (Frame ctx.primCtx)}
    {result : Val ctx.primCtx} {hM : ctx.M = Id}
    (hargs : Exact.EvaluatesList ctx env terms values hM)
    (hfinish : ∃ state,
      Machine.driveOp (finish (acc ++ values)) [] env stack = some state ∧
        Exact.EvaluatesFrom ctx state result base hM) :
    ∃ state,
      Machine.driveOp (Op.Body.collect finish values.length acc)
          (Op.Arg.ofTerms terms) env stack = some state ∧
        Exact.EvaluatesFrom ctx state result base hM := by
  induction hargs generalizing acc stack with
  | nil => simpa [Op.Body.collect] using hfinish
  | cons hterm hterms ih =>
      rename_i term terms value values _
      obtain ⟨state, hdrive, hfrom⟩ := ih (acc := acc ++ [value]) (stack := stack) (by
        simpa [List.append_assoc] using hfinish)
      let resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx := fun
        | some actual => Op.Body.collect finish values.length (acc ++ [actual])
        | none => .fail
      refine ⟨⟨.eval term, env, .opBody resume (Op.Arg.ofTerms terms) env :: stack⟩, ?_, ?_⟩
      · simp [Machine.driveOp, Op.Body.collect, Op.Arg.ofTerms, resume]
        funext input
        cases input <;> rfl
      · apply Exact.EvaluatesFrom.bind
          (hterm (.opBody resume (Op.Arg.ofTerms terms) env :: stack))
        intro scope
        apply Exact.EvaluatesFrom.pureStep (next := state)
        · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, hdrive, resume]
        exact hfrom

end Exact.EvaluatesFrom

namespace Exact.EvaluatesTo

theorem driveOp {ctx : Ctx} {env : Env ctx.primCtx}
    {terms : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    {hM : ctx.M = Id} (hargs : Exact.EvaluatesList ctx env terms values hM)
    {body : Op.Body ctx.primCtx} {result : Val ctx.primCtx}
    (hbody : body.applyVals values = some result) :
    ∀ stack, ∃ state,
      Machine.driveOp body (Op.Arg.ofTerms terms) env stack = some state ∧
        Exact.EvaluatesFrom ctx state result stack hM := by
  induction hargs generalizing body with
  | nil =>
      intro stack
      cases body with
      | fail => simp [Op.Body.applyVals] at hbody
      | done value =>
          have hvalue : value = result := by simpa [Op.Body.applyVals] using hbody
          subst result
          exact ⟨⟨.ret value, env, stack⟩, by simp [Machine.driveOp],
            Exact.EvaluatesFrom.done⟩
      | next evaluate resume => simp [Op.Body.applyVals] at hbody
      | apply fn args resume => simp [Op.Body.applyVals] at hbody
  | cons hterm hterms ih =>
      intro stack
      rename_i term terms termValue termValues _
      cases body with
      | fail => simp [Op.Body.applyVals] at hbody
      | done value =>
          have hvalue : value = result := by simpa [Op.Body.applyVals] using hbody
          subst result
          exact ⟨⟨.ret value, env, stack⟩, by simp [Machine.driveOp],
            Exact.EvaluatesFrom.done⟩
      | next evaluate resume =>
          cases evaluate with
          | false =>
              have hbody' : (resume none).applyVals termValues = some result := by
                simpa [Op.Body.applyVals] using hbody
              obtain ⟨state, hdrive, hfrom⟩ := ih hbody' stack
              exact ⟨state, by simpa [Machine.driveOp, Op.Arg.ofTerms] using hdrive, hfrom⟩
          | true =>
              have hbody' : (resume (some termValue)).applyVals termValues = some result := by
                simpa [Op.Body.applyVals] using hbody
              obtain ⟨state, hdrive, hfrom⟩ := ih hbody' stack
              let frame := Frame.opBody resume (Op.Arg.ofTerms terms) env
              refine ⟨⟨.eval term, env, frame :: stack⟩, ?_, ?_⟩
              · simp [Machine.driveOp, Op.Arg.ofTerms, frame]
              · apply Exact.EvaluatesFrom.bind (hterm (frame :: stack))
                intro scope
                apply Exact.EvaluatesFrom.pureStep (next := state)
                · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                    hdrive, frame]
                exact hfrom
      | apply fn args resume => simp [Op.Body.applyVals] at hbody

theorem op_applyVals {ctx : Ctx} {env : Env ctx.primCtx}
    {name : String} {args : List (Term ctx.primCtx)} {values : List (Val ctx.primCtx)}
    {oper : Op ctx.primCtx ctx.M} {result : Val ctx.primCtx} {hM : ctx.M = Id}
    (hop : ctx.opCtx.get? name = some oper)
    (hargs : Exact.EvaluatesList ctx env args values hM)
    (happly : Op.applyValsAt name oper values = some result) :
    Exact.EvaluatesTo ctx env (.op name args) result hM := by
  let idOper := Exact.idOp ctx hM oper
  have hopId : (Exact.idView ctx hM).opCtx.get? name = some idOper :=
    Exact.idView_get?_of_get? hM hop
  have happlyId : Op.applyValsAt name idOper values = some result :=
    Exact.idOp_property ctx hM oper
      (fun _ oper => Op.applyValsAt name oper values = some result) happly
  have hlen : args.length = values.length := hargs.length_eq
  unfold Op.applyValsAt at happlyId
  cases hstart : idOper.body name values.length with
  | none => simp [hstart] at happlyId
  | some body =>
      have hbody : body.applyVals values = some result := by simpa [hstart] using happlyId
      intro stack
      obtain ⟨state, hdrive, hfrom⟩ := driveOp hargs hbody stack
      apply Exact.EvaluatesFrom.pureStep (next := state)
      · simp [Machine.step, Machine.evalTerm, Machine.driveSelectedOp,
          Machine.ofOption, hopId, hlen, hstart, hdrive]
      exact hfrom

/-- A collected term operator can reuse the exact application specification of its operator
reference after all operands have been evaluated. -/
theorem op_collect_of_opRef {ctx : Ctx} {env : Env ctx.primCtx}
    {name : String} {terms : List (Term ctx.primCtx)}
    {captured args : List (Val ctx.primCtx)} {argTys : List Ty} {outTy : Ty}
    {oper : Op ctx.primCtx ctx.M} {finish : List (Val ctx.primCtx) → Op.Body ctx.primCtx}
    {result : Val ctx.primCtx} {hM : ctx.M = Id}
    (hop : ctx.opCtx.get? name = some oper)
    (hpure : oper.action name (captured ++ args) = none)
    (hbody : oper.body name (captured.length + args.length) =
      some (Op.Body.collect finish (captured.length + args.length) []))
    (hargs : Exact.EvaluatesList ctx env terms (captured ++ args) hM)
    (happly : Exact.EvaluatesApply ctx (.opRef name captured argTys outTy)
      args result hM) :
    Exact.EvaluatesTo ctx env (.op name terms) result hM := by
  let idOper := Exact.idOp ctx hM oper
  have hopId : (Exact.idView ctx hM).opCtx.get? name = some idOper :=
    Exact.idView_get?_of_get? hM hop
  have hpureId : idOper.action name (captured ++ args) = none :=
    Exact.idOp_property ctx hM oper
      (fun _ selected => selected.action name (captured ++ args) = none) hpure
  have hbodyId : idOper.body name (captured.length + args.length) =
      some (Op.Body.collect finish (captured.length + args.length) []) :=
    Exact.idOp_property ctx hM oper
      (fun _ selected => selected.body name (captured.length + args.length) =
        some (Op.Body.collect finish (captured.length + args.length) [])) hbody
  intro stack
  have href := happly env stack
  obtain ⟨state, hstep⟩ := Exact.EvaluatesFrom.existsPureStep
    (h := href) (by intro scope heq; cases heq)
  have hfrom := Exact.EvaluatesFrom.afterPureStep
    (h := href) (by intro scope heq; cases heq) hstep
  have hlen : terms.length = (captured ++ args).length := hargs.length_eq
  have hbodyTerms : idOper.body name terms.length =
      some (Op.Body.collect finish (captured.length + args.length) []) := by
    simpa [hlen, List.length_append] using hbodyId
  cases hdrive : Machine.driveOp
      (Op.Body.collect finish (captured.length + args.length) [])
      (Op.Arg.ofVals (captured ++ args)) env stack with
  | none =>
      have hdrive' : Machine.driveOp
          (Op.Body.collect finish (captured.length + args.length) [])
          (Op.Arg.ofVals captured ++ Op.Arg.ofVals args) env stack = none := by
        simpa [Op.Arg.ofVals, List.map_append] using hdrive
      have hbad := congrArg (fun action => action.run.run) hstep
      simp [Machine.step, Machine.applyValue, Machine.driveSelectedOp,
        Machine.ofOption, hopId, hpureId, hbodyId, hdrive'] at hbad
  | some driven =>
      have hdrive' : Machine.driveOp
          (Op.Body.collect finish (captured.length + args.length) [])
          (Op.Arg.ofVals captured ++ Op.Arg.ofVals args) env stack = some driven := by
        simpa [Op.Arg.ofVals, List.map_append] using hdrive
      have hstate : state = driven := by
        have hs := congrArg (fun action => action.run.run) hstep
        simp [Machine.step, Machine.applyValue, Machine.driveSelectedOp,
          Machine.ofOption, hopId, hpureId, hbodyId, hdrive'] at hs
        change (some driven : Option (Machine.Config ctx.primCtx)) = some state at hs
        exact (Option.some.inj hs).symm
      subst state
      have hfinish : Machine.driveOp (finish (captured ++ args)) [] env stack = some driven := by
        rw [Machine.driveOp_collect finish (captured ++ args) [] (by simp)] at hdrive
        simpa using hdrive
      obtain ⟨start, hstart, hresult⟩ := Exact.EvaluatesFrom.driveOp_collect
        (finish := finish) (acc := []) (stack := stack) (base := stack)
        (result := result) hargs ⟨driven, hfinish, hfrom⟩
      have hstart' : Machine.driveOp
          (Op.Body.collect finish (captured.length + args.length) [])
          (Op.Arg.ofTerms terms) env stack = some start := by
        simpa [List.length_append] using hstart
      apply Exact.EvaluatesFrom.pureStep (next := start)
      · simp [Machine.step, Machine.evalTerm, Machine.driveSelectedOp,
          Machine.ofOption, hopId, hbodyTerms, hstart']
      exact hresult

end Exact.EvaluatesTo

namespace Exact.EvaluatesList

/-- Resume an application frame after one argument has returned, then collect the rest. -/
theorem collectApply {ctx : Ctx} {env scope : Env ctx.primCtx}
    {fn current result : Val ctx.primCtx} {prior values : List (Val ctx.primCtx)}
    {terms : List (Term ctx.primCtx)} {stack : List (Frame ctx.primCtx)}
    {hM : ctx.M = Id} (hterms : Exact.EvaluatesList ctx env terms values hM)
    (happly : Exact.EvaluatesApply ctx fn (prior ++ current :: values) result hM) :
    Exact.EvaluatesFrom ctx
      ⟨.ret current, scope, .args .apply (fn :: prior) terms env :: stack⟩ result stack hM := by
  induction hterms generalizing prior current scope with
  | nil =>
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.apply fn (prior ++ [current]), env, stack⟩)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Exact.idView]
      simpa using happly env stack
  | cons hterm hrest ih =>
      rename_i term terms value values _
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.eval term, env,
          .args .apply (fn :: prior ++ [current]) terms env :: stack⟩)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Exact.idView]
      apply Exact.EvaluatesFrom.bind
        (hterm (.args .apply (fn :: prior ++ [current]) terms env :: stack))
      intro nextScope
      apply ih
      simpa [List.append_assoc] using happly

end Exact.EvaluatesList

namespace Exact.EvaluatesTo

/-- Evaluate a surface application from exact function, argument, and value-application proofs. -/
@[zspec] theorem app {ctx : Ctx} {fn : Term ctx.primCtx} {args : List (Term ctx.primCtx)}
    {fnValue : Val ctx.primCtx} {argValues : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {env : Env ctx.primCtx} {hM : ctx.M = Id}
    (hfn : Exact.EvaluatesTo ctx env fn fnValue hM)
    (hargs : Exact.EvaluatesList ctx env args argValues hM)
    (happly : Exact.EvaluatesApply ctx fnValue argValues value hM) :
    Exact.EvaluatesTo ctx env (.app fn args) value hM := by
  intro stack
  apply Exact.EvaluatesFrom.pureStep
    (next := ⟨.eval fn, env, .args .apply [] args env :: stack⟩)
  · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, Machine.ofOption, Exact.idView]
  apply Exact.EvaluatesFrom.bind (hfn (.args .apply [] args env :: stack))
  intro scope
  cases hargs with
  | nil =>
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.apply fnValue [], env, stack⟩)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Exact.idView]
      exact happly env stack
  | @cons arg args argValue argValues _ harg hrest =>
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.eval arg, env, .args .apply [fnValue] args env :: stack⟩)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Exact.idView]
      apply Exact.EvaluatesFrom.bind
        (harg (.args .apply [fnValue] args env :: stack))
      intro argScope
      exact hrest.collectApply (prior := []) happly

/-- Evaluate a surface block call from an exact value-call specification. -/
@[zspec] theorem call {ctx : Ctx} {name : String} {args : List (Term ctx.primCtx)}
    {argValues : List (Val ctx.primCtx)} {value : Val ctx.primCtx}
    {env : Env ctx.primCtx} {block : Block ctx.primCtx} {hM : ctx.M = Id}
    (hcall : Exact.EvaluatesCallValues ctx name argValues value hM)
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : Exact.EvaluatesList ctx env args argValues hM) :
    Exact.EvaluatesTo ctx env (.call name args) value hM := by
  have happly : Exact.EvaluatesApply ctx
      (.blockRef name (block.params.map Prod.snd) block.outTy) argValues value hM :=
    Exact.EvaluatesApply.blockRef hcall
  intro stack
  cases hargs with
  | nil =>
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.apply (.blockRef name (block.params.map Prod.snd) block.outTy) [], env, stack⟩)
      · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, Machine.ofOption,
          Exact.idView, hblock]
      exact happly env stack
  | @cons arg args argValue argValues _ harg hrest =>
      apply Exact.EvaluatesFrom.pureStep
        (next := ⟨.eval arg, env, .args .apply
          [.blockRef name (block.params.map Prod.snd) block.outTy] args env :: stack⟩)
      · simp [Machine.step, Machine.evalTerm, Machine.evalTermImmediate, Machine.ofOption,
          Exact.idView, hblock]
      apply Exact.EvaluatesFrom.bind
        (harg (.args .apply
          [.blockRef name (block.params.map Prod.snd) block.outTy] args env :: stack))
      intro argScope
      exact hrest.collectApply (prior := []) happly

end Exact.EvaluatesTo

namespace Exact

/-- Exact evaluation of a block's instruction sequence in an `Id` context. -/
inductive EvaluatesInstrs (ctx : Ctx) :
    List (Instr ctx.primCtx) → Term ctx.primCtx → Env ctx.primCtx →
      Val ctx.primCtx → (hM : ctx.M = Id := by first | assumption | rfl) → Prop where
| nil {result env value hM} :
    EvaluatesTo ctx env result value hM →
    EvaluatesInstrs ctx [] result env value hM
| cons {instr instrs result env instrValue value hM} :
    EvaluatesTo ctx env instr.value instrValue hM →
    EvaluatesInstrs ctx instrs result (env ++ [(instr.name, instrValue)]) value hM →
    EvaluatesInstrs ctx (instr :: instrs) result env value hM

attribute [zspec] EvaluatesInstrs.nil EvaluatesInstrs.cons

namespace EvaluatesInstrs

/-- Install the machine continuations represented by an exact instruction-sequence proof. -/
theorem toEvaluatesFrom {ctx : Ctx} {instrs : List (Instr ctx.primCtx)}
    {result : Term ctx.primCtx} {env callerEnv : Env ctx.primCtx}
    {value : Val ctx.primCtx} {name : String} {base : List (Frame ctx.primCtx)}
    {hM : ctx.M = Id} (h : EvaluatesInstrs ctx instrs result env value hM) :
    EvaluatesFrom ctx
      (Machine.enterInstrs instrs result env (.call name callerEnv :: base)) value base hM := by
  induction h with
  | nil hresult =>
      apply EvaluatesFrom.bind (hresult (.call name callerEnv :: base))
      intro scope
      apply EvaluatesFrom.pureStep
      · rfl
      exact EvaluatesFrom.done
  | @cons instr instrs result env instrValue value hM hinstr hrest ih =>
      apply EvaluatesFrom.bind
        (hinstr (.instrs instr.name instrs result env :: .call name callerEnv :: base))
      intro scope
      apply EvaluatesFrom.pureStep
      · rfl
      exact ih

end EvaluatesInstrs

namespace EvaluatesCallValues

/-- A block lookup, arity check, and exact instruction sequence establish a value call. -/
@[zspec] theorem of_evaluatesInstrs {ctx : Ctx} {name : String}
    {vargs : List (Val ctx.primCtx)} {value : Val ctx.primCtx}
    {block : Block ctx.primCtx} {hM : ctx.M = Id}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : vargs.length = block.params.length)
    (hbody : EvaluatesInstrs ctx block.instrs block.result (block.entryEnv vargs) value hM) :
    EvaluatesCallValues ctx name vargs value hM := by
  intro callerEnv base
  refine ⟨block,
    Machine.enterInstrs block.instrs block.result (block.entryEnv vargs)
      (.call name callerEnv :: base), hblock, ?_, hbody.toEvaluatesFrom⟩
  simp [Machine.enterBlock, hargs]

/-- A block whose result exits directly to its own call frame. -/
@[zspec] theorem of_exit {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {value : Val ctx.primCtx} {block : Block ctx.primCtx} {term : Term ctx.primCtx}
    {hM : ctx.M = Id}
    (hblock : ctx.blockCtx.get? name = some block)
    (hargs : vargs.length = block.params.length)
    (hinstrs : block.instrs = [])
    (hresult : block.result = .exit name term)
    (hvalue : EvaluatesTo ctx (block.entryEnv vargs) term value hM) :
    EvaluatesCallValues ctx name vargs value hM := by
  intro callerEnv base
  let blockEnv := block.entryEnv vargs
  let callFrame := Frame.call name callerEnv
  let exitFrame := Frame.args (.exitTo name) [] [] blockEnv
  refine ⟨block, ⟨.eval (.exit name term), blockEnv, callFrame :: base⟩, hblock, ?_, ?_⟩
  · simp [Machine.enterBlock, hargs, hinstrs, hresult, Machine.enterInstrs,
      blockEnv, callFrame]
  · apply EvaluatesFrom.pureStep
      (next := ⟨.eval term, blockEnv, exitFrame :: callFrame :: base⟩)
    · rfl
    apply EvaluatesFrom.bind (hvalue (exitFrame :: callFrame :: base))
    intro scope
    apply EvaluatesFrom.pureStep
      (next := ⟨.exit name value, blockEnv, callFrame :: base⟩)
    · rfl
    apply EvaluatesFrom.pureStep
      (next := ⟨.ret value, callerEnv, base⟩)
    · simp [Machine.step, Machine.ofOption, Machine.unwindFrame, callFrame]
    exact EvaluatesFrom.done

theorem of_eq {ctx : Ctx} {name : String} {vargs : List (Val ctx.primCtx)}
    {canonical value : Val ctx.primCtx} {hM : ctx.M = Id}
    (hcall : EvaluatesCallValues ctx name vargs canonical hM)
    (hvalue : canonical = value) : EvaluatesCallValues ctx name vargs value hM := by
  subst value
  exact hcall

end EvaluatesCallValues

end Exact

end EvalTriple

namespace EvaluatesApply

export EvalTriple.EvaluatesApply (of_step opRef loop)

end EvaluatesApply

namespace EvaluatesFrom

export EvalTriple.EvaluatesFrom (apply_then apply_opBody driveOp_apply)

end EvaluatesFrom

end Zag
