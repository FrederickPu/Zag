import Zag.Data

/-!
`Zag`'s syntax determines which propositions can be stated (only first order statements about terms and types)
but allows the meta-theory (in this case lean) to determine which of those statements are provable.
Meaning that depending on the consistency strength of the metatheory different programs will provably terminate
(see goodstein sequence).
-/

namespace Zag

namespace Val

@[simp] theorem as?_mk {primCtx : PrimitiveCtx} (ty : Ty) (val : Ty.type primCtx ty) :
    (Val.mk ty val).as? ty = some val := by
  simp [as?]

end Val

/- converts a partial function `f?` into a total function `f` if `f?` returns a value on all inputs
  otherwise returns none -/
def finPiOption : {n : Nat} → {A : Fin n → Type} → ((i : Fin n) → Option (A i)) → Option ((i : Fin n) → A i)
| 0, _, _ => some fun i => absurd i.isLt (Nat.not_lt_zero _)
| _ + 1, _, f => do
    let head ← f 0
    let tail ← finPiOption (fun i => f i.succ)
    some (Fin.cases head tail)

def valsAs? {primCtx : PrimitiveCtx} (tys : List Ty) (vals : List (Val primCtx)) :
    Option ((idx : Fin tys.length) → Ty.type primCtx tys[idx]) :=
  if vals.length = tys.length then
    finPiOption (fun idx => do
      let v ← vals[(idx : Nat)]?
      v.as? tys[idx])
  else none

def Op.Body.applyVals {primCtx : PrimitiveCtx} :
    Op.Body primCtx → List (Val primCtx) → Option (Val primCtx)
| .fail, _ => none
| .done value, _ => some value
| .next _ _, [] => none
| .next evaluate resume, value :: rest =>
    (resume (if evaluate then some value else none)).applyVals rest
termination_by _ vals => vals.length

/- apply an operator after dynamically checking its arity and domain -/
def Op.applyVals {primCtx : PrimitiveCtx} (oper : Op primCtx) (vals : List (Val primCtx)) :
    Option (Val primCtx) :=
  if vals.length = oper.arity then
    oper.body.applyVals vals
  else none

@[simp] theorem Op.Signature.applyVals_unary {primCtx : PrimitiveCtx} (output : Ty → Ty)
    (run : (input : Ty) → Ty.type primCtx input → Ty.type primCtx (output input))
    (input : Ty) (value : Ty.type primCtx input) :
    Op.applyVals (Signature.unary output run).toOp [Val.mk input value] =
      some (Val.mk (output input) (run input value)) := by
  simp [Op.applyVals, Signature.toOp, Signature.unary, Signature.eagerBody,
    Signature.apply, Op.Body.applyVals]

def PrimFunc.apply {primCtx : PrimitiveCtx} (pfunc : PrimFunc primCtx) (vargs : List (Val primCtx)) : Option (Val primCtx) :=
  if vargs.length = pfunc.args.length then do
    let raw ← (← pfunc.interp vargs).as? pfunc.outTy
    some (Val.mk pfunc.outTy raw)
  else none

def PrimFunc.toVal {primCtx : PrimitiveCtx} (pfunc : PrimFunc primCtx) : Val primCtx :=
  Val.mk pfunc.ty
    (cast (Ty.type.eq_6 primCtx (pfunc.args.map (.prim ·)) pfunc.outTy).symm
      (fun args => do
        let argTys := pfunc.args.map (.prim ·)
        let vargs := (List.finRange argTys.length).map fun idx =>
          Val.mk argTys[idx] (args idx)
        let result ← pfunc.apply vargs
        result.as? pfunc.outTy))

def Term.evalMkStruct {primCtx : PrimitiveCtx} (tys : List Ty) (vargs : List (Val primCtx)) : Option (Val primCtx) := do
  let fields ← valsAs? tys vargs
  some (Val.mk (.struct tys) (cast (Ty.type.eq_5 primCtx tys).symm fields))

def Term.evalApp {primCtx : PrimitiveCtx} (fn : Val primCtx) (args : List (Val primCtx)) : Option (Val primCtx) :=
  match h : fn.ty with
  | .func argsTy outTy => do
      let typedArgs ← valsAs? argsTy args
      let funcVal := cast (congrArg (Ty.type primCtx) h) fn.val
      let f := cast (Ty.type.eq_6 primCtx argsTy outTy) funcVal
      let result ← f typedArgs
      some (Val.mk outTy result)
  | _ => none

def Term.motiveVal {primCtx : PrimitiveCtx} (stateTy resultTy : Ty) : Val primCtx :=
  Val.mk (.func [stateTy] resultTy)
    (cast (Ty.type.eq_6 primCtx [stateTy] resultTy).symm
      (fun _ => none))

structure Term.MotiveCtx (primCtx : PrimitiveCtx) where
  body : Term primCtx
  env : List (Val primCtx)
  stateTy : Ty
  resultTy : Ty

/- Find the motive named by the de Bruijn variable `idx`, searching all enclosing motives. Returns it with the stack prefix up to and including it
  (re-invoking a motive restarts that level, so inner motives are dropped). -/
def Term.MotiveCtx.findMotive {primCtx : PrimitiveCtx} (idx : Nat)
    (motives : List (Term.MotiveCtx primCtx)) : Option (Term.MotiveCtx primCtx × List (Term.MotiveCtx primCtx)) := do
  let i ← motives.findIdx? (·.env.length + 1 = idx)
  let motive ← motives[i]?
  some (motive, motives.take (i + 1))

mutual

def Term.evalGo (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx)) :
    Term ctx.primCtx → Option (Val ctx.primCtx)
| .prim ty val => some (Val.mk ty val)
| .primFunc name => do
    let pfunc ← ctx.primFuncCtx.get? name
    some pfunc.toVal
| .var idx => env[idx]?
| .op name args => do
    let oper ← ctx.opCtx.get? name
    if args.length = oper.arity then
      Term.evalBody ctx motives env args oper.body
    else none
| .mkStruct tys =>
    some <| Val.mk (.func tys (.struct tys))
      (cast (Ty.type.eq_6 ctx.primCtx tys (.struct tys)).symm
        (fun args => some (cast (Ty.type.eq_5 ctx.primCtx tys).symm args)))
| .structProj tys idx =>
    some <| Val.mk (.func [.struct tys] tys[idx])
      (cast (Ty.type.eq_6 ctx.primCtx [.struct tys] tys[idx]).symm
        (fun args => some ((cast (Ty.type.eq_5 ctx.primCtx tys) (args 0)) idx)))
| .app (.primFunc name) args => do
    let pfunc ← ctx.primFuncCtx.get? name
    let vargs ← Term.evalList ctx motives env args
    PrimFunc.apply pfunc vargs
| .app (.mkStruct tys) args => do
    let vargs ← Term.evalList ctx motives env args
    Term.evalMkStruct tys vargs
| .app (.structProj tys idx) [arg] => do
    let value ← Term.evalGo ctx motives env arg
    let fields ← value.as? (.struct tys)
    some (Val.mk tys[idx] ((cast (Ty.type.eq_5 ctx.primCtx tys) fields) idx))
| .app (.var idx) [arg] =>
    -- A `.var idx` in application position may be a motive of *any* enclosing recursor (e.g. an
    -- inner loop body calling the outer motive to break out), so we search the whole recursor
    -- stack rather than only the innermost context.
    match Term.MotiveCtx.findMotive idx motives with
    | some (motive, stack) => do
        let state ← Term.evalGo ctx motives env arg
        let stateRaw ← state.as? motive.stateTy
        let stateVal := Val.mk motive.stateTy stateRaw
        let motiveVal := Term.motiveVal motive.stateTy motive.resultTy
        let result ← Term.evalGo ctx stack (motive.env ++ [stateVal, motiveVal]) motive.body
        let resultRaw ← result.as? motive.resultTy
        some (Val.mk motive.resultTy resultRaw)
    | none => do
        let vf ← Term.evalGo ctx motives env (.var idx)
        let varg ← Term.evalGo ctx motives env arg
        Term.evalApp vf [varg]
| .app f args => do
    let vf ← Term.evalGo ctx motives env f
    let vargs ← Term.evalList ctx motives env args
    Term.evalApp vf vargs
| .recurse resultTy init body => do
    let v ← Term.evalGo ctx motives env init
    let motiveVal := Term.motiveVal v.ty resultTy
    let motiveCtx : Term.MotiveCtx ctx.primCtx :=
      { body := body, env := env, stateTy := v.ty, resultTy := resultTy }
    Term.evalGo ctx (motives ++ [motiveCtx]) (env ++ [v, motiveVal]) body
partial_fixpoint

def Term.evalList (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (terms : List (Term ctx.primCtx)) : Option (List (Val ctx.primCtx)) :=
  terms.mapM (Term.evalGo ctx motives env)
partial_fixpoint

def Term.evalBody (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx)) :
    List (Term ctx.primCtx) → Op.Body ctx.primCtx → Option (Val ctx.primCtx)
| _, .fail => none
| _, .done value => some value
| [], .next _ _ => none
| term :: terms, .next evaluate resume =>
    if evaluate then do
      let value ← Term.evalGo ctx motives env term
      Term.evalBody ctx motives env terms (resume (some value))
    else
      Term.evalBody ctx motives env terms (resume none)
partial_fixpoint

end

theorem Term.evalBody_nil (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (body : Op.Body ctx.primCtx) :
    Term.evalBody ctx motives env [] body = body.applyVals [] := by
  rw [Term.evalBody.eq_def]
  cases body <;> simp [Op.Body.applyVals]

@[simp] theorem Term.evalBody_fail (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (terms : List (Term ctx.primCtx)) :
    Term.evalBody ctx motives env terms .fail = none := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_done (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (terms : List (Term ctx.primCtx)) (value : Val ctx.primCtx) :
    Term.evalBody ctx motives env terms (.done value) = some value := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_next_nil (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (evaluate : Bool) (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx motives env [] (.next evaluate resume) = none := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_next_true (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx motives env (term :: terms) (.next true resume) = (do
      let value ← Term.evalGo ctx motives env term
      Term.evalBody ctx motives env terms (resume (some value))) := by
  rw [Term.evalBody.eq_def]
  rfl

@[simp] theorem Term.evalBody_next_false (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx motives env (term :: terms) (.next false resume) =
      Term.evalBody ctx motives env terms (resume none) := by
  rw [Term.evalBody.eq_def]
  rfl

@[simp] theorem Term.evalBody_eagerBody_one (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (sig : Op.Signature ctx.primCtx 1) (term : Term ctx.primCtx) (value : Val ctx.primCtx)
    (heval : Term.evalGo ctx motives env term = some value) :
    Term.evalBody ctx motives env [term] (sig.eagerBody 1 []) =
      (sig.eagerBody 1 []).applyVals [value] := by
  simp [Op.Signature.eagerBody, heval, Term.evalBody_nil, Op.Body.applyVals]

@[simp] theorem Term.evalBody_eagerBody_two (ctx : Ctx)
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (sig : Op.Signature ctx.primCtx 2) (a b : Term ctx.primCtx) (va vb : Val ctx.primCtx)
    (ha : Term.evalGo ctx motives env a = some va)
    (hb : Term.evalGo ctx motives env b = some vb) :
    Term.evalBody ctx motives env [a, b] (sig.eagerBody 2 []) =
      (sig.eagerBody 2 []).applyVals [va, vb] := by
  simp [Op.Signature.eagerBody, ha, hb, Term.evalBody_nil, Op.Body.applyVals]

def Term.eval (ctx : Ctx)
    (env : List (Val ctx.primCtx)) (term : Term ctx.primCtx) : Option (Val ctx.primCtx) :=
  Term.evalGo ctx [] env term

theorem Term.hasType_lift {ctx : Ctx}
    {varCtx : VarCtx} {term : Term ctx.primCtx} {ty : Ty}
    (hterm : term.hasType ctx varCtx ty) :
    (Term.lift term).hasType ctx varCtx (.m ty) := by
  apply Term.hasType.op (tys := [ty]) (by rfl)
  · intro idx
    have hlt := idx.isLt
    change idx.val < 1 at hlt
    have hval : idx.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
    have hidx : idx = 0 := Fin.ext hval
    subst idx
    simpa using hterm
  · unfold OpCtx.outTy?
    simp [OpCtx.get?, Op.pure]

theorem Op.applyVals_pure {primCtx : PrimitiveCtx} (value : Val primCtx) :
    Op.applyVals Op.pure [value] =
      some (Val.mk (.m value.ty)
        (Ty.ofM primCtx value.ty (Pure.pure (some value.val)))) := by
  exact Signature.applyVals_unary .m
    (fun ty value => Ty.ofM primCtx ty (Pure.pure (some value))) value.ty value.val

theorem Term.evalGo_lift {ctx : Ctx}
    {motives : List (Term.MotiveCtx ctx.primCtx)}
    {env : List (Val ctx.primCtx)} {term : Term ctx.primCtx} {value : Val ctx.primCtx}
    (heval : Term.evalGo ctx motives env term = some value) :
    Term.evalGo ctx motives env (Term.lift term) =
      some (Val.mk (.m value.ty)
        (Ty.ofM ctx.primCtx value.ty (Pure.pure (some value.val)))) := by
  have hform : Term.evalGo ctx motives env (Term.lift term) =
      Op.applyVals Op.pure [value] := by
    rw [Term.evalGo.eq_def]
    simp [Term.lift, OpCtx.get?, heval, Op.pure, Op.applyVals,
      Op.Signature.eagerBody, Op.Body.applyVals, Term.evalBody_nil]
  rw [hform, Op.applyVals_pure]

/- termination of a partial `Option` evaluator is successful evaluation -/
def Term.Terminates (ctx : Ctx)
    (env : List (Val ctx.primCtx)) (term : Term ctx.primCtx) : Prop :=
  ∃ v, Term.eval ctx env term = some v

/- equality at `m` types is the equality supplied by the context's monad -/
structure Term.eq (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) (t₁ t₂ : Term ctx.primCtx) : Prop where
  hasType₁ : hasType ctx varCtx t₁ ty
  hasType₂ : hasType ctx varCtx t₂ ty
  eq : ∀ env : List (Val ctx.primCtx), env.length = varCtx.length →
    t₁.eval ctx env = t₂.eval ctx env

def Ty.subst (ctxTy : List Ty) : Ty → Ty
| .var idx =>
    if idx < ctxTy.length then
      (ctxTy[idx]?).getD (.var idx)
    else
      .var (idx - ctxTy.length)
| .prim b => .prim b
| .option ty => .option (Ty.subst ctxTy ty)
| .union tys => .union (tys.map (Ty.subst ctxTy))
| .struct tys => .struct (tys.map (Ty.subst ctxTy))
| .func args ret => .func (args.map (Ty.subst ctxTy)) (Ty.subst ctxTy ret)
| .m ty => .m (Ty.subst ctxTy ty)

def Term.subst {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx)) (term : Term primCtx) : Term primCtx :=
  match ctxTerm with
  | [] => term
  | _ :: _ =>
      match term with
      | .prim ty val => .prim ty val
      | .primFunc name => .primFunc name
      | .var idx =>
          if idx < ctxTerm.length then
            (ctxTerm[idx]?).getD (.var idx)
          else
            .var (idx - ctxTerm.length)
      | .op name args => .op name (args.map (Term.subst ctxTerm))
      | .app f args => .app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm))
      | .mkStruct tys => .mkStruct tys
      | .structProj tys idx => .structProj tys idx
      | .recurse resultTy init body =>
          .recurse resultTy (Term.subst ctxTerm init) (Term.subst ctxTerm body)

@[simp] theorem Term.subst_nil {primCtx : PrimitiveCtx} (term : Term primCtx) :
    Term.subst [] term = term := by
  simp [Term.subst]

@[simp] theorem Term.subst_prim {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (ty : Ty) (val : Ty.type primCtx ty) :
    Term.subst ctxTerm (.prim ty val) = .prim ty val := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_primFunc {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (name : String) :
    Term.subst ctxTerm (.primFunc name) = .primFunc name := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_var {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (idx : Nat) :
    Term.subst ctxTerm (.var idx) =
      if idx < ctxTerm.length then (ctxTerm[idx]?).getD (.var idx) else .var (idx - ctxTerm.length) := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_op {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (name : String) (args : List (Term primCtx)) :
    Term.subst ctxTerm (.op name args) = .op name (args.map (Term.subst ctxTerm)) := by
  cases ctxTerm with
  | nil =>
      have hmap : args.map (Term.subst ([] : List (Term primCtx))) = args := by
        induction args with
        | nil => simp
        | cons arg args ih => simp [ih]
      simp [hmap]
  | cons head tail => simp [Term.subst]

@[simp] theorem Term.subst_app {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (f : Term primCtx) (args : List (Term primCtx)) :
    Term.subst ctxTerm (.app f args) = .app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm)) := by
  cases ctxTerm with
  | nil =>
      have hmap : args.map (Term.subst ([] : List (Term primCtx))) = args := by
        induction args with
        | nil => simp
        | cons arg args ih => simp [ih]
      simp [hmap]
  | cons head tail => simp [Term.subst]

@[simp] theorem Term.subst_mkStruct {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (tys : List Ty) :
    Term.subst ctxTerm (.mkStruct tys) = .mkStruct tys := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_structProj {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (tys : List Ty) (idx : Fin tys.length) :
    Term.subst ctxTerm (.structProj tys idx) = .structProj tys idx := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_recurse {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (resultTy : Ty) (init body : Term primCtx) :
    Term.subst ctxTerm (.recurse resultTy init body) =
      .recurse resultTy (Term.subst ctxTerm init) (Term.subst ctxTerm body) := by
  cases ctxTerm <;> simp [Term.subst]

/- Zag propositions can only be assigned semantics under a fixed `Ctx` -/
def Pr.interp (ctx : Ctx) :
    (ctxTy : List Ty) → (ctxTerm : List (Term ctx.primCtx)) → Pr (Term ctx.primCtx) → Prop
| ctxTy, ctxTerm, .eq varCtx ty x y =>
  Term.eq ctx (varCtx.map (Ty.subst ctxTy)) (Ty.subst ctxTy ty) (Term.subst ctxTerm x) (Term.subst ctxTerm y)
| ctxTy, ctxTerm, .hasType varCtx t ty =>
  Term.hasType ctx (varCtx.map (Ty.subst ctxTy)) (Term.subst ctxTerm t) (Ty.subst ctxTy ty)
| ctxTy, ctxTerm, .and p q =>
  Pr.interp ctx ctxTy ctxTerm p ∧ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .or p q =>
  Pr.interp ctx ctxTy ctxTerm p ∨ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .implies p q =>
  Pr.interp ctx ctxTy ctxTerm p → Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .forallTy p =>
  ∀ (α : Ty), Pr.interp ctx (ctxTy ++ [α]) ctxTerm p
| ctxTy, ctxTerm, .forallTerm p =>
  ∀ (x : Term ctx.primCtx), Pr.interp ctx ctxTy (ctxTerm ++ [x]) p

/- metatheory (in this case lean) determines which Zag propositions are provable -/
inductive Pr.Provable (ctx : Ctx)
    (ctxTy : List Ty) (ctxTerm : List (Term ctx.primCtx)) (p : Pr (Term ctx.primCtx)) : Prop
| ofProof (proof : Pr.interp ctx ctxTy ctxTerm p)

end Zag
