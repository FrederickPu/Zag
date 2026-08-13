import Zag.Data

/-!
`Zag`'s syntax determines which propositions can be stated (only first order statements about terms and types)
but allows the meta-theory (in this case lean) to determine which of those statements are provable.
Meaning that depending on the consistency strength of the metatheory different programs will provably terminate
(see goodstein sequence).

Evaluation is partial: a block may call itself, so `Term.evalGo` is defined by
`partial_fixpoint` and a non-terminating program evaluates to `none`.
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
  simp [Op.applyVals, Signature.toOp, Signature.unary, Signature.eagerBody, Op.Body.eager,
    Signature.apply, Op.Body.applyVals]

def Term.evalApp {primCtx : PrimitiveCtx} (fn : Val primCtx) (args : List (Val primCtx)) :
    Option (Val primCtx) :=
  match h : fn.ty with
  | .func argsTy outTy => do
      let typedArgs ← valsAs? argsTy args
      let funcVal := cast (congrArg (Ty.type primCtx) h) fn.val
      let f := cast (Ty.type_func primCtx argsTy outTy) funcVal
      let result ← f typedArgs
      some (Val.mk outTy result)
  | _ => none

/- the environment a block is entered with: each parameter name bound to its argument -/
def Block.entryEnv {primCtx : PrimitiveCtx} (block : Block primCtx)
    (vargs : List (Val primCtx)) : Env primCtx :=
  (block.params.map Prod.fst).zip vargs

mutual

def Term.evalGo (ctx : Ctx) (env : Env ctx.primCtx) :
    Term ctx.primCtx → Option (Val ctx.primCtx)
| .prim ty val => some (Val.mk ty val)
| .var name => Scope.get? env name
| .op name args => do
    let oper ← ctx.opCtx.get? name
    if args.length = oper.arity then
      Term.evalBody ctx env args oper.body
    else none
| .call name args => do
    let block ← ctx.blockCtx.get? name
    let vargs ← Term.evalList ctx env args
    if vargs.length = block.params.length then
      Term.evalBlock ctx (block.entryEnv vargs) block
    else none
| .app f args => do
    let vf ← Term.evalGo ctx env f
    let vargs ← Term.evalList ctx env args
    Term.evalApp vf vargs
partial_fixpoint

/- run a block's instructions in order, then return its result term -/
def Term.evalBlock (ctx : Ctx) (env : Env ctx.primCtx) (block : Block ctx.primCtx) :
    Option (Val ctx.primCtx) := do
  let scope ← Term.evalInstrs ctx env block.instrs
  Term.evalGo ctx scope block.result
partial_fixpoint

/- each instruction extends the environment with its own name -/
def Term.evalInstrs (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Instr ctx.primCtx) → Option (Env ctx.primCtx)
| [] => some env
| instr :: instrs => do
    let value ← Term.evalGo ctx env instr.value
    Term.evalInstrs ctx (env ++ [(instr.name, value)]) instrs
partial_fixpoint

def Term.evalList (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) : Option (List (Val ctx.primCtx)) :=
  terms.mapM (Term.evalGo ctx env)
partial_fixpoint

def Term.evalBody (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Term ctx.primCtx) → Op.Body ctx.primCtx → Option (Val ctx.primCtx)
| _, .fail => none
| _, .done value => some value
| [], .next _ _ => none
| term :: terms, .next evaluate resume =>
    if evaluate then do
      let value ← Term.evalGo ctx env term
      Term.evalBody ctx env terms (resume (some value))
    else
      Term.evalBody ctx env terms (resume none)
partial_fixpoint

end

theorem Term.evalBody_nil (ctx : Ctx) (env : Env ctx.primCtx) (body : Op.Body ctx.primCtx) :
    Term.evalBody ctx env [] body = body.applyVals [] := by
  rw [Term.evalBody.eq_def]
  cases body <;> simp [Op.Body.applyVals]

@[simp] theorem Term.evalBody_fail (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) :
    Term.evalBody ctx env terms .fail = none := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_done (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) (value : Val ctx.primCtx) :
    Term.evalBody ctx env terms (.done value) = some value := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_next_nil (ctx : Ctx) (env : Env ctx.primCtx)
    (evaluate : Bool) (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env [] (.next evaluate resume) = none := by
  rw [Term.evalBody.eq_def]

@[simp] theorem Term.evalBody_next_true (ctx : Ctx) (env : Env ctx.primCtx)
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env (term :: terms) (.next true resume) = (do
      let value ← Term.evalGo ctx env term
      Term.evalBody ctx env terms (resume (some value))) := by
  rw [Term.evalBody.eq_def]
  rfl

@[simp] theorem Term.evalBody_next_false (ctx : Ctx) (env : Env ctx.primCtx)
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env (term :: terms) (.next false resume) =
      Term.evalBody ctx env terms (resume none) := by
  rw [Term.evalBody.eq_def]
  rfl

@[simp] theorem Term.evalBody_eager_one (ctx : Ctx) (env : Env ctx.primCtx)
    (run : List (Val ctx.primCtx) → Option (Val ctx.primCtx))
    (term : Term ctx.primCtx) (value : Val ctx.primCtx)
    (heval : Term.evalGo ctx env term = some value) :
    Term.evalBody ctx env [term] (Op.Body.eager run 1 []) =
      (Op.Body.eager run 1 []).applyVals [value] := by
  simp [Op.Body.eager, heval, Term.evalBody_nil, Op.Body.applyVals]

@[simp] theorem Term.evalBody_eager_two (ctx : Ctx) (env : Env ctx.primCtx)
    (run : List (Val ctx.primCtx) → Option (Val ctx.primCtx))
    (a b : Term ctx.primCtx) (va vb : Val ctx.primCtx)
    (ha : Term.evalGo ctx env a = some va)
    (hb : Term.evalGo ctx env b = some vb) :
    Term.evalBody ctx env [a, b] (Op.Body.eager run 2 []) =
      (Op.Body.eager run 2 []).applyVals [va, vb] := by
  simp [Op.Body.eager, ha, hb, Term.evalBody_nil, Op.Body.applyVals]

def Term.eval (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx) :
    Option (Val ctx.primCtx) :=
  Term.evalGo ctx env term

/- termination of a partial `Option` evaluator is successful evaluation -/
def Term.Terminates (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx) : Prop :=
  ∃ v, Term.eval ctx env term = some v

def Term.subst {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (term : Term primCtx) : Term primCtx :=
  match ctxTerm with
  | [] => term
  | _ :: _ =>
      match term with
      | .prim ty val => .prim ty val
      | .var name => (Scope.get? ctxTerm name).getD (.var name)
      | .op name args => .op name (args.map (Term.subst ctxTerm))
      | .call name args => .call name (args.map (Term.subst ctxTerm))
      | .app f args => .app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm))

@[simp] theorem Term.subst_nil {primCtx : PrimitiveCtx} (term : Term primCtx) :
    Term.subst [] term = term := by
  simp [Term.subst]

private theorem Term.map_subst_nil {primCtx : PrimitiveCtx} (terms : List (Term primCtx)) :
    terms.map (Term.subst []) = terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ih]

@[simp] theorem Term.subst_prim {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (ty : Ty) (val : Ty.type primCtx ty) :
    Term.subst ctxTerm (.prim ty val) = .prim ty val := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_var {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) :
    Term.subst ctxTerm (.var name) = (Scope.get? ctxTerm name).getD (.var name) := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_op {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (args : List (Term primCtx)) :
    Term.subst ctxTerm (.op name args) = .op name (args.map (Term.subst ctxTerm)) := by
  cases ctxTerm <;> simp [Term.subst, Term.map_subst_nil]

@[simp] theorem Term.subst_call {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (args : List (Term primCtx)) :
    Term.subst ctxTerm (.call name args) = .call name (args.map (Term.subst ctxTerm)) := by
  cases ctxTerm <;> simp [Term.subst, Term.map_subst_nil]

@[simp] theorem Term.subst_app {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (f : Term primCtx) (args : List (Term primCtx)) :
    Term.subst ctxTerm (.app f args) =
      .app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm)) := by
  cases ctxTerm <;> simp [Term.subst, Term.map_subst_nil]

/- instantiate the generic type variables of every type in a scope -/
def VarCtx.subst (ctxTy : Scope Ty) (varCtx : VarCtx) : VarCtx :=
  varCtx.map (fun entry => (entry.1, Ty.subst ctxTy entry.2))

/- two terms are equal at a type when they evaluate alike under every environment matching the
  scope they are stated in -/
structure Term.eq (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) (t₁ t₂ : Term ctx.primCtx) : Prop where
  hasType₁ : hasType ctx varCtx t₁ ty
  hasType₂ : hasType ctx varCtx t₂ ty
  eq : ∀ env : Env ctx.primCtx, env.Models varCtx →
    t₁.eval ctx env = t₂.eval ctx env

/- Zag propositions can only be assigned semantics under a fixed `Ctx` -/
def Pr.interp (ctx : Ctx) :
    (ctxTy : Scope Ty) → (ctxTerm : Scope (Term ctx.primCtx)) → Pr (Term ctx.primCtx) → Prop
| ctxTy, ctxTerm, .eq varCtx ty x y =>
  Term.eq ctx (VarCtx.subst ctxTy varCtx) (Ty.subst ctxTy ty)
    (Term.subst ctxTerm x) (Term.subst ctxTerm y)
| ctxTy, ctxTerm, .hasType varCtx t ty =>
  Term.hasType ctx (VarCtx.subst ctxTy varCtx) (Term.subst ctxTerm t) (Ty.subst ctxTy ty)
| ctxTy, ctxTerm, .and p q =>
  Pr.interp ctx ctxTy ctxTerm p ∧ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .or p q =>
  Pr.interp ctx ctxTy ctxTerm p ∨ Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .implies p q =>
  Pr.interp ctx ctxTy ctxTerm p → Pr.interp ctx ctxTy ctxTerm q
| ctxTy, ctxTerm, .forallTy name p =>
  ∀ (α : Ty), Pr.interp ctx (ctxTy ++ [(name, α)]) ctxTerm p
| ctxTy, ctxTerm, .forallTerm name p =>
  ∀ (x : Term ctx.primCtx), Pr.interp ctx ctxTy (ctxTerm ++ [(name, x)]) p

/- metatheory (in this case lean) determines which Zag propositions are provable -/
inductive Pr.Provable (ctx : Ctx)
    (ctxTy : Scope Ty) (ctxTerm : Scope (Term ctx.primCtx)) (p : Pr (Term ctx.primCtx)) : Prop
| ofProof (proof : Pr.interp ctx ctxTy ctxTerm p)

end Zag
