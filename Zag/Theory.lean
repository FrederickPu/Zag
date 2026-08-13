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

/- Evaluating anything either produces an `α` or unwinds the call stack, carrying the value to
  return and the name of the block to return it from. This is the `retBlock` continuation list
  of a stack-based IR, reified as data: naming a block is how you pick a frame to return from. -/
inductive Outcome (primCtx : PrimitiveCtx) (α : Type) where
| ok (value : α)
| exit (block : String) (value : Val primCtx)

def Outcome.ok? {primCtx : PrimitiveCtx} {α : Type} : Outcome primCtx α → Option α
| .ok value => some value
| .exit _ _ => none

@[simp] theorem Outcome.bind_map_ok {primCtx : PrimitiveCtx} {α : Type} (o : Option α) :
    (o.map (Outcome.ok (primCtx := primCtx))).bind Outcome.ok? = o := by
  cases o <;> rfl

mutual

def Term.evalOutcome (ctx : Ctx) (env : Env ctx.primCtx) :
    Term ctx.primCtx → Option (Outcome ctx.primCtx (Val ctx.primCtx))
| .prim ty val => some (.ok (Val.mk ty val))
| .var name => (Scope.get? env name).map .ok
| .exit blockName value => do
    match ← Term.evalOutcome ctx env value with
    | .ok v => some (.exit blockName v)
    | .exit b v => some (.exit b v)
| .op name args => do
    let oper ← ctx.opCtx.get? name
    if args.length = oper.arity then
      Term.evalBodyOutcome ctx env args oper.body
    else none
| .call name args => do
    let block ← ctx.blockCtx.get? name
    match ← Term.evalListOutcome ctx env args with
    | .exit b v => some (.exit b v)
    | .ok vargs =>
        if vargs.length = block.params.length then
          Term.evalBlock ctx name (block.entryEnv vargs) block
        else none
| .app f args => do
    match ← Term.evalOutcome ctx env f with
    | .exit b v => some (.exit b v)
    | .ok vf =>
        match ← Term.evalListOutcome ctx env args with
        | .exit b v => some (.exit b v)
        | .ok vargs => (Term.evalApp vf vargs).map .ok
partial_fixpoint

/- A call is the frame an unwind can target: an exit naming `name` stops here and becomes this
  call's value, and any other exit keeps unwinding to an outer frame. -/
def Term.evalBlock (ctx : Ctx) (name : String) (env : Env ctx.primCtx)
    (block : Block ctx.primCtx) : Option (Outcome ctx.primCtx (Val ctx.primCtx)) := do
  match ← Term.evalInstrs ctx env block.instrs with
  | .exit b v => some (if b = name then .ok v else .exit b v)
  | .ok scope =>
      match ← Term.evalOutcome ctx scope block.result with
      | .exit b v => some (if b = name then .ok v else .exit b v)
      | .ok v => some (.ok v)
partial_fixpoint

/- Each instruction extends the environment with its own name. An instruction that unwinds skips
  every later instruction and the block's result term -- that is early return. -/
def Term.evalInstrs (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Instr ctx.primCtx) → Option (Outcome ctx.primCtx (Env ctx.primCtx))
| [] => some (.ok env)
| instr :: instrs => do
    match ← Term.evalOutcome ctx env instr.value with
    | .exit b v => some (.exit b v)
    | .ok value => Term.evalInstrs ctx (env ++ [(instr.name, value)]) instrs
partial_fixpoint

def Term.evalListOutcome (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Term ctx.primCtx) → Option (Outcome ctx.primCtx (List (Val ctx.primCtx)))
| [] => some (.ok [])
| term :: terms => do
    match ← Term.evalOutcome ctx env term with
    | .exit b v => some (.exit b v)
    | .ok value =>
        match ← Term.evalListOutcome ctx env terms with
        | .exit b v => some (.exit b v)
        | .ok vals => some (.ok (value :: vals))
partial_fixpoint

def Term.evalBodyOutcome (ctx : Ctx) (env : Env ctx.primCtx) :
    List (Term ctx.primCtx) → Op.Body ctx.primCtx →
      Option (Outcome ctx.primCtx (Val ctx.primCtx))
| _, .fail => none
| _, .done value => some (.ok value)
| [], .next _ _ => none
| term :: terms, .next evaluate resume =>
    if evaluate then do
      match ← Term.evalOutcome ctx env term with
      | .exit b v => some (.exit b v)
      | .ok value => Term.evalBodyOutcome ctx env terms (resume (some value))
    else
      Term.evalBodyOutcome ctx env terms (resume none)
partial_fixpoint

end

/-! ### the value-level view

  An unwind that escapes every enclosing call is stuck, so at the level of values evaluation
  behaves exactly as it did before non-local exit existed. Every equation below is the
  definition `Term.evalGo` used to have. -/

def Term.evalGo (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx) :
    Option (Val ctx.primCtx) :=
  (Term.evalOutcome ctx env term).bind Outcome.ok?

def Term.evalList (ctx : Ctx) (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx)) :
    Option (List (Val ctx.primCtx)) :=
  (Term.evalListOutcome ctx env terms).bind Outcome.ok?

def Term.evalBody (ctx : Ctx) (env : Env ctx.primCtx) (terms : List (Term ctx.primCtx))
    (body : Op.Body ctx.primCtx) : Option (Val ctx.primCtx) :=
  (Term.evalBodyOutcome ctx env terms body).bind Outcome.ok?

@[simp] theorem Term.evalGo_prim (ctx : Ctx) (env : Env ctx.primCtx) (ty : Ty)
    (val : Ty.type ctx.primCtx ty) :
    Term.evalGo ctx env (.prim ty val) = some (Val.mk ty val) := by
  simp [Term.evalGo, Term.evalOutcome.eq_def, Outcome.ok?]

@[simp] theorem Term.evalGo_var (ctx : Ctx) (env : Env ctx.primCtx) (name : String) :
    Term.evalGo ctx env (.var name) = Scope.get? env name := by
  rw [Term.evalGo, Term.evalOutcome.eq_def]
  cases h : Scope.get? env name <;> simp [h, Outcome.ok?]

@[simp] theorem Term.evalGo_op (ctx : Ctx) (env : Env ctx.primCtx) (name : String)
    (args : List (Term ctx.primCtx)) :
    Term.evalGo ctx env (.op name args) = (do
      let oper ← ctx.opCtx.get? name
      if args.length = oper.arity then Term.evalBody ctx env args oper.body else none) := by
  simp [Term.evalGo, Term.evalOutcome.eq_def, Term.evalBody]
  cases hop : ctx.opCtx.get? name with
  | none => simp
  | some oper =>
      by_cases h : args.length = oper.arity <;> simp [h]

theorem Term.evalGo_exit (ctx : Ctx) (env : Env ctx.primCtx) (name : String)
    (value : Term ctx.primCtx) :
    Term.evalGo ctx env (.exit name value) = none := by
  rw [Term.evalGo, Term.evalOutcome.eq_def]
  cases hvalue : Term.evalOutcome ctx env value with
  | none => simp [hvalue]
  | some outcome => cases outcome <;> simp [hvalue, Outcome.ok?]

def Term.eval (ctx : Ctx) (env : Env ctx.primCtx) (term : Term ctx.primCtx) :
    Option (Val ctx.primCtx) :=
  Term.evalGo ctx env term

theorem Term.evalBody_nil (ctx : Ctx) (env : Env ctx.primCtx) (body : Op.Body ctx.primCtx) :
    Term.evalBody ctx env [] body = body.applyVals [] := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def]
  cases body <;> simp [Op.Body.applyVals, Outcome.ok?]

@[simp] theorem Term.evalBody_fail (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) :
    Term.evalBody ctx env terms .fail = none := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def]
  rfl

@[simp] theorem Term.evalBody_done (ctx : Ctx) (env : Env ctx.primCtx)
    (terms : List (Term ctx.primCtx)) (value : Val ctx.primCtx) :
    Term.evalBody ctx env terms (.done value) = some value := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def]
  rfl

@[simp] theorem Term.evalBody_next_nil (ctx : Ctx) (env : Env ctx.primCtx)
    (evaluate : Bool) (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env [] (.next evaluate resume) = none := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def]
  rfl

@[simp] theorem Term.evalBody_next_true (ctx : Ctx) (env : Env ctx.primCtx)
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env (term :: terms) (.next true resume) = (do
      let value ← Term.evalGo ctx env term
      Term.evalBody ctx env terms (resume (some value))) := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def, Term.evalGo]
  cases hterm : Term.evalOutcome ctx env term with
  | none => simp [hterm]
  | some outcome => cases outcome <;> simp [hterm, Outcome.ok?, Term.evalBody]

@[simp] theorem Term.evalBody_next_false (ctx : Ctx) (env : Env ctx.primCtx)
    (term : Term ctx.primCtx) (terms : List (Term ctx.primCtx))
    (resume : Option (Val ctx.primCtx) → Op.Body ctx.primCtx) :
    Term.evalBody ctx env (term :: terms) (.next false resume) =
      Term.evalBody ctx env terms (resume none) := by
  rw [Term.evalBody, Term.evalBodyOutcome.eq_def]
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
      | .exit name value => .exit name (Term.subst ctxTerm value)
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

@[simp] theorem Term.subst_exit {primCtx : PrimitiveCtx} (ctxTerm : Scope (Term primCtx))
    (name : String) (value : Term primCtx) :
    Term.subst ctxTerm (.exit name value) = .exit name (Term.subst ctxTerm value) := by
  cases ctxTerm <;> simp [Term.subst]

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
