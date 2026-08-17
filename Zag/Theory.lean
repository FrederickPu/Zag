import Zag.Data

/-!
`Zag`'s syntax determines which propositions can be stated (only first order statements about terms and types)
but allows the meta-theory (in this case lean) to determine which of those statements are provable.
Meaning that depending on the consistency strength of the metatheory different programs will
provably terminate (see goodstein sequence). Evaluation itself lives in `Zag.EvalState` as a
fuelled small-step machine.
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

/- Apply a *primitive* function value. A block reference declines here: running a block needs the
  machine, so `EvalState.step` intercepts it before this is reached. -/
def Term.evalApp {primCtx : PrimitiveCtx} (fn : Val primCtx) (args : List (Val primCtx)) :
    Option (Val primCtx) :=
  match fn with
  | .blockRef .. => none
  | .mk fnTy fnVal =>
      match fnTy, fnVal with
      | .func argsTy outTy, fnVal => do
          -- the match has already refined `fnVal`'s type; only `Ty.type`'s own equation is left
          let typedArgs ← valsAs? argsTy args
          let f := cast (Ty.type_func primCtx argsTy outTy) fnVal
          let result ← f typedArgs
          some (Val.mk outTy result)
      | _, _ => none

/- the environment a block is entered with: each parameter name bound to its argument -/
def Block.entryEnv {primCtx : PrimitiveCtx} (block : Block primCtx)
    (vargs : List (Val primCtx)) : Env primCtx :=
  (block.params.map Prod.fst).zip vargs

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

end Zag
