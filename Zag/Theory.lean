import Zag.Data

/-!
`Zag`'s syntax determines which propositions can be stated (only first order statements about terms and types)
but allows the meta-theory (in this case lean) to determine which of those statements are provable.
Meaning that depending on the consistency strength of the metatheory different programs will provably terminate
(see goodstein sequence).
-/

namespace Zag

namespace Val

def as? {primCtx : PrimitiveCtx} (ty : Ty) (v : Val primCtx) : Option (Ty.type primCtx ty) :=
  if h : v.ty = ty then
    some (cast (congrArg (Ty.type primCtx) h) v.val)
  else none

def nat {primCtx : PrimitiveCtx} (n : Nat) : Val primCtx :=
  .mk (.prim "Nat") (Ty.ofNat primCtx n)

def bool {primCtx : PrimitiveCtx} (b : Bool) : Val primCtx :=
  .mk (.prim "Bool") (Ty.ofBool primCtx b)

def asNat? {primCtx : PrimitiveCtx} (v : Val primCtx) : Option Nat := do
  let raw ← v.as? (.prim "Nat")
  some (Ty.toNat primCtx raw)

def asBool? {primCtx : PrimitiveCtx} (v : Val primCtx) : Option Bool := do
  let raw ← v.as? (.prim "Bool")
  some (Ty.toBool primCtx raw)

@[simp] theorem as?_mk {primCtx : PrimitiveCtx} (ty : Ty) (val : Ty.type primCtx ty) :
    (Val.mk ty val).as? ty = some val := by
  simp [as?]

@[simp] theorem asNat?_nat {primCtx : PrimitiveCtx} (n : Nat) :
    (Val.nat (primCtx := primCtx) n).asNat? = some n := by
  simp [asNat?, nat, Ty.toNat, Ty.ofNat]

@[simp] theorem asBool?_bool {primCtx : PrimitiveCtx} (b : Bool) :
    (Val.bool (primCtx := primCtx) b).asBool? = some b := by
  simp [asBool?, bool, Ty.toBool, Ty.ofBool]

@[simp] theorem as?_nat {primCtx : PrimitiveCtx} (n : Nat) :
    (Val.nat (primCtx := primCtx) n).as? (.prim "Nat") = some (Ty.ofNat primCtx n) := by
  simp [nat]

@[simp] theorem as?_bool {primCtx : PrimitiveCtx} (b : Bool) :
    (Val.bool (primCtx := primCtx) b).as? (.prim "Bool") = some (Ty.ofBool primCtx b) := by
  simp [bool]

@[simp] theorem mk_ofNat {primCtx : PrimitiveCtx} (n : Nat) :
    (Val.mk (.prim "Nat") (Ty.ofNat primCtx n) : Val primCtx) = Val.nat n := rfl

@[simp] theorem mk_ofBool {primCtx : PrimitiveCtx} (b : Bool) :
    (Val.mk (.prim "Bool") (Ty.ofBool primCtx b) : Val primCtx) = Val.bool b := rfl

def primEq? {primCtx : PrimitiveCtx} (lhs rhs : Val primCtx) : Option Bool :=
  match lhs.asNat?, rhs.asNat? with
  | some lhs, some rhs => some (decide (lhs = rhs))
  | _, _ =>
      match lhs.asBool?, rhs.asBool? with
      | some lhs, some rhs => some (decide (lhs = rhs))
      | _, _ => none

def primLt? {primCtx : PrimitiveCtx} (lhs rhs : Val primCtx) : Option Bool :=
  match lhs.asNat?, rhs.asNat? with
  | some lhs, some rhs => some (decide (lhs < rhs))
  | _, _ =>
      match lhs.asBool?, rhs.asBool? with
      | some lhs, some rhs => some (decide (lhs = false ∧ rhs = true))
      | _, _ => none

def primGt? {primCtx : PrimitiveCtx} (lhs rhs : Val primCtx) : Option Bool :=
  Val.primLt? rhs lhs

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

def PrimFunc.apply {primCtx : PrimitiveCtx} (pfunc : PrimFunc primCtx) (vargs : List (Val primCtx)) : Option (Val primCtx) :=
  if vargs.length = pfunc.args.length then do
    let raw ← (← pfunc.interp vargs).as? (.prim pfunc.out)
    some (Val.mk (.prim pfunc.out) raw)
  else none

def PrimFunc.toVal {primCtx : PrimitiveCtx} (pfunc : PrimFunc primCtx) : Val primCtx :=
  Val.mk pfunc.ty
    (cast (Ty.type.eq_6 primCtx (pfunc.args.map (.prim ·)) (.prim pfunc.out)).symm
      (fun args => do
        let argTys := pfunc.args.map (.prim ·)
        let vargs := (List.finRange argTys.length).map fun idx =>
          Val.mk argTys[idx] (args idx)
        let result ← pfunc.apply vargs
        result.as? (.prim pfunc.out)))

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

structure Term.RecCtx (primCtx : PrimitiveCtx) where
  body : Term primCtx
  env : List (Val primCtx)
  stateTy : Ty
  resultTy : Ty

mutual

def Term.evalGo (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx)
    (rec? : Option (Term.RecCtx primCtx)) (env : List (Val primCtx)) : Term primCtx → Option (Val primCtx)
| .prim ty val => some (Val.mk ty val)
| .primFunc name => do
    let pfunc ← primFuncCtx.get? name
    some pfunc.toVal
| .var idx => env[idx]?
| .primEq lhs rhs => do
    let lhsVal ← Term.evalGo primCtx primFuncCtx rec? env lhs
    let rhsVal ← Term.evalGo primCtx primFuncCtx rec? env rhs
    some (Val.bool (← Val.primEq? lhsVal rhsVal))
| .primLt lhs rhs => do
    let lhsVal ← Term.evalGo primCtx primFuncCtx rec? env lhs
    let rhsVal ← Term.evalGo primCtx primFuncCtx rec? env rhs
    some (Val.bool (← Val.primLt? lhsVal rhsVal))
| .primGt lhs rhs => do
    let lhsVal ← Term.evalGo primCtx primFuncCtx rec? env lhs
    let rhsVal ← Term.evalGo primCtx primFuncCtx rec? env rhs
    some (Val.bool (← Val.primGt? lhsVal rhsVal))
| .mkStruct tys =>
    some <| Val.mk (.func tys (.struct tys))
      (cast (Ty.type.eq_6 primCtx tys (.struct tys)).symm
        (fun args => some (cast (Ty.type.eq_5 primCtx tys).symm args)))
| .structProj tys idx =>
    some <| Val.mk (.func [.struct tys] tys[idx])
      (cast (Ty.type.eq_6 primCtx [.struct tys] tys[idx]).symm
        (fun args => some ((cast (Ty.type.eq_5 primCtx tys) (args 0)) idx)))
| .ite cond thenTerm elseTerm => do
    let v ← Term.evalGo primCtx primFuncCtx rec? env cond
    match v.asBool? with
    | some true => Term.evalGo primCtx primFuncCtx rec? env thenTerm
    | some false => Term.evalGo primCtx primFuncCtx rec? env elseTerm
    | none => none
| .app (.primFunc name) args => do
    let pfunc ← primFuncCtx.get? name
    let vargs ← Term.evalList primCtx primFuncCtx rec? env args
    PrimFunc.apply pfunc vargs
| .app (.mkStruct tys) args => do
    let vargs ← Term.evalList primCtx primFuncCtx rec? env args
    Term.evalMkStruct tys vargs
| .app (.structProj tys idx) [arg] => do
    let value ← Term.evalGo primCtx primFuncCtx rec? env arg
    let fields ← value.as? (.struct tys)
    some (Val.mk tys[idx] ((cast (Ty.type.eq_5 primCtx tys) fields) idx))
-- TODO :: suppoort arbitrary recursion not just one recursor/motive at a time
-- for example if with have break_outer the inner loop body needs to be able to call the outer motive
| .app (.var idx) [arg] =>
    match rec? with
    | some rec =>
        if idx = rec.env.length + 1 then do
          let state ← Term.evalGo primCtx primFuncCtx rec? env arg
          let stateRaw ← state.as? rec.stateTy
          let stateVal := Val.mk rec.stateTy stateRaw
          let motiveVal := Term.motiveVal rec.stateTy rec.resultTy
          let result ← Term.evalGo primCtx primFuncCtx rec? (rec.env ++ [stateVal, motiveVal]) rec.body
          let resultRaw ← result.as? rec.resultTy
          some (Val.mk rec.resultTy resultRaw)
        else do
          let vf ← Term.evalGo primCtx primFuncCtx rec? env (.var idx)
          let varg ← Term.evalGo primCtx primFuncCtx rec? env arg
          Term.evalApp vf [varg]
    | none => do
        let vf ← Term.evalGo primCtx primFuncCtx rec? env (.var idx)
        let varg ← Term.evalGo primCtx primFuncCtx rec? env arg
        Term.evalApp vf [varg]
| .app f args => do
    let vf ← Term.evalGo primCtx primFuncCtx rec? env f
    let vargs ← Term.evalList primCtx primFuncCtx rec? env args
    Term.evalApp vf vargs
| .recurse resultTy init body => do
    let v ← Term.evalGo primCtx primFuncCtx rec? env init
    let motiveVal := Term.motiveVal v.ty resultTy
    let recCtx : Term.RecCtx primCtx :=
      { body := body, env := env, stateTy := v.ty, resultTy := resultTy }
    Term.evalGo primCtx primFuncCtx (some recCtx) (env ++ [v, motiveVal]) body
partial_fixpoint

def Term.evalList (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx)
    (rec? : Option (Term.RecCtx primCtx)) (env : List (Val primCtx))
    (terms : List (Term primCtx)) : Option (List (Val primCtx)) :=
  terms.mapM (Term.evalGo primCtx primFuncCtx rec? env)
partial_fixpoint

end

def Term.eval (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx)
    (env : List (Val primCtx)) (term : Term primCtx) : Option (Val primCtx) :=
  Term.evalGo primCtx primFuncCtx none env term

/- Termination of a partial `Option` evaluator is successful evaluation. -/
def Term.Terminates (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx)
    (env : List (Val primCtx)) (term : Term primCtx) : Prop :=
  ∃ v, Term.eval primCtx primFuncCtx env term = some v

structure Term.eq (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx) (varCtx : VarCtx) (ty : Ty) (t₁ t₂ : Term primCtx) : Prop where
  hasType₁ : hasType primCtx primFuncCtx varCtx t₁ ty
  hasType₂ : hasType primCtx primFuncCtx varCtx t₂ ty
  eq : ∀ env : List (Val primCtx), env.length = varCtx.length →
    t₁.eval primCtx primFuncCtx env = t₂.eval primCtx primFuncCtx env

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
      | .primEq lhs rhs => .primEq (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs)
      | .primLt lhs rhs => .primLt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs)
      | .primGt lhs rhs => .primGt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs)
      | .app f args => .app (Term.subst ctxTerm f) (args.map (Term.subst ctxTerm))
      | .mkStruct tys => .mkStruct tys
      | .structProj tys idx => .structProj tys idx
      | .ite cond thenTerm elseTerm =>
          .ite (Term.subst ctxTerm cond) (Term.subst ctxTerm thenTerm) (Term.subst ctxTerm elseTerm)
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

@[simp] theorem Term.subst_primEq {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (lhs rhs : Term primCtx) :
    Term.subst ctxTerm (.primEq lhs rhs) = .primEq (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs) := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_primLt {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (lhs rhs : Term primCtx) :
    Term.subst ctxTerm (.primLt lhs rhs) = .primLt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs) := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_primGt {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (lhs rhs : Term primCtx) :
    Term.subst ctxTerm (.primGt lhs rhs) = .primGt (Term.subst ctxTerm lhs) (Term.subst ctxTerm rhs) := by
  cases ctxTerm <;> simp [Term.subst]

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

@[simp] theorem Term.subst_ite {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (cond thenTerm elseTerm : Term primCtx) :
    Term.subst ctxTerm (.ite cond thenTerm elseTerm) =
      .ite (Term.subst ctxTerm cond) (Term.subst ctxTerm thenTerm) (Term.subst ctxTerm elseTerm) := by
  cases ctxTerm <;> simp [Term.subst]

@[simp] theorem Term.subst_recurse {primCtx : PrimitiveCtx} (ctxTerm : List (Term primCtx))
    (resultTy : Ty) (init body : Term primCtx) :
    Term.subst ctxTerm (.recurse resultTy init body) =
      .recurse resultTy (Term.subst ctxTerm init) (Term.subst ctxTerm body) := by
  cases ctxTerm <;> simp [Term.subst]

/- Zag propositions can only be assigned semantics under a fixed `PrimitiveCtxF` -/
def Pr.interp (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx) :
    (ctxTy : List Ty) → (ctxTerm : List (Term primCtx)) → Pr primCtx → Prop
| ctxTy, ctxTerm, .eq ctx ty x y =>
  Term.eq primCtx primFuncCtx (ctx.map (Ty.subst ctxTy)) (Ty.subst ctxTy ty) (Term.subst ctxTerm x) (Term.subst ctxTerm y)
| ctxTy, ctxTerm, .hasType ctx t ty =>
  Term.hasType primCtx primFuncCtx (ctx.map (Ty.subst ctxTy)) (Term.subst ctxTerm t) (Ty.subst ctxTy ty)
| ctxTy, ctxTerm, .and p q =>
  Pr.interp primCtx primFuncCtx ctxTy ctxTerm p ∧ Pr.interp primCtx primFuncCtx ctxTy ctxTerm q
| ctxTy, ctxTerm, .or p q =>
  Pr.interp primCtx primFuncCtx ctxTy ctxTerm p ∨ Pr.interp primCtx primFuncCtx ctxTy ctxTerm q
| ctxTy, ctxTerm, .implies p q =>
  Pr.interp primCtx primFuncCtx ctxTy ctxTerm p → Pr.interp primCtx primFuncCtx ctxTy ctxTerm q
| ctxTy, ctxTerm, .forallTy p =>
  ∀ (α : Ty), Pr.interp primCtx primFuncCtx (ctxTy ++ [α]) ctxTerm p
| ctxTy, ctxTerm, .forallTerm p =>
  ∀ (x : Term primCtx), Pr.interp primCtx primFuncCtx ctxTy (ctxTerm ++ [x]) p

/- metatheory (in this case lean) determines which Zag propositions are provable -/
inductive Pr.Provable (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx)
    (ctxTy : List Ty) (ctxTerm : List (Term primCtx)) (p : Pr primCtx) : Prop
| ofProof (proof : Pr.interp primCtx primFuncCtx ctxTy ctxTerm p)
