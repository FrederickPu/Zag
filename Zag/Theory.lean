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

namespace Op

/- binary comparison operator built from a raw `Val` comparator: defined on two operands of the
  same type, always yielding `Bool`. `eq` is built from this; `lt`/`gt` implementations
  (e.g. in a Peano library) are too. -/
def compare {primCtx : PrimitiveCtx} (cmp : Val primCtx → Val primCtx → Option Bool) : Op primCtx where
  arity := 2
  out tys := if tys 0 = tys 1 then some (.prim "Bool") else none
  interp {_tys _r} _hout vals :=
    match vals with
    | [lhs, rhs] => do
        let b ← cmp lhs rhs
        (Val.bool b).as? _r
    | _ => none

/- the built-in equality operator; pinned to `Val.primEq?` -/
def eq {primCtx : PrimitiveCtx} : Op primCtx := compare Val.primEq?

end Op

/- Look up the operator named `name`: `eq` is built in (like `Nat`/`Bool` in `PrimitiveCtx.get?`),
  every other operator — including `lt`/`gt` — must be supplied by the context. -/
def OpCtx.get? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx) (name : String) : Option (Op primCtx) :=
  if name = "eq" then some Op.eq
  else (opCtx.find? (·.1 = name)).map (·.2)

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
    let vargs ← Term.evalList ctx motives env args
    oper.applyVals vargs
| .mkStruct tys =>
    some <| Val.mk (.func tys (.struct tys))
      (cast (Ty.type.eq_6 ctx.primCtx tys (.struct tys)).symm
        (fun args => some (cast (Ty.type.eq_5 ctx.primCtx tys).symm args)))
| .structProj tys idx =>
    some <| Val.mk (.func [.struct tys] tys[idx])
      (cast (Ty.type.eq_6 ctx.primCtx [.struct tys] tys[idx]).symm
        (fun args => some ((cast (Ty.type.eq_5 ctx.primCtx tys) (args 0)) idx)))
| .ite cond thenTerm elseTerm => do
    let v ← Term.evalGo ctx motives env cond
    match v.asBool? with
    | some true => Term.evalGo ctx motives env thenTerm
    | some false => Term.evalGo ctx motives env elseTerm
    | none => none
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

end

def Term.eval (ctx : Ctx)
    (env : List (Val ctx.primCtx)) (term : Term ctx.primCtx) : Option (Val ctx.primCtx) :=
  Term.evalGo ctx [] env term

/- Evaluating a comparison operator built by `Op.compare` on two values of equal type. -/
theorem Op.applyVals_compare {primCtx : PrimitiveCtx}
    (cmp : Val primCtx → Val primCtx → Option Bool)
    (va vb : Val primCtx) (hty : va.ty = vb.ty) :
    Op.applyVals (Op.compare cmp) [va, vb] = (cmp va vb).map Val.bool := by
  dsimp [Op.applyVals, Op.compare]
  rw [if_pos hty]
  cases cmp va vb with
  | none => rfl
  | some c => rfl

theorem Term.evalGo_op_compare {ctx : Ctx}
    {motives : List (Term.MotiveCtx ctx.primCtx)} {env : List (Val ctx.primCtx)}
    {name : String} {a b : Term ctx.primCtx}
    {cmp : Val ctx.primCtx → Val ctx.primCtx → Option Bool}
    {va vb : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.compare cmp))
    (ha : Term.evalGo ctx motives env a = some va)
    (hb : Term.evalGo ctx motives env b = some vb)
    (hty : va.ty = vb.ty) :
    Term.evalGo ctx motives env (.op name [a, b]) = (cmp va vb).map Val.bool := by
  have hform :
      Term.evalGo ctx motives env (.op name [a, b]) =
        Op.applyVals (Op.compare cmp) [va, vb] := by
    simp [Term.evalGo, hop, Term.evalList, ha, hb]
  rw [hform, Op.applyVals_compare cmp va vb hty]

/- Termination of a partial `Option` evaluator is successful evaluation. -/
def Term.Terminates (ctx : Ctx)
    (env : List (Val ctx.primCtx)) (term : Term ctx.primCtx) : Prop :=
  ∃ v, Term.eval ctx env term = some v

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
