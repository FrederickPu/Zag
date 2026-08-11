/-!
All objects are either a type: `Zag.Ty`
Or a term: `Zag.Term`

All functions are `Zag.Term × ... × Zag.Term → Zag.Term`
or `Zag.Ty × ... × Zag.Ty → Zag.Ty`

Typing is a predicate. Evaluation is partial and returns `Option`; termination is expressed by
successful evaluation, i.e. `∃ v, eval ... = some v`.
-/

namespace Zag

inductive Ty where
/- debrujin index of variable -/
| var : Nat → Ty
/- primitive types such as "int", "nat", "bool" -/
| prim : String → Ty
| option : Ty → Ty
| union : List Ty → Ty
| struct : List Ty → Ty
| func : List Ty → Ty → Ty
| m : Ty → Ty
/- application of a transparent, named type abbreviation -/
| «abbrev» : String → List Ty → Ty
deriving Repr

mutual

def Ty.decEq : (a b : Ty) → Decidable (a = b)
| .var a, .var b =>
    if h : a = b then isTrue (by rw [h])
    else isFalse (fun hc => h (by injection hc))
| .prim a, .prim b =>
    if h : a = b then isTrue (by rw [h])
    else isFalse (fun hc => h (by injection hc))
| .option a, .option b =>
    match Ty.decEq a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hc => h (by injection hc))
| .union as, .union bs =>
    match Ty.decEqList as bs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hc => h (by injection hc))
| .struct as, .struct bs =>
    match Ty.decEqList as bs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hc => h (by injection hc))
| .func as a, .func bs b =>
    match Ty.decEqList as bs, Ty.decEq a b with
    | isTrue hs, isTrue h => isTrue (by rw [hs, h])
    | isFalse hs, _ => isFalse (fun hc => hs (by injection hc))
    | _, isFalse h => isFalse (fun hc => h (by injection hc))
| .m a, .m b =>
    match Ty.decEq a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hc => h (by injection hc))
| .«abbrev» a as, .«abbrev» b bs =>
    match String.decEq a b, Ty.decEqList as bs with
    | isTrue hn, isTrue hs => isTrue (by rw [hn, hs])
    | isFalse hn, _ => isFalse (fun hc => hn (by injection hc))
    | _, isFalse hs => isFalse (fun hc => hs (by injection hc))
| .var _, .prim _ => isFalse nofun
| .var _, .option _ => isFalse nofun
| .var _, .union _ => isFalse nofun
| .var _, .struct _ => isFalse nofun
| .var _, .func _ _ => isFalse nofun
| .prim _, .var _ => isFalse nofun
| .prim _, .option _ => isFalse nofun
| .prim _, .union _ => isFalse nofun
| .prim _, .struct _ => isFalse nofun
| .prim _, .func _ _ => isFalse nofun
| .option _, .var _ => isFalse nofun
| .option _, .prim _ => isFalse nofun
| .option _, .union _ => isFalse nofun
| .option _, .struct _ => isFalse nofun
| .option _, .func _ _ => isFalse nofun
| .union _, .var _ => isFalse nofun
| .union _, .prim _ => isFalse nofun
| .union _, .option _ => isFalse nofun
| .union _, .struct _ => isFalse nofun
| .union _, .func _ _ => isFalse nofun
| .struct _, .var _ => isFalse nofun
| .struct _, .prim _ => isFalse nofun
| .struct _, .option _ => isFalse nofun
| .struct _, .union _ => isFalse nofun
| .struct _, .func _ _ => isFalse nofun
| .func _ _, .var _ => isFalse nofun
| .func _ _, .prim _ => isFalse nofun
| .func _ _, .option _ => isFalse nofun
| .func _ _, .union _ => isFalse nofun
| .func _ _, .struct _ => isFalse nofun
| .var _, .m _ => isFalse nofun
| .prim _, .m _ => isFalse nofun
| .option _, .m _ => isFalse nofun
| .union _, .m _ => isFalse nofun
| .struct _, .m _ => isFalse nofun
| .func _ _, .m _ => isFalse nofun
| .m _, .var _ => isFalse nofun
| .m _, .prim _ => isFalse nofun
| .m _, .option _ => isFalse nofun
| .m _, .union _ => isFalse nofun
| .m _, .struct _ => isFalse nofun
| .m _, .func _ _ => isFalse nofun
| .var _, .«abbrev» _ _ => isFalse nofun
| .prim _, .«abbrev» _ _ => isFalse nofun
| .option _, .«abbrev» _ _ => isFalse nofun
| .union _, .«abbrev» _ _ => isFalse nofun
| .struct _, .«abbrev» _ _ => isFalse nofun
| .func _ _, .«abbrev» _ _ => isFalse nofun
| .m _, .«abbrev» _ _ => isFalse nofun
| .«abbrev» _ _, .var _ => isFalse nofun
| .«abbrev» _ _, .prim _ => isFalse nofun
| .«abbrev» _ _, .option _ => isFalse nofun
| .«abbrev» _ _, .union _ => isFalse nofun
| .«abbrev» _ _, .struct _ => isFalse nofun
| .«abbrev» _ _, .func _ _ => isFalse nofun
| .«abbrev» _ _, .m _ => isFalse nofun

def Ty.decEqList : (as bs : List Ty) → Decidable (as = bs)
| [], [] => isTrue rfl
| [], _ :: _ => isFalse nofun
| _ :: _, [] => isFalse nofun
| a :: as, b :: bs =>
    match Ty.decEq a b, Ty.decEqList as bs with
    | isTrue h, isTrue hs => isTrue (by rw [h, hs])
    | isFalse h, _ => isFalse (fun hc => h (by injection hc))
    | _, isFalse hs => isFalse (fun hc => hs (by injection hc))

end

instance : DecidableEq Ty := Ty.decEq

/- A type abbreviation body may refer to generic arguments with `Ty.var`. -/
structure TypeAbbrev where
  /- number of generic type arguments accepted by the abbreviation -/
  typeArity : Nat
  body : Ty
deriving Repr, DecidableEq

namespace TypeAbbrevCtx

abbrev Raw := List (String × TypeAbbrev)

def Raw.get? (ctx : Raw) (name : String) : Option TypeAbbrev :=
  (ctx.find? (·.1 = name)).map (·.2)

def Raw.getWithPrefix? : Raw → String → Option (Raw × TypeAbbrev)
| [], _ => none
| entry :: rest, name =>
    if entry.1 = name then
      some ([], entry.2)
    else
      match Raw.getWithPrefix? rest name with
      | some (prior, definition) => some (entry :: prior, definition)
      | none => none

theorem Raw.getWithPrefix?_prefix_lt
    {ctx prior : Raw} {name : String} {definition : TypeAbbrev}
    (h : ctx.getWithPrefix? name = some (prior, definition)) :
    prior.length < ctx.length := by
  induction ctx generalizing prior definition with
  | nil => simp [Raw.getWithPrefix?] at h
  | cons entry rest ih =>
      simp only [Raw.getWithPrefix?] at h
      split at h
      · simp_all
      · split at h
        · next prefix' definition' heq =>
            cases h
            simp only [List.length_cons, Nat.add_lt_add_iff_right]
            exact ih heq
        · simp_all

end TypeAbbrevCtx

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
| .«abbrev» name args => .«abbrev» name (args.map (Ty.subst ctxTy))

mutual

def Ty.validIn (ctx : TypeAbbrevCtx.Raw) (typeArity : Nat) : Ty → Bool
| .var idx => decide (idx < typeArity)
| .prim _ => true
| .option ty => validIn ctx typeArity ty
| .union tys => validListIn ctx typeArity tys
| .struct tys => validListIn ctx typeArity tys
| .func args out => validListIn ctx typeArity args && validIn ctx typeArity out
| .m ty => validIn ctx typeArity ty
| .«abbrev» name args =>
    match ctx.get? name with
    | some definition =>
        decide (args.length = definition.typeArity) && validListIn ctx typeArity args
    | none => false

def Ty.validListIn (ctx : TypeAbbrevCtx.Raw) (typeArity : Nat) : List Ty → Bool
| [] => true
| ty :: tys => validIn ctx typeArity ty && validListIn ctx typeArity tys

end

def TypeAbbrevCtx.validFrom (previous : TypeAbbrevCtx.Raw) : TypeAbbrevCtx.Raw → Bool
| [] => true
| entry :: rest =>
    Ty.validIn previous entry.2.typeArity entry.2.body &&
      validFrom (previous ++ [entry]) rest

/- Every definition references only earlier definitions and uses its generic arguments in range. -/
def TypeAbbrevCtx.Valid (ctx : TypeAbbrevCtx.Raw) : Prop :=
  (ctx.map Prod.fst).Nodup ∧ TypeAbbrevCtx.validFrom [] ctx = true

instance (ctx : TypeAbbrevCtx.Raw) : Decidable (TypeAbbrevCtx.Valid ctx) := by
  unfold TypeAbbrevCtx.Valid
  infer_instance

structure TypeAbbrevCtx where
  val : TypeAbbrevCtx.Raw
  isValid : TypeAbbrevCtx.Valid val

namespace TypeAbbrevCtx

instance : Coe TypeAbbrevCtx TypeAbbrevCtx.Raw := ⟨TypeAbbrevCtx.val⟩

def empty : TypeAbbrevCtx := ⟨[], by decide⟩

def get? (ctx : TypeAbbrevCtx) (name : String) : Option TypeAbbrev := ctx.val.get? name

def ofRaw? (raw : Raw) : Option TypeAbbrevCtx :=
  if h : Valid raw then some ⟨raw, h⟩ else none

end TypeAbbrevCtx

def Ty.normalizeWith (ctx : TypeAbbrevCtx.Raw) (env : List Ty) (ty : Ty) : Ty :=
  match ty with
  | .var idx =>
      if idx < env.length then (env[idx]?).getD (.var idx) else .var (idx - env.length)
  | .prim name => .prim name
  | .option element => .option (normalizeWith ctx env element)
  | .union alternatives => .union (alternatives.map (normalizeWith ctx env))
  | .struct fields => .struct (fields.map (normalizeWith ctx env))
  | .func args out =>
      .func (args.map (normalizeWith ctx env)) (normalizeWith ctx env out)
  | .m result => .m (normalizeWith ctx env result)
  | .«abbrev» name args =>
      let args := args.map (normalizeWith ctx env)
      match _hget : TypeAbbrevCtx.Raw.getWithPrefix? ctx name with
      | some (prior, definition) =>
          if args.length = definition.typeArity then
            normalizeWith prior args definition.body
          else
            .«abbrev» name args
      | none => .«abbrev» name args
termination_by (ctx.length, sizeOf ty)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left
      exact TypeAbbrevCtx.Raw.getWithPrefix?_prefix_lt _hget
    | apply Prod.Lex.right
      simp only [Ty.option.sizeOf_spec, Ty.union.sizeOf_spec, Ty.struct.sizeOf_spec,
        Ty.func.sizeOf_spec, Ty.m.sizeOf_spec, Ty.«abbrev».sizeOf_spec]
      first
      | omega
      | (have := List.sizeOf_lt_of_mem (by assumption); omega)

/- Fully expand type abbreviations using their ordered, nonrecursive declarations. -/
def Ty.normalizeAbbrev (ctx : TypeAbbrevCtx) (ty : Ty) : Ty :=
  Ty.normalizeWith ctx.val [] ty

def Ty.deltaEq (ctx : TypeAbbrevCtx) (left right : Ty) : Bool :=
  left.normalizeAbbrev ctx == right.normalizeAbbrev ctx

def Ty.deltaEqList (ctx : TypeAbbrevCtx) (left right : List Ty) : Bool :=
  left.map (Ty.normalizeAbbrev ctx) == right.map (Ty.normalizeAbbrev ctx)

structure Primitive where
  name : String
  type : Type
  repr : Repr type

abbrev Primitive.of (name : String) (type : Type) [Repr type] : Primitive where
  name := name
  type := type
  repr := inferInstance

def Primitive.reprValue (primitive : Primitive) (value : primitive.type) : String :=
  letI := primitive.repr
  reprStr value

/- primitive types and the monad used to interpret `Ty.m` -/
structure PrimitiveCtx where
  prims : List Primitive
  M : Type → Type
  monad : Monad M

class PrimitiveCtx.ReprName (primCtx : PrimitiveCtx) where
  expr : String

attribute [instance] PrimitiveCtx.monad

/- primitive context where `m(T)` is `Option T` -/
abbrev PrimitiveCtx.ofPrims (prims : List Primitive) : PrimitiveCtx where
  prims := prims
  M := Id
  monad := inferInstance

abbrev PrimitiveCtx.get? (primCtx : PrimitiveCtx) (primName : String) : Option Type :=
  (primCtx.prims.find? (·.name = primName)).map (·.type)

def PrimitiveCtx.reprPrimitive? (primCtx : PrimitiveCtx) (primName : String)
    (value : (primCtx.get? primName).getD Empty) : Option String :=
  match h : primCtx.prims.find? (·.name = primName) with
  | none => none
  | some primitive =>
      have htype : primCtx.get? primName = some primitive.type := by
        simp [PrimitiveCtx.get?, h]
      some (primitive.reprValue (cast (by simp [htype]) value))

/- variable context `varCtx : VarCtx` then `varCtx[i]` is the type of the `i`th variable in the context -/
abbrev VarCtx := List Ty

def Ty.type (primCtx : PrimitiveCtx) : Ty → Type
| var idx => Empty -- should be unreachable
| prim b => (primCtx.get? b).getD Empty
| option t => Option (t.type primCtx)
| union tys => Σ idx : Fin tys.length, (tys[idx].type primCtx)
| struct tys => ∀ idx : Fin tys.length, (tys[idx].type primCtx)
| func argsTy outTy =>
    ((idx : Fin argsTy.length) → (argsTy[idx].type primCtx)) → Option (outTy.type primCtx)
/- suspended computation which may get stuck after performing effects -/
| m t => primCtx.M (Option (t.type primCtx))
| «abbrev» _ _ => Empty
termination_by ty => ty
decreasing_by
  all_goals
    simp only [Fin.getElem_fin, Ty.option.sizeOf_spec, Ty.union.sizeOf_spec,
               Ty.struct.sizeOf_spec, Ty.func.sizeOf_spec, Ty.m.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt); omega)

def PrimitiveCtx.toPrimitiveValue (primCtx : PrimitiveCtx) (primName : String)
    {type : Type} (value : type) (h : primCtx.get? primName = some type) :
    Ty.type primCtx (.prim primName) :=
  cast (by
    rw [Ty.type.eq_2, h]
    rfl) value

namespace Ty

def ofM (primCtx : PrimitiveCtx) (t : Ty) :
    primCtx.M (Option (t.type primCtx)) → Ty.type primCtx (.m t) :=
  cast (Ty.type.eq_7 primCtx t).symm

def toM (primCtx : PrimitiveCtx) (t : Ty) :
    Ty.type primCtx (.m t) → primCtx.M (Option (t.type primCtx)) :=
  cast (Ty.type.eq_7 primCtx t)

@[simp] theorem toM_ofM (primCtx : PrimitiveCtx) (t : Ty)
    (value : primCtx.M (Option (t.type primCtx))) :
    toM primCtx t (ofM primCtx t value) = value := by
  simp [toM, ofM]

@[simp] theorem ofM_toM (primCtx : PrimitiveCtx) (t : Ty)
    (value : Ty.type primCtx (.m t)) :
    ofM primCtx t (toM primCtx t value) = value := by
  simp [toM, ofM]

def applyUnary? (primCtx : PrimitiveCtx) (inputTy outputTy : Ty)
    (fn : Ty.type primCtx (.func [inputTy] outputTy))
    (input : Ty.type primCtx inputTy) : Option (Ty.type primCtx outputTy) :=
  let fn' := cast (Ty.type.eq_6 primCtx [inputTy] outputTy) fn
  fn' (fun idx => cast (congrArg (Ty.type primCtx) (by simp)) input)

end Ty

structure Val (primCtx : PrimitiveCtx) where
  ty : Ty
  val : Ty.type primCtx ty

def Val.as? {primCtx : PrimitiveCtx} (ty : Ty) (v : Val primCtx) : Option (Ty.type primCtx ty) :=
  if h : v.ty = ty then
    some (cast (congrArg (Ty.type primCtx) h) v.val)
  else none

/- lazy left-to-right operator program -/
inductive Op.Body (primCtx : PrimitiveCtx) where
| fail
| done (value : Val primCtx)
| next (evaluate : Bool) (resume : Option (Val primCtx) → Op.Body primCtx)

structure Op (primCtx : PrimitiveCtx) where
  arity : Nat
  out : (Fin arity → Ty) → Option Ty
  body : Op.Body primCtx

/- type shape and semantics of an operator -/
structure Op.Signature (primCtx : PrimitiveCtx) (arity : Nat) where
  Shape : Type
  inputs : Shape → Fin arity → Ty
  output : Shape → Ty
  decode : (Fin arity → Ty) → Option Shape
  decode_inputs : ∀ {tys shape}, decode tys = some shape → inputs shape = tys
  run : (shape : Shape) →
    ((idx : Fin arity) → Ty.type primCtx (inputs shape idx)) → Ty.type primCtx (output shape)

namespace Op.Signature

def apply {primCtx : PrimitiveCtx} {arity : Nat} (sig : Signature primCtx arity)
    (vals : List (Val primCtx)) : Option (Val primCtx) :=
  if h : vals.length = arity then
    let getVal (idx : Fin arity) := vals.get ⟨idx.val, by rw [h]; exact idx.isLt⟩
    let tys : Fin arity → Ty := fun idx => (getVal idx).ty
    match hdecode : sig.decode tys with
    | none => none
    | some shape =>
        have hinputs := sig.decode_inputs hdecode
        some (Val.mk (sig.output shape) (sig.run shape fun idx =>
          cast (congrArg (Ty.type primCtx) (congrFun hinputs idx).symm) (getVal idx).val))
  else none

def eagerBody {primCtx : PrimitiveCtx} {arity : Nat} (sig : Signature primCtx arity) :
    Nat → List (Val primCtx) → Op.Body primCtx
| 0, vals =>
    match sig.apply vals with
    | some value => .done value
    | none => .fail
| remaining + 1, vals => .next true fun
    | some value => eagerBody sig remaining (vals ++ [value])
    | none => .fail

@[simp] def toOp {primCtx : PrimitiveCtx} {arity : Nat} (sig : Signature primCtx arity) : Op primCtx where
  arity := arity
  out tys := (sig.decode tys).map sig.output
  body := eagerBody sig arity []

@[simp] def unary {primCtx : PrimitiveCtx} (output : Ty → Ty)
    (run : (input : Ty) → Ty.type primCtx input → Ty.type primCtx (output input)) :
    Signature primCtx 1 where
  Shape := Ty
  inputs input _ := input
  output := output
  decode tys := some (tys 0)
  decode_inputs := by
    intro tys input hdecode
    simp only [Option.some.injEq] at hdecode
    subst input
    funext idx
    exact congrArg tys (Subsingleton.elim 0 idx)
  run input args := run input (args 0)

@[simp] def binary {primCtx : PrimitiveCtx} {shape : Type} (input₀ input₁ output : shape → Ty)
    (decode : (a b : Ty) → Option {s : shape // input₀ s = a ∧ input₁ s = b})
    (run : (s : shape) → Ty.type primCtx (input₀ s) → Ty.type primCtx (input₁ s) →
      Ty.type primCtx (output s)) : Signature primCtx 2 where
  Shape := shape
  inputs s := @Fin.cases 1 (fun _ => Ty) (input₀ s) (fun _ => input₁ s)
  output := output
  decode tys := (decode (tys 0) (tys 1)).map Subtype.val
  decode_inputs := by
    intro tys s hdecode
    simp only [Option.map_eq_some_iff] at hdecode
    obtain ⟨decoded, hdecoded, rfl⟩ := hdecode
    funext idx
    cases idx using Fin.cases with
    | zero => exact decoded.property.1
    | succ idx =>
        have : idx = 0 := Subsingleton.elim _ _
        subst idx
        exact decoded.property.2
  run s args := run s (args ⟨0, Nat.zero_lt_succ 1⟩) (args ⟨1, by decide⟩)

@[simp] def ternary {primCtx : PrimitiveCtx} {shape : Type}
    (input₀ input₁ input₂ output : shape → Ty)
    (decode : (a b c : Ty) →
      Option {s : shape // input₀ s = a ∧ input₁ s = b ∧ input₂ s = c})
    (run : (s : shape) → Ty.type primCtx (input₀ s) → Ty.type primCtx (input₁ s) →
      Ty.type primCtx (input₂ s) → Ty.type primCtx (output s)) : Signature primCtx 3 where
  Shape := shape
  inputs s := @Fin.cases 2 (fun _ => Ty) (input₀ s)
    (@Fin.cases 1 (fun _ => Ty) (input₁ s) (fun _ => input₂ s))
  output := output
  decode tys := (decode (tys 0) (tys 1) (tys 2)).map Subtype.val
  decode_inputs := by
    intro tys s hdecode
    simp only [Option.map_eq_some_iff] at hdecode
    obtain ⟨decoded, hdecoded, rfl⟩ := hdecode
    funext idx
    cases idx using Fin.cases with
    | zero => exact decoded.property.1
    | succ idx =>
        cases idx using Fin.cases with
        | zero => exact decoded.property.2.1
        | succ idx =>
            have : idx = 0 := Subsingleton.elim _ _
            subst idx
            exact decoded.property.2.2
  run s args := run s (args 0) (args 1) (args 2)

end Op.Signature

namespace Op

def pure {primCtx : PrimitiveCtx} : Op primCtx :=
  (Signature.unary .m fun ty value => Ty.ofM primCtx ty (Pure.pure (some value))).toOp

@[simp] private def bindShape? (a b : Ty) :
    Option {s : Ty × Ty // .m s.1 = a ∧ .func [s.1] (.m s.2) = b} :=
  match a, b with
  | .m input, .func [arg] (.m result) =>
      if h : input = arg then some ⟨(input, result), rfl, by simp [h]⟩ else none
  | _, _ => none

def bind {primCtx : PrimitiveCtx} : Op primCtx :=
  (Signature.binary (shape := Ty × Ty) (fun s => .m s.1)
    (fun s => .func [s.1] (.m s.2)) (fun s => .m s.2)
    bindShape? fun (inputTy, resultTy) computation continuation =>
      Ty.ofM primCtx resultTy do
        let input? ← Ty.toM primCtx inputTy computation
        match input? with
        | none => Pure.pure none
        | some input =>
            match Ty.applyUnary? primCtx inputTy (.m resultTy) continuation input with
            | none => Pure.pure none
            | some next => Ty.toM primCtx resultTy next).toOp

end Op

/- operator context: named operators, looked up the way `PrimFuncCtx` looks up functions -/
abbrev OpCtx (primCtx : PrimitiveCtx) := List (String × Op primCtx)

/- look up the operator named `name` -/
def OpCtx.get? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx) (name : String) : Option (Op primCtx) :=
  if name = "pure" then some Op.pure
  else if name = "bind" then some Op.bind
  else (opCtx.find? (·.1 = name)).map (·.2)

def Op.pureOut? : List Ty → Option Ty
| [ty] => some (.m ty)
| _ => none

def Op.bindOut? : List Ty → Option Ty
| [.m inputTy, .func [argTy] (.m resultTy)] =>
    if inputTy = argTy then some (.m resultTy) else none
| _ => none

/- infer an operator's output type -/
def OpCtx.outTy? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx)
    (name : String) (tys : List Ty) : Option Ty :=
  match opCtx.get? name with
  | some op =>
      if h : tys.length = op.arity then
        let f : Fin op.arity → Ty := fun i => tys.get (i.cast h.symm)
        op.out f
      else none
  | none => none

inductive Term (primCtx : PrimitiveCtx) where
/- primitive value tagged with its Zag type -/
| prim (ty : Ty) : Ty.type primCtx ty → Term primCtx
/- primitive function -/
| primFunc : String → Term primCtx
/- debrujin index of variable -/
| var : Nat → Term primCtx
| app : Term primCtx → List (Term primCtx) → Term primCtx
/- application of a named n-ary operator -/
| op : String → List (Term primCtx) → Term primCtx
/- saturated application of a transparent, named term abbreviation -/
| «abbrev» : String → List Ty → List (Term primCtx) → Term primCtx
/- struct constructor function for a concrete list of field types -/
| mkStruct : List Ty → Term primCtx
/- field projection function for a concrete struct type -/
| structProj : (tys : List Ty) → Fin tys.length → Term primCtx
| recurse
  /- `resultTy : Ty` -/
  (resultTy : Ty)
  /- `initState : stateTy` -/
  (initState : Term primCtx)
  /- `body : stateTy → (motive : stateTy → resultTy) → resultTy` -/
  (body : Term primCtx) : Term primCtx

namespace Term

mutual

private def reprString {primCtx : PrimitiveCtx} [PrimitiveCtx.ReprName primCtx] : Term primCtx → String
| .prim (.prim name) value =>
    let value := cast (by rw [Ty.type.eq_2]) value
    match primCtx.reprPrimitive? name value with
    | some rendered => "Zag.Term.prim (" ++ reprStr (Ty.prim name) ++
        ") (Zag.PrimitiveCtx.toPrimitiveValue " ++ PrimitiveCtx.ReprName.expr primCtx ++ " " ++
          reprStr name ++ " (" ++ rendered ++
        ") (by rfl))"
    | none => "Zag.Term.prim (" ++ reprStr (Ty.prim name) ++
        ") (_opaque : Zag.Ty.type _ (" ++ reprStr (Ty.prim name) ++ "))"
| .prim ty _ => "Zag.Term.prim (" ++ reprStr ty ++
    ") (_opaque : Zag.Ty.type _ (" ++ reprStr ty ++ "))"
| .primFunc name => "Zag.Term.primFunc " ++ reprStr name
| .var idx => "Zag.Term.var " ++ reprStr idx
| .app fn args => "Zag.Term.app (" ++ reprString fn ++ ") " ++ reprListString args
| .op name args => "Zag.Term.op " ++ reprStr name ++ " " ++ reprListString args
| .«abbrev» name typeArgs args =>
    "Zag.Term.abbrev " ++ reprStr name ++ " " ++ reprStr typeArgs ++ " " ++ reprListString args
| .mkStruct tys => "Zag.Term.mkStruct " ++ reprStr tys
| .structProj tys idx => "Zag.Term.structProj " ++ reprStr tys ++ " " ++ reprStr idx.val
| .recurse resultTy init body =>
    "Zag.Term.recurse (" ++ reprStr resultTy ++ ") (" ++ reprString init ++ ") (" ++
      reprString body ++ ")"

private def reprListString {primCtx : PrimitiveCtx} [PrimitiveCtx.ReprName primCtx] :
    List (Term primCtx) → String
| [] => "[]"
| term :: terms => "[" ++ reprString term ++ reprListTailString terms

private def reprListTailString {primCtx : PrimitiveCtx} [PrimitiveCtx.ReprName primCtx] :
    List (Term primCtx) → String
| [] => "]"
| term :: terms => ", " ++ reprString term ++ reprListTailString terms

end

instance {primCtx : PrimitiveCtx} [PrimitiveCtx.ReprName primCtx] : Repr (Term primCtx) where
  reprPrec term _ := Std.Format.text ("(" ++ reprString term ++ " : Zag.Term " ++
    PrimitiveCtx.ReprName.expr primCtx ++ ")")

/- lift a term into the context's monad using the `pure` operator -/
def lift {primCtx : PrimitiveCtx} (term : Term primCtx) : Term primCtx :=
  .op "pure" [term]

def bind {primCtx : PrimitiveCtx} (computation continuation : Term primCtx) : Term primCtx :=
  .op "bind" [computation, continuation]

end Term

/- Zag propositions (first order statements about expressions and types)
  note that the debrujin indexes for varTy and varTerm are tracked seperately -/
inductive Pr (E : Type) where
/- include a ctx so that Zag propositions can talk about bound vars
  without needing to reason about a lambda style funcion type directly -/
| eq (ctx : List Ty) (ty : Ty) : E → E → Pr E
| hasType (ctx : List Ty) : E → Ty → Pr E
| and : Pr E → Pr E → Pr E
| or : Pr E → Pr E → Pr E
| implies : Pr E → Pr E → Pr E
/- quantify over Ty -/
| forallTy : Pr E → Pr E
/- quantify over Term -/
| forallTerm : Pr E → Pr E
deriving DecidableEq

namespace Pr

def map {E F : Type} (f : E → F) : Pr E → Pr F
| .eq ctx ty lhs rhs => .eq ctx ty (f lhs) (f rhs)
| .hasType ctx e ty => .hasType ctx (f e) ty
| .and p q => .and (p.map f) (q.map f)
| .or p q => .or (p.map f) (q.map f)
| .implies p q => .implies (p.map f) (q.map f)
| .forallTy p => .forallTy (p.map f)
| .forallTerm p => .forallTerm (p.map f)

@[simp] theorem map_id {E : Type} :
    ∀ p : Pr E, p.map id = p
| .eq _ _ _ _ => rfl
| .hasType _ _ _ => rfl
| .and p q => by simp [map, map_id p, map_id q]
| .or p q => by simp [map, map_id p, map_id q]
| .implies p q => by simp [map, map_id p, map_id q]
| .forallTy p => by simp [map, map_id p]
| .forallTerm p => by simp [map, map_id p]

theorem map_congr {E F : Type} {f g : E → F} (hfg : ∀ e, f e = g e) :
    ∀ p : Pr E, p.map f = p.map g
| .eq _ _ _ _ => by simp [map, hfg]
| .hasType _ _ _ => by simp [map, hfg]
| .and p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .or p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .implies p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .forallTy p => by simp [map, map_congr hfg p]
| .forallTerm p => by simp [map, map_congr hfg p]

theorem map_eq_self {E : Type} {f : E → E} (hf : ∀ e, f e = e) :
    ∀ p : Pr E, p.map f = p
| p => (map_congr hf p).trans (map_id p)

@[simp] theorem map_map {E F G : Type} (g : F → G) (f : E → F) :
    ∀ p : Pr E, (p.map f).map g = p.map (g ∘ f)
| .eq _ _ _ _ => rfl
| .hasType _ _ _ => rfl
| .and p q => by simp [map, map_map g f p, map_map g f q]
| .or p q => by simp [map, map_map g f p, map_map g f q]
| .implies p q => by simp [map, map_map g f p, map_map g f q]
| .forallTy p => by simp [map, map_map g f p]
| .forallTerm p => by simp [map, map_map g f p]

def forallTermOfType {primCtx : PrimitiveCtx} (boundIdx : Nat) (ty : Ty) (body : Pr (Term primCtx)) : Pr (Term primCtx) :=
  .forallTerm (.implies (.hasType [] (.var boundIdx) ty) body)

end Pr

structure PrimFunc (primCtx : PrimitiveCtx) where
  args : List String
  out : String
  /- whether the function returns `m(out)` instead of `out` -/
  monadic : Bool := false
  hprim : out::args ⊆ primCtx.prims.map (·.name)
  interp : List (Val primCtx) → Option (Val primCtx)

/- declared result type of a primitive function -/
def PrimFunc.outTy {primCtx} (pfunc : PrimFunc primCtx) : Ty :=
  if pfunc.monadic then .m (.prim pfunc.out) else .prim pfunc.out

def PrimFunc.ty {primCtx} (pfunc : PrimFunc primCtx) : Ty :=
  (.func (pfunc.args.map (.prim ·)) pfunc.outTy)

/-all primitive functions
  for example for nat we have
  [
    ("add", ["Nat", "Nat"], "Nat")
    ("succ", ["Nat"], "Nat")
  ]
-/
abbrev PrimFuncCtx (primCtx : PrimitiveCtx) := List (String × PrimFunc primCtx)

def PrimFuncCtx.get? {primCtx : PrimitiveCtx} (primFuncCtx : PrimFuncCtx primCtx) (name : String) : Option (PrimFunc primCtx) :=
  (primFuncCtx.find? (·.1 = name)).map (·.2)

/- A transparent Zag function. Its body binds one nameless term variable per `varCtx` entry. -/
structure TermAbbrev (primCtx : PrimitiveCtx) where
  /- number of generic type arguments accepted by the abbreviation -/
  typeArity : Nat
  varCtx : VarCtx
  outTy : Ty
  body : Term primCtx

namespace TermAbbrevCtx

abbrev Raw (primCtx : PrimitiveCtx) := List (String × TermAbbrev primCtx)

def Raw.get? {primCtx : PrimitiveCtx} (ctx : Raw primCtx)
    (name : String) : Option (TermAbbrev primCtx) :=
  (ctx.find? (·.1 = name)).map (·.2)

def Raw.getWithPrefix? {primCtx : PrimitiveCtx} : Raw primCtx → String →
    Option (Raw primCtx × TermAbbrev primCtx)
| [], _ => none
| entry :: rest, name =>
    if entry.1 = name then
      some ([], entry.2)
    else
      match Raw.getWithPrefix? rest name with
      | some (prior, definition) => some (entry :: prior, definition)
      | none => none

theorem Raw.exists_getWithPrefix?_of_get? {primCtx : PrimitiveCtx}
    {ctx : Raw primCtx} {name : String} {definition : TermAbbrev primCtx}
    (h : ctx.get? name = some definition) :
    ∃ prior, ctx.getWithPrefix? name = some (prior, definition) := by
  induction ctx with
  | nil => simp [Raw.get?] at h
  | cons entry rest ih =>
      by_cases hname : entry.1 = name
      · have hdefinition : entry.2 = definition := by
          simpa [Raw.get?, List.find?, hname] using h
        exact ⟨[], by simp [Raw.getWithPrefix?, hname, hdefinition]⟩
      · have hrest : Raw.get? rest name = some definition := by
          simpa [Raw.get?, List.find?, hname] using h
        obtain ⟨prior, hprior⟩ := ih hrest
        exact ⟨entry :: prior, by simp [Raw.getWithPrefix?, hname, hprior]⟩

theorem Raw.get?_eq_some_of_getWithPrefix? {primCtx : PrimitiveCtx}
    {ctx prior : Raw primCtx} {name : String} {definition : TermAbbrev primCtx}
    (h : ctx.getWithPrefix? name = some (prior, definition)) :
    ctx.get? name = some definition := by
  induction ctx generalizing prior definition with
  | nil => simp [Raw.getWithPrefix?] at h
  | cons entry rest ih =>
      by_cases hname : entry.1 = name
      · have hdefinition : entry.2 = definition := by
          simp only [Raw.getWithPrefix?, hname, ↓reduceIte, Option.some.injEq] at h
          exact congrArg Prod.snd h
        simp [Raw.get?, List.find?, hname, hdefinition]
      · simp only [Raw.getWithPrefix?, hname, ↓reduceIte] at h
        split at h
        · next foundPrior foundDefinition hrest =>
            cases h
            simpa [Raw.get?, List.find?, hname] using ih hrest
        · contradiction

end TermAbbrevCtx

private def Term.abbrevNames {primCtx : PrimitiveCtx} : Term primCtx → List String
| .prim _ _ | .primFunc _ | .var _ | .mkStruct _ | .structProj _ _ => []
| .app fn args => fn.abbrevNames ++ args.flatMap Term.abbrevNames
| .op _ args => args.flatMap Term.abbrevNames
| .«abbrev» name _ args => name :: args.flatMap Term.abbrevNames
| .recurse _ init body => init.abbrevNames ++ body.abbrevNames

private def TermAbbrevCtx.validFrom {primCtx : PrimitiveCtx}
    (previous : TermAbbrevCtx.Raw primCtx) : TermAbbrevCtx.Raw primCtx → Bool
| [] => true
| entry :: rest =>
    entry.2.body.abbrevNames.all (fun name => previous.any (·.1 = name)) &&
      validFrom (previous ++ [entry]) rest

/- Names are unique and bodies refer only to earlier term abbreviations. -/
def TermAbbrevCtx.Valid {primCtx : PrimitiveCtx} (ctx : TermAbbrevCtx.Raw primCtx) : Prop :=
  (ctx.map Prod.fst).Nodup ∧
    TermAbbrevCtx.validFrom [] ctx = true

instance {primCtx : PrimitiveCtx} (ctx : TermAbbrevCtx.Raw primCtx) :
    Decidable (TermAbbrevCtx.Valid ctx) := by
  unfold TermAbbrevCtx.Valid
  infer_instance

structure StructuralTermAbbrevCtx (primCtx : PrimitiveCtx) where
  val : TermAbbrevCtx.Raw primCtx
  isValid : TermAbbrevCtx.Valid val

namespace TermAbbrevCtx

instance {primCtx : PrimitiveCtx} :
    Coe (StructuralTermAbbrevCtx primCtx) (TermAbbrevCtx.Raw primCtx) :=
  ⟨StructuralTermAbbrevCtx.val⟩

def structuralEmpty {primCtx : PrimitiveCtx} : StructuralTermAbbrevCtx primCtx :=
  ⟨[], ⟨by simp, rfl⟩⟩

end TermAbbrevCtx

/- The context needed to check declarations; it deliberately does not mention term abbreviations. -/
structure BaseCtx where
  primCtx : PrimitiveCtx
  primFuncCtx : PrimFuncCtx primCtx
  opCtx : OpCtx primCtx
  tyAbbrevCtx : TypeAbbrevCtx := .empty

mutual

def Ty.runtimeTagSafe : Ty → Bool
| .var _ | .«abbrev» _ _ => false
| .prim _ => true
| .option ty | .m ty => ty.runtimeTagSafe
| .union tys | .struct tys => Ty.runtimeTagsSafe tys
| .func args out => Ty.runtimeTagsSafe args && out.runtimeTagSafe

def Ty.runtimeTagsSafe : List Ty → Bool
| [] => true
| ty :: tys => ty.runtimeTagSafe && Ty.runtimeTagsSafe tys

end

mutual

def Term.inferType? (base : BaseCtx) (terms : TermAbbrevCtx.Raw base.primCtx)
    (typeArity : Nat) (varCtx : VarCtx) : Term base.primCtx → Option Ty
| .prim ty _ =>
    if Ty.validIn base.tyAbbrevCtx.val typeArity ty &&
        ty.normalizeAbbrev base.tyAbbrevCtx = ty && Ty.runtimeTagSafe ty then
      some ty
    else none
| .primFunc name =>
    (base.primFuncCtx.get? name).map fun definition =>
      definition.ty.normalizeAbbrev base.tyAbbrevCtx
| .var idx => (varCtx[idx]?).map (Ty.normalizeAbbrev base.tyAbbrevCtx)
| .app fn args => do
    let (.func expected out) ← inferType? base terms typeArity varCtx fn | none
    let actual ← inferTypes? base terms typeArity varCtx args
    if actual = expected then some out else none
| .op name args => do
    let actual ← inferTypes? base terms typeArity varCtx args
    (base.opCtx.outTy? name actual).map (Ty.normalizeAbbrev base.tyAbbrevCtx)
| .«abbrev» name typeArgs args => do
    let definition ← terms.get? name
    if typeArgs.length != definition.typeArity ||
        !Ty.validListIn base.tyAbbrevCtx.val typeArity typeArgs then none
    let actual ← inferTypes? base terms typeArity varCtx args
    let expected := definition.varCtx.map fun ty =>
      (Ty.subst typeArgs ty).normalizeAbbrev base.tyAbbrevCtx
    if actual = expected then
      some ((Ty.subst typeArgs definition.outTy).normalizeAbbrev base.tyAbbrevCtx)
    else none
| .mkStruct tys =>
    if Ty.validListIn base.tyAbbrevCtx.val typeArity tys then
      let tys := tys.map (Ty.normalizeAbbrev base.tyAbbrevCtx)
      some (.func tys (.struct tys))
    else none
| .structProj tys idx =>
    if Ty.validListIn base.tyAbbrevCtx.val typeArity tys then
      let normalized := tys.map (Ty.normalizeAbbrev base.tyAbbrevCtx)
      have hlen : tys.length = normalized.length := by simp [normalized]
      some (.func [.struct normalized] normalized[idx.cast hlen])
    else none
| .recurse resultTy init body => do
    if !Ty.validIn base.tyAbbrevCtx.val typeArity resultTy then none
    let resultTy := resultTy.normalizeAbbrev base.tyAbbrevCtx
    let stateTy ← inferType? base terms typeArity varCtx init
    let bodyTy ← inferType? base terms typeArity
      (varCtx ++ [stateTy, .func [stateTy] resultTy]) body
    if bodyTy = resultTy then some resultTy else none

def Term.inferTypes? (base : BaseCtx) (terms : TermAbbrevCtx.Raw base.primCtx)
    (typeArity : Nat) (varCtx : VarCtx) : List (Term base.primCtx) → Option (List Ty)
| [] => some []
| term :: rest => do
    let ty ← Term.inferType? base terms typeArity varCtx term
    let tys ← Term.inferTypes? base terms typeArity varCtx rest
    some (ty :: tys)

end


def TermAbbrev.check (base : BaseCtx) (prior : TermAbbrevCtx.Raw base.primCtx)
    (definition : TermAbbrev base.primCtx) : Bool :=
  Ty.validListIn base.tyAbbrevCtx.val definition.typeArity definition.varCtx &&
    Ty.validIn base.tyAbbrevCtx.val definition.typeArity definition.outTy &&
    definition.body.inferType? base prior definition.typeArity definition.varCtx =
      some (definition.outTy.normalizeAbbrev base.tyAbbrevCtx)

def TermAbbrevCtx.checkFrom (base : BaseCtx) :
    TermAbbrevCtx.Raw base.primCtx → TermAbbrevCtx.Raw base.primCtx → Bool
| _, [] => true
| prior, entry :: rest =>
    !prior.any (·.1 = entry.1) && entry.2.check base prior &&
      checkFrom base (prior ++ [entry]) rest

def TermAbbrevCtx.check (base : BaseCtx) (ctx : TermAbbrevCtx.Raw base.primCtx) : Bool :=
  TermAbbrevCtx.checkFrom base [] ctx

private theorem TermAbbrevCtx.checkFrom_getWithPrefix? {base : BaseCtx}
    {accumulated entries priorEntries : TermAbbrevCtx.Raw base.primCtx}
    {name : String} {definition : TermAbbrev base.primCtx}
    (hcheck : TermAbbrevCtx.checkFrom base accumulated entries = true)
    (hget : entries.getWithPrefix? name = some (priorEntries, definition)) :
    definition.check base (accumulated ++ priorEntries) = true := by
  induction entries generalizing accumulated priorEntries definition with
  | nil => simp [TermAbbrevCtx.Raw.getWithPrefix?] at hget
  | cons entry rest ih =>
      simp only [TermAbbrevCtx.checkFrom, Bool.and_eq_true] at hcheck
      simp only [TermAbbrevCtx.Raw.getWithPrefix?] at hget
      split at hget
      · cases hget
        simpa using hcheck.1.2
      · split at hget
        · next foundPrefix foundDefinition hrest =>
            cases hget
            simpa [List.append_assoc] using ih hcheck.2 hrest
        · contradiction

structure CheckedTermAbbrevCtx (base : BaseCtx) where
  val : TermAbbrevCtx.Raw base.primCtx
  isChecked : TermAbbrevCtx.check base val = true

namespace CheckedTermAbbrevCtx

abbrev empty (base : BaseCtx) : CheckedTermAbbrevCtx base := ⟨[], rfl⟩

@[simp] theorem empty_val (base : BaseCtx) : (empty base).val = [] := rfl

def get? {base : BaseCtx} (ctx : CheckedTermAbbrevCtx base)
    (name : String) : Option (TermAbbrev base.primCtx) := ctx.val.get? name

def getWithPrefix? {base : BaseCtx} (ctx : CheckedTermAbbrevCtx base)
    (name : String) : Option (TermAbbrevCtx.Raw base.primCtx × TermAbbrev base.primCtx) :=
  ctx.val.getWithPrefix? name

theorem getWithPrefix?_check {base : BaseCtx} {ctx : CheckedTermAbbrevCtx base}
    {name : String} {prior : TermAbbrevCtx.Raw base.primCtx}
    {definition : TermAbbrev base.primCtx}
    (hget : ctx.getWithPrefix? name = some (prior, definition)) :
    definition.check base prior = true := by
  apply TermAbbrevCtx.checkFrom_getWithPrefix? (accumulated := []) ctx.isChecked
  simpa [getWithPrefix?] using hget

/-- A declaration in a checked context has a body of its canonical declared result type. -/
theorem getWithPrefix?_bodyInferType {base : BaseCtx} {ctx : CheckedTermAbbrevCtx base}
    {name : String} {prior : TermAbbrevCtx.Raw base.primCtx}
    {definition : TermAbbrev base.primCtx}
    (hget : ctx.getWithPrefix? name = some (prior, definition)) :
    definition.body.inferType? base prior definition.typeArity definition.varCtx =
      some (definition.outTy.normalizeAbbrev base.tyAbbrevCtx) := by
  have hcheck := getWithPrefix?_check hget
  simp only [TermAbbrev.check, Bool.and_eq_true] at hcheck
  exact of_decide_eq_true hcheck.2

def ofRaw? (base : BaseCtx) (raw : TermAbbrevCtx.Raw base.primCtx) :
    Option (CheckedTermAbbrevCtx base) :=
  if h : TermAbbrevCtx.check base raw = true then some ⟨raw, h⟩ else none

end CheckedTermAbbrevCtx

/- Everything a `Term` is interpreted against: primitives, operators, and transparent
  abbreviation declarations. Later fields may depend on the earlier contexts. -/
structure Ctx extends BaseCtx where
  termAbbrevCtx : CheckedTermAbbrevCtx toBaseCtx := .empty toBaseCtx

/- monad used to interpret `Ty.m` in this context -/
abbrev Ctx.M (ctx : Ctx) : Type → Type := ctx.primCtx.M

/- `hasType Δ Γ t T` means `Γ ⊢ t : T`. Generic term parameters remain nameless in `VarCtx`. -/
inductive Term.hasType (ctx : Ctx) : VarCtx → Term ctx.primCtx → Ty → Prop where
| prim {varCtx} {ty : Ty} (val : Ty.type ctx.primCtx ty) :
    hasType ctx varCtx (.prim ty val) ty
| primFunc {varCtx} {idx : Fin ctx.primFuncCtx.length} :
    hasType ctx varCtx (.primFunc ctx.primFuncCtx[idx].1) ctx.primFuncCtx[idx].2.ty
| var {varCtx} {idx : Fin varCtx.length} {ty : Ty} (h : varCtx.get idx = ty) :
    hasType ctx varCtx (.var idx) ty
| op {varCtx} {name : String} {args : List (Term ctx.primCtx)}
    {tys : List Ty} {r : Ty}
    (hargs₁ : args.length = tys.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] tys[idx])
    (hout : ctx.opCtx.outTy? name tys = some r) :
    hasType ctx varCtx (.op name args) r
| «abbrev» {varCtx} {name : String} {typeArgs : List Ty}
    {args : List (Term ctx.primCtx)} {definition : TermAbbrev ctx.primCtx}
    {prior : TermAbbrevCtx.Raw ctx.primCtx}
    (hget : ctx.termAbbrevCtx.getWithPrefix? name = some (prior, definition))
    (htypes : typeArgs.length = definition.typeArity)
    (htypeArgs : Ty.validListIn ctx.tyAbbrevCtx.val 0 typeArgs = true)
    (hargs₁ : args.length = definition.varCtx.length)
    (hargs₂ : ∀ idx : Fin args.length,
      hasType ctx varCtx args[idx]
        ((Ty.subst typeArgs definition.varCtx[idx]).normalizeAbbrev ctx.tyAbbrevCtx)) :
    hasType ctx varCtx (.«abbrev» name typeArgs args)
      ((Ty.subst typeArgs definition.outTy).normalizeAbbrev ctx.tyAbbrevCtx)
| app {varCtx} {f : Term ctx.primCtx} {fTy : Ty}
    {args : List (Term ctx.primCtx)} {argsTy : List Ty}
    (hf : hasType ctx varCtx f (.func argsTy fTy))
    (hargs₁ : args.length = argsTy.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] argsTy[idx]) :
    hasType ctx varCtx (.app f args) fTy
| mkStruct {varCtx} {tys : List Ty} :
    hasType ctx varCtx (.mkStruct tys) (.func tys (.struct tys))
| structProj {varCtx} {tys : List Ty} (idx : Fin tys.length) :
    hasType ctx varCtx (.structProj tys idx) (.func [.struct tys] tys[idx])
| recurse {varCtx} {stateTy resultTy : Ty} {init body : Term ctx.primCtx}
    (hinit : hasType ctx varCtx init stateTy)
    (hbody : hasType ctx (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy) :
    hasType ctx varCtx (.recurse resultTy init body) resultTy

theorem Term.hasType.abbrev_result {ctx : Ctx} {varCtx : VarCtx} {name : String}
    {typeArgs : List Ty} {args : List (Term ctx.primCtx)} {ty : Ty}
    (h : Term.hasType ctx varCtx (.«abbrev» name typeArgs args) ty) :
    ∃ (definition : TermAbbrev ctx.primCtx) (prior : TermAbbrevCtx.Raw ctx.primCtx),
      ctx.termAbbrevCtx.getWithPrefix? name = some (prior, definition) ∧
      ty = (Ty.subst typeArgs definition.outTy).normalizeAbbrev ctx.tyAbbrevCtx := by
  cases h with
  | «abbrev» hget _ _ _ _ => exact ⟨_, _, hget, rfl⟩

theorem Term.hasType.abbrev_typeArgs_valid {ctx : Ctx} {varCtx : VarCtx} {name : String}
    {typeArgs : List Ty} {args : List (Term ctx.primCtx)} {ty : Ty}
    (h : Term.hasType ctx varCtx (.«abbrev» name typeArgs args) ty) :
    Ty.validListIn ctx.tyAbbrevCtx.val 0 typeArgs = true := by
  cases h with
  | «abbrev» _ _ htypeArgs _ _ => exact htypeArgs

/- a `Term` of a particular `ty : Ty` under some context and variable context -/
abbrev TermOf (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) :=
  { term : Term ctx.primCtx // term.hasType ctx varCtx ty }
