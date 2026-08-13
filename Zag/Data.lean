/-!
All objects are either a type: `Zag.Ty`
Or a term: `Zag.Term`

All functions are `Zag.Term × ... × Zag.Term → Zag.Term`
or `Zag.Ty × ... × Zag.Ty → Zag.Ty`

A program is a list of named `Zag.Block`s. A block declares named parameters, a list of
instructions -- each of which just names the value of a `Term` -- and a returned term. Blocks
refer to one another by name, which is where Zag gets recursion and general control flow: a
block may name itself.

Everything a term can compute is either an `op` (semantics supplied by the context) or a `call`
(semantics supplied by the program). Variables, ops, blocks and primitives are all named by
`String`; there are no de Bruijn indices.

Typing is a predicate. Evaluation is partial and returns `Option`; termination is expressed by
successful evaluation, i.e. `∃ v, eval ... = some v`.
-/

namespace Zag

/- A type is a generic variable, an application of a named parametric primitive type
  constructor, or a function type. `option`, `union`, `struct` and `m` are not built in: each is
  an ordinary primitive of the appropriate arity supplied by a `PrimitiveCtx`. -/
inductive Ty where
/- name of a generic type variable -/
| var : String → Ty
/- application of a named primitive type constructor, e.g. `prim "Nat" []`, `prim "Option" [t]` -/
| prim : String → List Ty → Ty
| func : List Ty → Ty → Ty
deriving Repr

mutual

def Ty.decEq : (a b : Ty) → Decidable (a = b)
| .var a, .var b =>
    if h : a = b then isTrue (by rw [h])
    else isFalse (fun hc => h (by injection hc))
| .prim a as, .prim b bs =>
    match String.decEq a b, Ty.decEqList as bs with
    | isTrue hn, isTrue hs => isTrue (by rw [hn, hs])
    | isFalse hn, _ => isFalse (fun hc => hn (by injection hc))
    | _, isFalse hs => isFalse (fun hc => hs (by injection hc))
| .func as a, .func bs b =>
    match Ty.decEqList as bs, Ty.decEq a b with
    | isTrue hs, isTrue h => isTrue (by rw [hs, h])
    | isFalse hs, _ => isFalse (fun hc => hs (by injection hc))
    | _, isFalse h => isFalse (fun hc => h (by injection hc))
| .var _, .prim _ _ => isFalse nofun
| .var _, .func _ _ => isFalse nofun
| .prim _ _, .var _ => isFalse nofun
| .prim _ _, .func _ _ => isFalse nofun
| .func _ _, .var _ => isFalse nofun
| .func _ _, .prim _ _ => isFalse nofun

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

/- A named scope. Entries are in declaration order and a later entry shadows an earlier one of
  the same name, so lookup keeps the last match. -/
abbrev Scope (α : Type _) := List (String × α)

def Scope.get? {α : Type _} (scope : Scope α) (name : String) : Option α :=
  (scope.reverse.find? (·.1 = name)).map (·.2)

namespace Scope

@[simp] theorem get?_nil {α : Type _} (name : String) :
    Scope.get? ([] : Scope α) name = none := rfl

theorem get?_append {α : Type _} (before after : Scope α) (name : String) :
    Scope.get? (before ++ after) name = (Scope.get? after name).or (Scope.get? before name) := by
  simp only [Scope.get?, List.reverse_append, List.find?_append]
  cases after.reverse.find? (·.1 = name) <;> simp

@[simp] theorem get?_singleton {α : Type _} (name entryName : String) (value : α) :
    Scope.get? [(entryName, value)] name = if name = entryName then some value else none := by
  simp only [Scope.get?, List.reverse_cons, List.reverse_nil, List.nil_append, List.find?_cons]
  by_cases h : entryName = name <;> simp [h, eq_comm (a := name)]

theorem get?_append_singleton {α : Type _} (before : Scope α) (name entryName : String)
    (value : α) :
    Scope.get? (before ++ [(entryName, value)]) name =
      if name = entryName then some value else Scope.get? before name := by
  rw [get?_append, get?_singleton]
  by_cases h : name = entryName <;> simp [h]

end Scope

/- substitute named generic type variables -/
def Ty.subst (subst : Scope Ty) : Ty → Ty
| .var name => (Scope.get? subst name).getD (.var name)
| .prim name args => .prim name (args.map (Ty.subst subst))
| .func args out => .func (args.map (Ty.subst subst)) (Ty.subst subst out)

/- A named parametric type constructor. `arity` is the number of type arguments it accepts and
  `type` interprets it, applied to the interpretations of those arguments. -/
structure Primitive where
  name : String
  arity : Nat
  type : List Type → Type
  /- how to render a value; a constructor may decline for argument shapes it cannot print -/
  repr : (args : List Type) → Option (Repr (type args))

/- a ground (argument-free) primitive -/
abbrev Primitive.of (name : String) (type : Type) [Repr type] : Primitive where
  name := name
  arity := 0
  type := fun _ => type
  repr := fun _ => some inferInstance

def Primitive.reprValue? (primitive : Primitive) (args : List Type)
    (value : primitive.type args) : Option String :=
  match primitive.repr args with
  | some inst => letI := inst; some (reprStr value)
  | none => none

/- the primitive type constructors a term may mention -/
structure PrimitiveCtx where
  prims : List Primitive

class PrimitiveCtx.ReprName (primCtx : PrimitiveCtx) where
  expr : String

abbrev PrimitiveCtx.ofPrims (prims : List Primitive) : PrimitiveCtx where
  prims := prims

def PrimitiveCtx.find? (primCtx : PrimitiveCtx) (name : String) : Option Primitive :=
  primCtx.prims.find? (·.name = name)

/- interpretation of a ground primitive, i.e. one applied to no type arguments -/
abbrev PrimitiveCtx.get? (primCtx : PrimitiveCtx) (name : String) : Option Type :=
  (primCtx.find? name).map (·.type [])

mutual

def Ty.type (primCtx : PrimitiveCtx) : Ty → Type
| var _ => Empty -- unbound generic variables are uninhabited
| prim name args =>
    match primCtx.find? name with
    | some primitive => primitive.type (Ty.types primCtx args)
    | none => Empty
| func argsTy outTy =>
    ((idx : Fin argsTy.length) → Ty.type primCtx argsTy[idx]) → Option (Ty.type primCtx outTy)
termination_by ty => sizeOf ty
decreasing_by
  all_goals
    simp only [Fin.getElem_fin, Ty.prim.sizeOf_spec, Ty.func.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt); omega)

def Ty.types (primCtx : PrimitiveCtx) : List Ty → List Type
| [] => []
| ty :: tys => Ty.type primCtx ty :: Ty.types primCtx tys
termination_by tys => sizeOf tys
decreasing_by
  all_goals simp only [List.cons.sizeOf_spec]; omega

end

theorem Ty.type_var (primCtx : PrimitiveCtx) (name : String) :
    Ty.type primCtx (.var name) = Empty := by
  rw [Ty.type.eq_def]

theorem Ty.type_prim (primCtx : PrimitiveCtx) (name : String) (args : List Ty) :
    Ty.type primCtx (.prim name args) =
      match primCtx.find? name with
      | some primitive => primitive.type (Ty.types primCtx args)
      | none => Empty := by
  rw [Ty.type.eq_def]

theorem Ty.type_func (primCtx : PrimitiveCtx) (argsTy : List Ty) (outTy : Ty) :
    Ty.type primCtx (.func argsTy outTy) =
      ((((idx : Fin argsTy.length) → Ty.type primCtx argsTy[idx]) →
        Option (Ty.type primCtx outTy))) := by
  rw [Ty.type.eq_def]

theorem Ty.type_prim_of_find {primCtx : PrimitiveCtx} {name : String} {primitive : Primitive}
    (args : List Ty) (h : primCtx.find? name = some primitive) :
    Ty.type primCtx (.prim name args) = primitive.type (Ty.types primCtx args) := by
  rw [Ty.type_prim, h]

@[simp] theorem Ty.types_nil (primCtx : PrimitiveCtx) :
    Ty.types primCtx [] = [] := by
  rw [Ty.types.eq_def]

@[simp] theorem Ty.types_cons (primCtx : PrimitiveCtx) (ty : Ty) (tys : List Ty) :
    Ty.types primCtx (ty :: tys) = Ty.type primCtx ty :: Ty.types primCtx tys := by
  rw [Ty.types.eq_def]

@[simp] theorem Ty.types_length (primCtx : PrimitiveCtx) :
    ∀ tys : List Ty, (Ty.types primCtx tys).length = tys.length
| [] => by simp
| _ :: tys => by simp [Ty.types_length primCtx tys]

theorem Ty.types_getElem (primCtx : PrimitiveCtx) :
    ∀ (tys : List Ty) (idx : Nat) (h : idx < tys.length),
      (Ty.types primCtx tys)[idx]'(by simpa using h) = Ty.type primCtx tys[idx]
| [], _, h => absurd h (by simp)
| _ :: tys, 0, _ => by simp
| _ :: tys, idx + 1, h => by
    simpa using Ty.types_getElem primCtx tys idx (by simpa using h)

/- interpretation of a ground primitive is the interpretation recorded by `PrimitiveCtx.get?` -/
theorem Ty.type_ground {primCtx : PrimitiveCtx} {name : String} {type : Type}
    (h : primCtx.get? name = some type) : Ty.type primCtx (.prim name []) = type := by
  simp only [PrimitiveCtx.get?, Option.map_eq_some_iff] at h
  obtain ⟨primitive, hfind, rfl⟩ := h
  rw [Ty.type_prim_of_find [] hfind, Ty.types_nil]

def PrimitiveCtx.toPrimitiveValue (primCtx : PrimitiveCtx) (name : String)
    {type : Type} (value : type) (h : primCtx.get? name = some type) :
    Ty.type primCtx (.prim name []) :=
  cast (Ty.type_ground h).symm value

def PrimitiveCtx.reprPrimitive? (primCtx : PrimitiveCtx) (name : String) (args : List Ty)
    (value : Ty.type primCtx (.prim name args)) : Option String :=
  match h : primCtx.find? name with
  | none => none
  | some primitive =>
      primitive.reprValue? (Ty.types primCtx args) (cast (Ty.type_prim_of_find args h) value)

/- variable context: the type of each name in scope -/
abbrev VarCtx := Scope Ty

namespace Ty

def applyUnary? (primCtx : PrimitiveCtx) (inputTy outputTy : Ty)
    (fn : Ty.type primCtx (.func [inputTy] outputTy))
    (input : Ty.type primCtx inputTy) : Option (Ty.type primCtx outputTy) :=
  let fn' := cast (Ty.type_func primCtx [inputTy] outputTy) fn
  fn' (fun _ => cast (congrArg (Ty.type primCtx) (by simp)) input)

end Ty

structure Val (primCtx : PrimitiveCtx) where
  ty : Ty
  val : Ty.type primCtx ty

def Val.as? {primCtx : PrimitiveCtx} (ty : Ty) (v : Val primCtx) : Option (Ty.type primCtx ty) :=
  if h : v.ty = ty then
    some (cast (congrArg (Ty.type primCtx) h) v.val)
  else none

/- evaluation environment: the value bound to each name in scope -/
abbrev Env (primCtx : PrimitiveCtx) := Scope (Val primCtx)

/- an environment supplies a value of the declared type for every name in scope -/
def Env.Models {primCtx : PrimitiveCtx} (env : Env primCtx) (varCtx : VarCtx) : Prop :=
  ∀ name ty, Scope.get? varCtx name = some ty →
    ∃ value, Scope.get? env name = some value ∧ value.ty = ty

/- lazy left-to-right operator program: an operator decides, one operand at a time, whether that
  operand is evaluated at all, which is what gives ops general control flow -/
inductive Op.Body (primCtx : PrimitiveCtx) where
| fail
| done (value : Val primCtx)
| next (evaluate : Bool) (resume : Option (Val primCtx) → Op.Body primCtx)

structure Op (primCtx : PrimitiveCtx) where
  arity : Nat
  out : (Fin arity → Ty) → Option Ty
  body : Op.Body primCtx

/- evaluate every operand left to right, then run `run` on the collected values -/
def Op.Body.eager {primCtx : PrimitiveCtx} (run : List (Val primCtx) → Option (Val primCtx)) :
    Nat → List (Val primCtx) → Op.Body primCtx
| 0, vals =>
    match run vals with
    | some value => .done value
    | none => .fail
| remaining + 1, vals => .next true fun
    | some value => eager run remaining (vals ++ [value])
    | none => .fail

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
    Nat → List (Val primCtx) → Op.Body primCtx :=
  Op.Body.eager sig.apply

@[simp] def toOp {primCtx : PrimitiveCtx} {arity : Nat} (sig : Signature primCtx arity) :
    Op primCtx where
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

/- An operator with fixed operand and result types. This is what used to be a "primitive
  function": such a function is now just an op, so a term has only one kind of named
  context-supplied operation. -/
def Op.ofVals {primCtx : PrimitiveCtx} (argTys : List Ty) (outTy : Ty)
    (interp : List (Val primCtx) → Option (Val primCtx)) : Op primCtx where
  arity := argTys.length
  out tys := if List.ofFn tys = argTys then some outTy else none
  body := Op.Body.eager (fun vals =>
    if vals.map Val.ty = argTys then do
      let raw ← (← interp vals).as? outTy
      some (Val.mk outTy raw)
    else none) argTys.length []

/- operator context: the named operators a term may use -/
abbrev OpCtx (primCtx : PrimitiveCtx) := List (String × Op primCtx)

def OpCtx.get? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx) (name : String) :
    Option (Op primCtx) :=
  (opCtx.find? (·.1 = name)).map (·.2)

/- infer an operator's output type -/
def OpCtx.outTy? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx)
    (name : String) (tys : List Ty) : Option Ty :=
  match opCtx.get? name with
  | some op =>
      if h : tys.length = op.arity then
        op.out (fun i => tys.get (i.cast h.symm))
      else none
  | none => none

/- A term computes a value. `op` names an operation whose semantics come from the context;
  `call` names a block whose semantics come from the program. -/
inductive Term (primCtx : PrimitiveCtx) where
/- primitive value tagged with its Zag type -/
| prim (ty : Ty) : Ty.type primCtx ty → Term primCtx
/- name of a variable in scope -/
| var : String → Term primCtx
| app : Term primCtx → List (Term primCtx) → Term primCtx
/- saturated application of a named n-ary operator -/
| op : String → List (Term primCtx) → Term primCtx
/- saturated call of a named block -/
| call : String → List (Term primCtx) → Term primCtx

/- One instruction names the value of a term for the remainder of its block. Instructions are
  terms rather than flat `op name args` rows, so operands may nest. -/
structure Instr (primCtx : PrimitiveCtx) where
  name : String
  value : Term primCtx

/- A named scope: parameters bound on entry (`phi` in SSA terms), straight-line instructions,
  and the term whose value the block returns. Blocks are declared explicitly and called by name
  rather than delimited by instruction ranges. -/
structure Block (primCtx : PrimitiveCtx) where
  params : VarCtx
  instrs : List (Instr primCtx)
  outTy : Ty
  result : Term primCtx

namespace Term

/- every block name a term calls -/
def callNames {primCtx : PrimitiveCtx} : Term primCtx → List String
| .prim _ _ | .var _ => []
| .app fn args => fn.callNames ++ args.flatMap callNames
| .op _ args => args.flatMap callNames
| .call name args => name :: args.flatMap callNames

end Term

def Block.callNames {primCtx : PrimitiveCtx} (block : Block primCtx) : List String :=
  block.instrs.flatMap (·.value.callNames) ++ block.result.callNames

namespace BlockCtx

abbrev Raw (primCtx : PrimitiveCtx) := Scope (Block primCtx)

def Raw.get? {primCtx : PrimitiveCtx} (ctx : Raw primCtx) (name : String) :
    Option (Block primCtx) := Scope.get? ctx name

end BlockCtx

/- Names are unique and every call names a declared block. Unlike the abbreviations blocks
  replace, a block may name itself or a later block, which is what makes recursion and loops
  expressible. -/
def BlockCtx.Valid {primCtx : PrimitiveCtx} (ctx : BlockCtx.Raw primCtx) : Prop :=
  (ctx.map Prod.fst).Nodup ∧
    ∀ entry ∈ ctx, ∀ name ∈ entry.2.callNames, name ∈ ctx.map Prod.fst

instance {primCtx : PrimitiveCtx} (ctx : BlockCtx.Raw primCtx) :
    Decidable (BlockCtx.Valid ctx) := by
  unfold BlockCtx.Valid
  infer_instance

structure BlockCtx (primCtx : PrimitiveCtx) where
  val : BlockCtx.Raw primCtx
  isValid : BlockCtx.Valid val

namespace BlockCtx

instance {primCtx : PrimitiveCtx} :
    Coe (BlockCtx primCtx) (BlockCtx.Raw primCtx) := ⟨BlockCtx.val⟩

def empty {primCtx : PrimitiveCtx} : BlockCtx primCtx := ⟨[], by simp [BlockCtx.Valid]⟩

def get? {primCtx : PrimitiveCtx} (ctx : BlockCtx primCtx) (name : String) :
    Option (Block primCtx) := ctx.val.get? name

end BlockCtx

/- Everything a `Term` is interpreted against: primitive types, operators, and the program's
  blocks. Later fields may depend on the earlier contexts. -/
structure Ctx where
  primCtx : PrimitiveCtx
  opCtx : OpCtx primCtx
  blockCtx : BlockCtx primCtx := .empty

namespace Term

mutual

private def reprString {primCtx : PrimitiveCtx} [PrimitiveCtx.ReprName primCtx] :
    Term primCtx → String
| .prim (.prim name args) value =>
    match primCtx.reprPrimitive? name args value with
    | some rendered => "Zag.Term.prim (" ++ reprStr (Ty.prim name args) ++
        ") (Zag.PrimitiveCtx.toPrimitiveValue " ++ PrimitiveCtx.ReprName.expr primCtx ++ " " ++
          reprStr name ++ " (" ++ rendered ++
        ") (by rfl))"
    | none => "Zag.Term.prim (" ++ reprStr (Ty.prim name args) ++
        ") (_opaque : Zag.Ty.type _ (" ++ reprStr (Ty.prim name args) ++ "))"
| .prim ty _ => "Zag.Term.prim (" ++ reprStr ty ++
    ") (_opaque : Zag.Ty.type _ (" ++ reprStr ty ++ "))"
| .var name => "Zag.Term.var " ++ reprStr name
| .app fn args => "Zag.Term.app (" ++ reprString fn ++ ") " ++ reprListString args
| .op name args => "Zag.Term.op " ++ reprStr name ++ " " ++ reprListString args
| .call name args => "Zag.Term.call " ++ reprStr name ++ " " ++ reprListString args

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

end Term

/- Zag propositions (first order statements about expressions and types)
  note that type variables and term variables are named and tracked separately -/
inductive Pr (E : Type) where
/- include a ctx so that Zag propositions can talk about bound vars
  without needing to reason about a lambda style funcion type directly -/
| eq (ctx : VarCtx) (ty : Ty) : E → E → Pr E
| hasType (ctx : VarCtx) : E → Ty → Pr E
| and : Pr E → Pr E → Pr E
| or : Pr E → Pr E → Pr E
| implies : Pr E → Pr E → Pr E
/- quantify over Ty, binding the name `ty` -/
| forallTy (ty : String) : Pr E → Pr E
/- quantify over Term, binding the name `term` -/
| forallTerm (term : String) : Pr E → Pr E
deriving DecidableEq

namespace Pr

def map {E F : Type} (f : E → F) : Pr E → Pr F
| .eq ctx ty lhs rhs => .eq ctx ty (f lhs) (f rhs)
| .hasType ctx e ty => .hasType ctx (f e) ty
| .and p q => .and (p.map f) (q.map f)
| .or p q => .or (p.map f) (q.map f)
| .implies p q => .implies (p.map f) (q.map f)
| .forallTy name p => .forallTy name (p.map f)
| .forallTerm name p => .forallTerm name (p.map f)

@[simp] theorem map_id {E : Type} :
    ∀ p : Pr E, p.map id = p
| .eq _ _ _ _ => rfl
| .hasType _ _ _ => rfl
| .and p q => by simp [map, map_id p, map_id q]
| .or p q => by simp [map, map_id p, map_id q]
| .implies p q => by simp [map, map_id p, map_id q]
| .forallTy _ p => by simp [map, map_id p]
| .forallTerm _ p => by simp [map, map_id p]

theorem map_congr {E F : Type} {f g : E → F} (hfg : ∀ e, f e = g e) :
    ∀ p : Pr E, p.map f = p.map g
| .eq _ _ _ _ => by simp [map, hfg]
| .hasType _ _ _ => by simp [map, hfg]
| .and p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .or p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .implies p q => by simp [map, map_congr hfg p, map_congr hfg q]
| .forallTy _ p => by simp [map, map_congr hfg p]
| .forallTerm _ p => by simp [map, map_congr hfg p]

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
| .forallTy _ p => by simp [map, map_map g f p]
| .forallTerm _ p => by simp [map, map_map g f p]

def forallTermOfType {primCtx : PrimitiveCtx} (name : String) (ty : Ty)
    (body : Pr (Term primCtx)) : Pr (Term primCtx) :=
  .forallTerm name (.implies (.hasType [] (.var name) ty) body)

end Pr

/- `hasType Γ t T` means `Γ ⊢ t : T`. -/
inductive Term.hasType (ctx : Ctx) : VarCtx → Term ctx.primCtx → Ty → Prop where
| prim {varCtx} {ty : Ty} (val : Ty.type ctx.primCtx ty) :
    hasType ctx varCtx (.prim ty val) ty
| var {varCtx} {name : String} {ty : Ty} (h : Scope.get? varCtx name = some ty) :
    hasType ctx varCtx (.var name) ty
| op {varCtx} {name : String} {args : List (Term ctx.primCtx)}
    {tys : List Ty} {r : Ty}
    (hargs₁ : args.length = tys.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] tys[idx])
    (hout : ctx.opCtx.outTy? name tys = some r) :
    hasType ctx varCtx (.op name args) r
| call {varCtx} {name : String} {args : List (Term ctx.primCtx)} {block : Block ctx.primCtx}
    (hget : ctx.blockCtx.get? name = some block)
    (hargs₁ : args.length = block.params.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] block.params[idx].2) :
    hasType ctx varCtx (.call name args) block.outTy
| app {varCtx} {f : Term ctx.primCtx} {fTy : Ty}
    {args : List (Term ctx.primCtx)} {argsTy : List Ty}
    (hf : hasType ctx varCtx f (.func argsTy fTy))
    (hargs₁ : args.length = argsTy.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] argsTy[idx]) :
    hasType ctx varCtx (.app f args) fTy

/- Instructions are checked in order, each extending the scope with its own binding. The final
  scope is the one the block's returned term is checked against. -/
inductive Block.instrsHaveType (ctx : Ctx) :
    VarCtx → List (Instr ctx.primCtx) → VarCtx → Prop where
| nil {varCtx} : instrsHaveType ctx varCtx [] varCtx
| cons {varCtx : VarCtx} {instr : Instr ctx.primCtx} {instrs : List (Instr ctx.primCtx)}
    {ty : Ty} {out : VarCtx}
    (hvalue : Term.hasType ctx varCtx instr.value ty)
    (hrest : instrsHaveType ctx (varCtx ++ [(instr.name, ty)]) instrs out) :
    instrsHaveType ctx varCtx (instr :: instrs) out

/- A block is well typed when its instructions check in order and its returned term has the
  declared output type. A block's declared `outTy` is what `Term.hasType.call` uses, so a
  recursive block is typeable without inferring its own result type. -/
def Block.WellTyped (ctx : Ctx) (block : Block ctx.primCtx) : Prop :=
  ∃ scope, Block.instrsHaveType ctx block.params block.instrs scope ∧
    Term.hasType ctx scope block.result block.outTy

/- every block of the program is well typed -/
def Ctx.WellTyped (ctx : Ctx) : Prop :=
  ∀ entry ∈ ctx.blockCtx.val, Block.WellTyped ctx entry.2

/- a `Term` of a particular `ty : Ty` under some context and variable context -/
abbrev TermOf (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) :=
  { term : Term ctx.primCtx // term.hasType ctx varCtx ty }
