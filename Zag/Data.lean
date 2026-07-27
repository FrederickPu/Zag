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

declare_syntax_cat zagTy
declare_syntax_cat zagTerm

syntax "ty%" "{" zagTy "}" : term
syntax "term%" "{" zagTerm "}" : term
syntax "zagTerm%" zagTerm : term
syntax "zagName%" ident : term

syntax ident : zagTy
syntax str : zagTy
syntax "var(" term ")" : zagTy
syntax "option(" zagTy ")" : zagTy
syntax "m(" zagTy ")" : zagTy
syntax "union[" zagTy,* "]" : zagTy
syntax "struct[" zagTy,* "]" : zagTy
syntax "func[" zagTy,* "]" "=>" zagTy : zagTy
syntax "(" zagTy ")" : zagTy

syntax "raw(" term ")" : zagTerm
syntax "term(" term ")" : zagTerm
syntax "prim(" term ":" zagTy ")" : zagTerm
syntax "func(" ident ")" : zagTerm
syntax "func(" str ")" : zagTerm
syntax "var(" term ")" : zagTerm
syntax "call" zagTerm "[" zagTerm,* "]" : zagTerm
syntax "op" str "[" zagTerm,* "]" : zagTerm
syntax "recurse" zagTy "from" zagTerm "{" zagTerm "}" : zagTerm
syntax "mkStruct[" zagTy,* "]" : zagTerm
syntax "struct[" zagTy,* "]" "[" zagTerm,* "]" : zagTerm
syntax "(" zagTerm ")" : zagTerm

macro_rules
  | `(zagName% $name:ident) =>
      pure (Lean.Syntax.mkStrLit name.getId.toString)
  | `(ty% { $name:ident }) => `((Zag.Ty.prim (zagName% $name) : Zag.Ty))
  | `(ty% { $name:str }) => `((Zag.Ty.prim $name : Zag.Ty))
  | `(ty% { var($idx:term) }) => `((Zag.Ty.var (($idx : Nat)) : Zag.Ty))
  | `(ty% { option($ty:zagTy) }) => `((Zag.Ty.option (ty% { $ty }) : Zag.Ty))
  | `(ty% { m($ty:zagTy) }) => `((Zag.Ty.m (ty% { $ty }) : Zag.Ty))
  | `(ty% { union[$tys:zagTy,*] }) => `((Zag.Ty.union [ $[(ty% { $tys })],* ] : Zag.Ty))
  | `(ty% { struct[$tys:zagTy,*] }) => `((Zag.Ty.struct [ $[(ty% { $tys })],* ] : Zag.Ty))
  | `(ty% { func[$args:zagTy,*] => $ret:zagTy }) =>
      `((Zag.Ty.func [ $[(ty% { $args })],* ] (ty% { $ret }) : Zag.Ty))
  | `(ty% { ($ty:zagTy) }) => `(ty% { $ty })
  | `(term% { $body:zagTerm }) => `(zagTerm% $body)
  | `(zagTerm% raw($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% term($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% prim($value:term : $ty:zagTy)) =>
      `(Zag.Term.prim (ty% { $ty }) (($value : Zag.Ty.type _ (ty% { $ty }))))
  | `(zagTerm% func($name:ident)) => `(Zag.Term.primFunc (zagName% $name))
  | `(zagTerm% func($name:str)) => `(Zag.Term.primFunc $name)
  | `(zagTerm% var($idx:term)) => `(Zag.Term.var (($idx : Nat)))
  | `(zagTerm% call $fn:zagTerm [ $args:zagTerm,* ]) =>
      `(Zag.Term.app (zagTerm% $fn) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% op $name:str [ $args:zagTerm,* ]) =>
      `(Zag.Term.op $name [ $[(zagTerm% $args)],* ])
  | `(zagTerm% recurse $resultTy:zagTy from $init:zagTerm { $body:zagTerm }) =>
      `(Zag.Term.recurse (ty% { $resultTy }) (zagTerm% $init) (zagTerm% $body))
  | `(zagTerm% mkStruct[$tys:zagTy,*]) =>
      `(Zag.Term.mkStruct [ $[(ty% { $tys })],* ])
  | `(zagTerm% struct[$tys:zagTy,*] [ $fields:zagTerm,* ]) =>
      `(Zag.Term.app (Zag.Term.mkStruct [ $[(ty% { $tys })],* ]) [ $[(zagTerm% $fields)],* ])
  | `(zagTerm% ($term:zagTerm)) => `(zagTerm% $term)

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

/- Everything a `Term` is interpreted against, packed together so it can be threaded as one value
  rather than three: the primitive types, the primitive functions over them, and the operators.
  The later fields depend on the earlier `primCtx`. -/
structure Ctx where
  primCtx : PrimitiveCtx
  primFuncCtx : PrimFuncCtx primCtx
  opCtx : OpCtx primCtx

/- monad used to interpret `Ty.m` in this context -/
abbrev Ctx.M (ctx : Ctx) : Type → Type := ctx.primCtx.M

/- `hasType Δ Γ t T` means `Γ ⊢ t : T` under the primitive context `Δ` and primitive function context `δ`
  which we denote as `Δ, δ ⊨ (Γ ⊢ t : T)` or `Δ, δ ⊨ Γ ⊢ t : T`

  `hasType` will never be true if the `ty : Ty` contains vars.
  `Ty` with vars are only used for Zag propositions.
-/
inductive Term.hasType (ctx : Ctx) : VarCtx → Term ctx.primCtx → Ty → Prop where
| prim {varCtx} {ty : Ty} (val : Ty.type ctx.primCtx ty) :
    hasType ctx varCtx (.prim ty val) ty
| primFunc {varCtx} {idx : Fin ctx.primFuncCtx.length} : hasType ctx varCtx (.primFunc ctx.primFuncCtx[idx].1) ctx.primFuncCtx[idx].2.ty
| var {varCtx} {idx : Fin varCtx.length} {ty : Ty} (h : varCtx.get idx = ty) : hasType ctx varCtx (.var idx) ty
| op {varCtx} {name : String} {args : List (Term ctx.primCtx)} {tys : List Ty} {r : Ty}
    (hargs₁ : args.length = tys.length)
    (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] tys[idx])
    (hout : ctx.opCtx.outTy? name tys = some r) :
    hasType ctx varCtx (.op name args) r
| app {varCtx} {f : Term ctx.primCtx} {fTy : Ty} {args : List (Term ctx.primCtx)} {argsTy : List Ty}
  (hf : hasType ctx varCtx f (.func argsTy fTy))
  (hargs₁ : args.length = argsTy.length)
  (hargs₂ : ∀ idx : Fin args.length, hasType ctx varCtx args[idx] argsTy[idx]) : hasType ctx varCtx (.app f args) fTy
| mkStruct {varCtx} {tys : List Ty} :
    hasType ctx varCtx (.mkStruct tys) (.func tys (.struct tys))
| structProj {varCtx} {tys : List Ty} (idx : Fin tys.length) :
    hasType ctx varCtx (.structProj tys idx) (.func [.struct tys] tys[idx])
| recurse {varCtx}
    {stateTy resultTy : Ty}
    {init body : Term ctx.primCtx}
    (hinit : hasType ctx varCtx init stateTy)
    (hbody : hasType ctx
              (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy) :
    hasType ctx varCtx (.recurse resultTy init body) resultTy

/- a `Term` of a particular `ty : Ty` under some context and variable context -/
abbrev TermOf (ctx : Ctx) (varCtx : VarCtx) (ty : Ty) :=
  { term : Term ctx.primCtx // term.hasType ctx varCtx ty }
