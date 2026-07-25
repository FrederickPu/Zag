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

/- all types from the metatheory `Zag` considers to be primitives -/
abbrev PrimitiveCtx := List (String × Type)

def PrimitiveCtx.get? (primCtx : PrimitiveCtx) (primName : String) : Option Type :=
  if primName = "Nat" then some Nat
  else if primName = "Bool" then some Bool
  else (primCtx.find? (·.1 = primName)).map (·.2)

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
termination_by ty => ty
decreasing_by
  all_goals
    simp only [Fin.getElem_fin, Ty.option.sizeOf_spec, Ty.union.sizeOf_spec,
               Ty.struct.sizeOf_spec, Ty.func.sizeOf_spec]
    first
      | omega
      | (have := List.sizeOf_lt_of_mem (List.getElem_mem idx.isLt); omega)

namespace Ty

def ofNat (primCtx : PrimitiveCtx) (n : Nat) : Ty.type primCtx (.prim "Nat") :=
  cast (by simp [Ty.type.eq_2, PrimitiveCtx.get?] : Nat = Ty.type primCtx (.prim "Nat")) n

def toNat (primCtx : PrimitiveCtx) (v : Ty.type primCtx (.prim "Nat")) : Nat :=
  cast (by simp [Ty.type.eq_2, PrimitiveCtx.get?] : Ty.type primCtx (.prim "Nat") = Nat) v

def ofBool (primCtx : PrimitiveCtx) (b : Bool) : Ty.type primCtx (.prim "Bool") :=
  cast (by simp [Ty.type.eq_2, PrimitiveCtx.get?] : Bool = Ty.type primCtx (.prim "Bool")) b

def toBool (primCtx : PrimitiveCtx) (v : Ty.type primCtx (.prim "Bool")) : Bool :=
  cast (by simp [Ty.type.eq_2, PrimitiveCtx.get?] : Ty.type primCtx (.prim "Bool") = Bool) v

end Ty

structure Val (primCtx : PrimitiveCtx) where
  ty : Ty
  val : Ty.type primCtx ty

/- A user-defined fixed-arity operator. `out` maps operand types to `some` result type when
  supported or `none` otherwise; `interp` evaluates them, returning `none` when undefined. -/
structure Op (primCtx : PrimitiveCtx) where
  arity : Nat
  out : (Fin arity → Ty) → Option Ty
  interp : {tys : Fin arity → Ty} → {r : Ty} → out tys = some r →
    List (Val primCtx) → Option (Ty.type primCtx r)

/- operator context: named operators, looked up the way `PrimFuncCtx` looks up functions -/
abbrev OpCtx (primCtx : PrimitiveCtx) := List (String × Op primCtx)

/- Infer an operator's output type. `eq` is built in for matching types; `lt` and `gt` must
  exist in the context but always return `Bool`; other operators use their declared `out`. -/
def OpCtx.outTy? {primCtx : PrimitiveCtx} (opCtx : OpCtx primCtx)
    (name : String) (tys : List Ty) : Option Ty :=
  if name = "eq" then
    match tys with
    | [p, q] => if p = q then some (.prim "Bool") else none
    | _ => none
  else
    let op? : Option (Op primCtx) := (opCtx.find? (·.1 = name)).map (·.2)
    match op? with
    | some op =>
        if h : tys.length = op.arity then
          let f : Fin op.arity → Ty := fun i => tys.get (i.cast h.symm)
          if name = "lt" ∨ name = "gt" then (op.out f).map (fun _ => .prim "Bool")
          else op.out f
        else none
    | none => none

/- apply an operator to operand values, mirroring how `.op` is evaluated -/
def Op.applyVals {primCtx : PrimitiveCtx} (op : Op primCtx) (vals : List (Val primCtx)) :
    Option (Val primCtx) :=
  if h : vals.length = op.arity then
    let tys : Fin op.arity → Ty := fun i => (vals.get (i.cast h.symm)).ty
    match hout : op.out tys with
    | some r => (Val.mk r) <$> op.interp hout vals
    | none => none
  else none

inductive Term (primCtx : PrimitiveCtx) where
/- primitive value tagged with its Zag type -/
| prim (ty : Ty) : Ty.type primCtx ty → Term primCtx
/- primitive function -/
| primFunc : String → Term primCtx
/- debrujin index of variable -/
| var : Nat → Term primCtx
| app : Term primCtx → List (Term primCtx) → Term primCtx
/- application of a named n-ary operator over primitive values (see `Op`);
  the comparisons `eq`/`lt`/`gt` are binary operators -/
| op : String → List (Term primCtx) → Term primCtx
/- struct constructor function for a concrete list of field types -/
| mkStruct : List Ty → Term primCtx
/- field projection function for a concrete struct type -/
| structProj : (tys : List Ty) → Fin tys.length → Term primCtx
/- conditional branch; the condition must have primitive Bool type -/
| ite : Term primCtx → Term primCtx → Term primCtx → Term primCtx
| recurse
  /- `resultTy : Ty` -/
  (resultTy : Ty)
  /- `initState : stateTy` -/
  (initState : Term primCtx)
  /- `body : stateTy → (motive : stateTy → resultTy) → resultTy` -/
  (body : Term primCtx) : Term primCtx

namespace Term

def nat {primCtx : PrimitiveCtx} (n : Nat) : Term primCtx :=
  .prim (.prim "Nat") (Ty.ofNat primCtx n)

def bool {primCtx : PrimitiveCtx} (b : Bool) : Term primCtx :=
  .prim (.prim "Bool") (Ty.ofBool primCtx b)

def natLit? {primCtx : PrimitiveCtx} : (term : Term primCtx) → Option { n : Nat // term = Term.nat n }
| .prim (.prim "Nat") val =>
    some ⟨Ty.toNat primCtx val, by
      simp [Term.nat, Ty.ofNat, Ty.toNat]⟩
| _ => none

@[simp] theorem natLit?_nat {primCtx : PrimitiveCtx} (n : Nat) :
    natLit? (Term.nat (primCtx := primCtx) n) = some ⟨n, rfl⟩ := by
  simp [natLit?, Term.nat, Ty.ofNat, Ty.toNat]

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
syntax "union[" zagTy,* "]" : zagTy
syntax "struct[" zagTy,* "]" : zagTy
syntax "func[" zagTy,* "]" "=>" zagTy : zagTy
syntax "(" zagTy ")" : zagTy

syntax "raw(" term ")" : zagTerm
syntax "term(" term ")" : zagTerm
syntax "prim(" term ":" zagTy ")" : zagTerm
syntax "nat(" term ")" : zagTerm
syntax "bool(" term ")" : zagTerm
syntax "func(" ident ")" : zagTerm
syntax "func(" str ")" : zagTerm
syntax "var(" term ")" : zagTerm
syntax "call" zagTerm "[" zagTerm,* "]" : zagTerm
syntax "op" str "[" zagTerm,* "]" : zagTerm
syntax "primEq" zagTerm zagTerm : zagTerm
syntax "primLt" zagTerm zagTerm : zagTerm
syntax "primGt" zagTerm zagTerm : zagTerm
syntax "if" zagTerm "{" zagTerm "}" "else" "{" zagTerm "}" : zagTerm
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
  | `(zagTerm% nat($value:term)) => `(Zag.Term.nat (($value : Nat)))
  | `(zagTerm% bool($value:term)) => `(Zag.Term.bool (($value : Bool)))
  | `(zagTerm% func($name:ident)) => `(Zag.Term.primFunc (zagName% $name))
  | `(zagTerm% func($name:str)) => `(Zag.Term.primFunc $name)
  | `(zagTerm% var($idx:term)) => `(Zag.Term.var (($idx : Nat)))
  | `(zagTerm% call $fn:zagTerm [ $args:zagTerm,* ]) =>
      `(Zag.Term.app (zagTerm% $fn) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% op $name:str [ $args:zagTerm,* ]) =>
      `(Zag.Term.op $name [ $[(zagTerm% $args)],* ])
  | `(zagTerm% primEq $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "eq" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% primLt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "lt" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% primGt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "gt" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% if $cond:zagTerm { $thenTerm:zagTerm } else { $elseTerm:zagTerm }) =>
      `(Zag.Term.ite (zagTerm% $cond) (zagTerm% $thenTerm) (zagTerm% $elseTerm))
  | `(zagTerm% recurse $resultTy:zagTy from $init:zagTerm { $body:zagTerm }) =>
      `(Zag.Term.recurse (ty% { $resultTy }) (zagTerm% $init) (zagTerm% $body))
  | `(zagTerm% mkStruct[$tys:zagTy,*]) =>
      `(Zag.Term.mkStruct [ $[(ty% { $tys })],* ])
  | `(zagTerm% struct[$tys:zagTy,*] [ $fields:zagTerm,* ]) =>
      `(Zag.Term.app (Zag.Term.mkStruct [ $[(ty% { $tys })],* ]) [ $[(zagTerm% $fields)],* ])
  | `(zagTerm% ($term:zagTerm)) => `(zagTerm% $term)

/- Zag propositions (first order statements about terms and types)
  note that the debrujin indexes for varTy and varTerm are tracked seperately -/
inductive Pr (primCtx : PrimitiveCtx) where
/- include a ctx so that Zag propositions can talk about bound vars
  without needing to reason about a lambda style funcion type directly -/
| eq (ctx : List Ty) (ty : Ty) : Term primCtx → Term primCtx → Pr primCtx
| hasType (ctx : List Ty) : Term primCtx → Ty → Pr primCtx
| and : Pr primCtx → Pr primCtx → Pr primCtx
| or : Pr primCtx → Pr primCtx → Pr primCtx
| implies : Pr primCtx → Pr primCtx → Pr primCtx
/- quantify over Ty -/
| forallTy : Pr primCtx → Pr primCtx
/- quantify over Term -/
| forallTerm : Pr primCtx → Pr primCtx

namespace Pr

def forallTermOfType {primCtx : PrimitiveCtx} (boundIdx : Nat) (ty : Ty) (body : Pr primCtx) : Pr primCtx :=
  .forallTerm (.implies (.hasType [] (.var boundIdx) ty) body)

def forallNat {primCtx : PrimitiveCtx} (boundIdx : Nat) (body : Pr primCtx) : Pr primCtx :=
  forallTermOfType boundIdx (.prim "Nat") body

end Pr

structure PrimFunc (primCtx : PrimitiveCtx) where
  args : List String
  out : String
  hprim : out::args ⊆ primCtx.map (·.1)
  interp : List (Val primCtx) → Option (Val primCtx)

def PrimFunc.ty {primCtx} (pfunc : PrimFunc primCtx) : Ty :=
  (.func (pfunc.args.map (.prim ·)) (.prim pfunc.out))

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
| ite {varCtx} {cond thenTerm elseTerm : Term ctx.primCtx} {ty : Ty}
    (hcond : hasType ctx varCtx cond (.prim "Bool"))
    (hthen : hasType ctx varCtx thenTerm ty)
    (helse : hasType ctx varCtx elseTerm ty) :
    hasType ctx varCtx (.ite cond thenTerm elseTerm) ty
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
