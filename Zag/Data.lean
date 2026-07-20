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

inductive Term (primCtx : PrimitiveCtx) where
/- primitive value tagged with its Zag type -/
| prim (ty : Ty) : Ty.type primCtx ty → Term primCtx
/- primitive function -/
| primFunc : String → Term primCtx
/- debrujin index of variable -/
| var : Nat → Term primCtx
| app : Term primCtx → List (Term primCtx) → Term primCtx
/- comparisons for primitive values; typing enforces both operands share one primitive type -/
| primEq : Term primCtx → Term primCtx → Term primCtx
| primLt : Term primCtx → Term primCtx → Term primCtx
| primGt : Term primCtx → Term primCtx → Term primCtx
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
  | `(zagTerm% primEq $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.primEq (zagTerm% $lhs) (zagTerm% $rhs))
  | `(zagTerm% primLt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.primLt (zagTerm% $lhs) (zagTerm% $rhs))
  | `(zagTerm% primGt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.primGt (zagTerm% $lhs) (zagTerm% $rhs))
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

/- `hasType Δ Γ t T` means `Γ ⊢ t : T` under the primitive context `Δ` and primitive function context `δ`
  which we denote as `Δ, δ ⊨ (Γ ⊢ t : T)` or `Δ, δ ⊨ Γ ⊢ t : T`

  `hasType` will never be true if the `ty : Ty` contains vars.
  `Ty` with vars are only used for Zag propositions.
-/
inductive Term.hasType (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx) : VarCtx → Term primCtx → Ty → Prop where
| prim {varCtx} {ty : Ty} (val : Ty.type primCtx ty) :
    hasType primCtx primFuncCtx varCtx (.prim ty val) ty
| primFunc {varCtx} {idx : Fin primFuncCtx.length} : hasType primCtx primFuncCtx varCtx (.primFunc primFuncCtx[idx].1) primFuncCtx[idx].2.ty
| var {varCtx} {idx : Fin varCtx.length} {ty : Ty} (h : varCtx.get idx = ty) : hasType primCtx primFuncCtx varCtx (.var idx) ty
| primEq {varCtx p lhs rhs}
    (hlhs : hasType primCtx primFuncCtx varCtx lhs (.prim p))
    (hrhs : hasType primCtx primFuncCtx varCtx rhs (.prim p)) :
    hasType primCtx primFuncCtx varCtx (.primEq lhs rhs) (.prim "Bool")
| primLt {varCtx p lhs rhs}
    (hlhs : hasType primCtx primFuncCtx varCtx lhs (.prim p))
    (hrhs : hasType primCtx primFuncCtx varCtx rhs (.prim p)) :
    hasType primCtx primFuncCtx varCtx (.primLt lhs rhs) (.prim "Bool")
| primGt {varCtx p lhs rhs}
    (hlhs : hasType primCtx primFuncCtx varCtx lhs (.prim p))
    (hrhs : hasType primCtx primFuncCtx varCtx rhs (.prim p)) :
    hasType primCtx primFuncCtx varCtx (.primGt lhs rhs) (.prim "Bool")
| app {varCtx} {f : Term primCtx} {fTy : Ty} {args : List (Term primCtx)} {argsTy : List Ty}
  (hf : hasType primCtx primFuncCtx varCtx f (.func argsTy fTy))
  (hargs₁ : args.length = argsTy.length)
  (hargs₂ : ∀ idx : Fin args.length, hasType primCtx primFuncCtx varCtx args[idx] argsTy[idx]) : hasType primCtx primFuncCtx varCtx (.app f args) fTy
| mkStruct {varCtx} {tys : List Ty} :
    hasType primCtx primFuncCtx varCtx (.mkStruct tys) (.func tys (.struct tys))
| structProj {varCtx} {tys : List Ty} (idx : Fin tys.length) :
    hasType primCtx primFuncCtx varCtx (.structProj tys idx) (.func [.struct tys] tys[idx])
| ite {varCtx} {cond thenTerm elseTerm : Term primCtx} {ty : Ty}
    (hcond : hasType primCtx primFuncCtx varCtx cond (.prim "Bool"))
    (hthen : hasType primCtx primFuncCtx varCtx thenTerm ty)
    (helse : hasType primCtx primFuncCtx varCtx elseTerm ty) :
    hasType primCtx primFuncCtx varCtx (.ite cond thenTerm elseTerm) ty
| recurse {varCtx}
    {stateTy resultTy : Ty}
    {init body : Term primCtx}
    (hinit : hasType primCtx primFuncCtx varCtx init stateTy)
    (hbody : hasType primCtx primFuncCtx
              (varCtx ++ [stateTy, .func [stateTy] resultTy]) body resultTy) :
    hasType primCtx primFuncCtx varCtx (.recurse resultTy init body) resultTy

/- a `Term` of a particular `ty : Ty` under some primitive and variable context -/
abbrev TermOf (primCtx : PrimitiveCtx) (primFuncCtx : PrimFuncCtx primCtx) (varCtx : VarCtx) (ty : Ty) :=
  { term : Term primCtx // term.hasType primCtx primFuncCtx varCtx ty }
