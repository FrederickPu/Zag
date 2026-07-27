import Zag.Theory

namespace Zag

namespace Peano

abbrev NatTy : Ty := .prim "Nat"
abbrev BoolTy : Ty := .prim "Bool"

class Types (primCtx : PrimitiveCtx) : Prop where
  natType : primCtx.get? "Nat" = some Nat
  boolType : primCtx.get? "Bool" = some Bool

end Peano

namespace Ty

def ofNat (primCtx : PrimitiveCtx) [Peano.Types primCtx] (n : Nat) :
    Ty.type primCtx Peano.NatTy :=
  cast (by
    rw [Ty.type.eq_2, Peano.Types.natType]
    rfl : Nat = Ty.type primCtx Peano.NatTy) n

def toNat (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (v : Ty.type primCtx Peano.NatTy) : Nat :=
  cast (by
    rw [Ty.type.eq_2, Peano.Types.natType]
    rfl : Ty.type primCtx Peano.NatTy = Nat) v

def ofBool (primCtx : PrimitiveCtx) [Peano.Types primCtx] (b : Bool) :
    Ty.type primCtx Peano.BoolTy :=
  cast (by
    rw [Ty.type.eq_2, Peano.Types.boolType]
    rfl : Bool = Ty.type primCtx Peano.BoolTy) b

def toBool (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (v : Ty.type primCtx Peano.BoolTy) : Bool :=
  cast (by
    rw [Ty.type.eq_2, Peano.Types.boolType]
    rfl : Ty.type primCtx Peano.BoolTy = Bool) v

@[simp] theorem toBool_ofBool (primCtx : PrimitiveCtx) [Peano.Types primCtx] (b : Bool) :
    toBool primCtx (ofBool primCtx b) = b := by
  simp [toBool, ofBool]

@[simp] theorem toNat_ofNat (primCtx : PrimitiveCtx) [Peano.Types primCtx] (n : Nat) :
    toNat primCtx (ofNat primCtx n) = n := by
  simp [toNat, ofNat]

end Ty

namespace Val

def nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) : Val primCtx :=
  .mk Peano.NatTy (Ty.ofNat primCtx n)

def bool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) : Val primCtx :=
  .mk Peano.BoolTy (Ty.ofBool primCtx b)

def asNat? {primCtx : PrimitiveCtx} [Peano.Types primCtx] (v : Val primCtx) : Option Nat := do
  let raw ← v.as? Peano.NatTy
  some (Ty.toNat primCtx raw)

def asBool? {primCtx : PrimitiveCtx} [Peano.Types primCtx] (v : Val primCtx) : Option Bool := do
  let raw ← v.as? Peano.BoolTy
  some (Ty.toBool primCtx raw)

def primEq? {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (lhs rhs : Val primCtx) : Option Bool :=
  match lhs.asNat?, rhs.asNat? with
  | some lhs, some rhs => some (decide (lhs = rhs))
  | _, _ =>
      match lhs.asBool?, rhs.asBool? with
      | some lhs, some rhs => some (decide (lhs = rhs))
      | _, _ => none

def primLt? {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (lhs rhs : Val primCtx) : Option Bool :=
  match lhs.asNat?, rhs.asNat? with
  | some lhs, some rhs => some (decide (lhs < rhs))
  | _, _ =>
      match lhs.asBool?, rhs.asBool? with
      | some lhs, some rhs => some (decide (lhs = false ∧ rhs = true))
      | _, _ => none

def primGt? {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (lhs rhs : Val primCtx) : Option Bool :=
  Val.primLt? rhs lhs

@[simp] theorem asNat?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    (Val.nat (primCtx := primCtx) n).asNat? = some n := by
  simp [asNat?, nat, Ty.toNat, Ty.ofNat]

@[simp] theorem asBool?_bool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) :
    (Val.bool (primCtx := primCtx) b).asBool? = some b := by
  simp [asBool?, bool, Ty.toBool, Ty.ofBool]

@[simp] theorem as?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    (Val.nat (primCtx := primCtx) n).as? Peano.NatTy = some (Ty.ofNat primCtx n) := by
  simp [nat]

@[simp] theorem as?_bool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) :
    (Val.bool (primCtx := primCtx) b).as? Peano.BoolTy = some (Ty.ofBool primCtx b) := by
  simp [bool]

@[simp] theorem mk_ofNat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    (Val.mk Peano.NatTy (Ty.ofNat primCtx n) : Val primCtx) = Val.nat n := rfl

@[simp] theorem mk_ofBool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) :
    (Val.mk Peano.BoolTy (Ty.ofBool primCtx b) : Val primCtx) = Val.bool b := rfl

end Val

namespace Op

def compareOut? : List Ty → Option Ty
| [a, b] => if a = b then some Peano.BoolTy else none
| _ => none

def compare {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (cmp : Val primCtx → Val primCtx → Option Bool) : Op primCtx where
  arity := 2
  out tys := if tys 0 = tys 1 then some Peano.BoolTy else none
  body := .next true fun
    | none => .fail
    | some lhs => .next true fun
        | none => .fail
        | some rhs =>
            if lhs.ty = rhs.ty then
              match cmp lhs rhs with
              | none => .fail
              | some result => .done (Val.bool result)
            else .fail

theorem applyVals_compare {primCtx : PrimitiveCtx} [Peano.Types primCtx]
    (cmp : Val primCtx → Val primCtx → Option Bool) (va vb : Val primCtx)
    (hty : va.ty = vb.ty) :
    Op.applyVals (compare cmp) [va, vb] = (cmp va vb).map Val.bool := by
  simp [Op.applyVals, Op.Body.applyVals, compare, hty]
  cases cmp va vb <;> simp [Op.Body.applyVals]

def eq {primCtx : PrimitiveCtx} [Peano.Types primCtx] : Op primCtx :=
  compare Val.primEq?

@[simp] private def iteShape? (condTy thenTy elseTy : Ty) :
    Option {ty : Ty // Peano.BoolTy = condTy ∧ ty = thenTy ∧ ty = elseTy} :=
  if h : condTy = Peano.BoolTy ∧ thenTy = elseTy then
    some ⟨thenTy, h.1.symm, rfl, h.2⟩
  else none

def ite {primCtx : PrimitiveCtx} [Peano.Types primCtx] : Op primCtx :=
  { arity := 3
    out := fun tys => (iteShape? (tys 0) (tys 1) (tys 2)).map Subtype.val
    body := .next true fun
      | none => .fail
      | some conditionVal =>
          match conditionVal.as? Peano.BoolTy with
          | none => .fail
          | some condition =>
              let chooseThen := Ty.toBool primCtx condition
              .next chooseThen fun thenVal =>
                .next (!chooseThen) fun elseVal =>
                  match if chooseThen then thenVal else elseVal with
                  | some value => .done value
                  | none => .fail }

end Op

def Peano.opCtx (primCtx : PrimitiveCtx) [Peano.Types primCtx] : OpCtx primCtx :=
  [("eq", Op.eq), ("lt", Op.compare Val.primLt?), ("gt", Op.compare Val.primGt?),
   ("ite", Op.ite)]

namespace Peano

class Model (ctx : Ctx) : Prop extends Types ctx.primCtx where
  eqOp : ctx.opCtx.get? "eq" = some Op.eq
  ltOp : ctx.opCtx.get? "lt" = some (Op.compare Val.primLt?)
  gtOp : ctx.opCtx.get? "gt" = some (Op.compare Val.primGt?)
  iteOp : ctx.opCtx.get? "ite" = some Op.ite

end Peano

namespace Term

def nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) : Term primCtx :=
  .prim Peano.NatTy (Ty.ofNat primCtx n)

def bool {primCtx : PrimitiveCtx} [Peano.Types primCtx] (b : Bool) : Term primCtx :=
  .prim Peano.BoolTy (Ty.ofBool primCtx b)

def ite {primCtx : PrimitiveCtx} (cond thenTerm elseTerm : Term primCtx) : Term primCtx :=
  .op "ite" [cond, thenTerm, elseTerm]

def natLit? {primCtx : PrimitiveCtx} [Peano.Types primCtx] :
    (term : Term primCtx) → Option { n : Nat // term = Term.nat n }
| .prim (.prim "Nat") val =>
    some ⟨Ty.toNat primCtx val, by simp [Term.nat, Ty.ofNat, Ty.toNat]⟩
| _ => none

@[simp] theorem natLit?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    natLit? (Term.nat (primCtx := primCtx) n) = some ⟨n, rfl⟩ := by
  simp [natLit?, Term.nat, Ty.ofNat, Ty.toNat]

end Term

def Pr.forallNat {primCtx : PrimitiveCtx} (boundIdx : Nat) (body : Pr (Term primCtx)) :
    Pr (Term primCtx) :=
  Pr.forallTermOfType boundIdx Peano.NatTy body

theorem Term.hasType.ite {ctx : Ctx} [Peano.Model ctx]
    {varCtx : VarCtx} {cond thenTerm elseTerm : Term ctx.primCtx} {ty : Ty}
    (hcond : Term.hasType ctx varCtx cond Peano.BoolTy)
    (hthen : Term.hasType ctx varCtx thenTerm ty)
    (helse : Term.hasType ctx varCtx elseTerm ty) :
    Term.hasType ctx varCtx (Term.ite cond thenTerm elseTerm) ty := by
  refine Term.hasType.op (tys := [Peano.BoolTy, ty, ty]) rfl ?_ ?_
  · intro idx
    match idx with
    | ⟨0, _⟩ => simpa using hcond
    | ⟨1, _⟩ => simpa using hthen
    | ⟨2, _⟩ => simpa using helse
    | ⟨n + 3, h⟩ =>
      have : False := by
        change n + 3 < 3 at h
        omega
      contradiction
  · unfold OpCtx.outTy?
    rw [Peano.Model.iteOp]
    simp [Op.ite, Op.iteShape?]

theorem Term.evalGo_op_compare {ctx : Ctx} [Peano.Types ctx.primCtx]
    {motives : List (Term.MotiveCtx ctx.primCtx)} {env : List (Val ctx.primCtx)}
    {name : String} {a b : Term ctx.primCtx}
    {cmp : Val ctx.primCtx → Val ctx.primCtx → Option Bool} {va vb : Val ctx.primCtx}
    (hop : ctx.opCtx.get? name = some (Op.compare cmp))
    (ha : Term.evalGo ctx motives env a = some va)
    (hb : Term.evalGo ctx motives env b = some vb) (hty : va.ty = vb.ty) :
    Term.evalGo ctx motives env (.op name [a, b]) =
      (cmp va vb).map Val.bool := by
  rw [Term.evalGo.eq_def]
  simp [hop, Op.compare, ha, hb, hty]
  cases cmp va vb <;> simp

theorem Term.evalGo_ite {ctx : Ctx} [Peano.Model ctx]
    (motives : List (Term.MotiveCtx ctx.primCtx)) (env : List (Val ctx.primCtx))
    (cond thenTerm elseTerm : Term ctx.primCtx) :
    Term.evalGo ctx motives env (Term.ite cond thenTerm elseTerm) = (do
      let conditionVal ← Term.evalGo ctx motives env cond
      let condition ← conditionVal.as? Peano.BoolTy
      if Ty.toBool ctx.primCtx condition then
        Term.evalGo ctx motives env thenTerm
      else
        Term.evalGo ctx motives env elseTerm) := by
  cases hcond : Term.evalGo ctx motives env cond with
  | none =>
      rw [Term.evalGo.eq_def]
      simp [Term.ite, Peano.Model.iteOp, Op.ite, hcond]
  | some value =>
      cases hvalue : value.as? Peano.BoolTy with
      | none =>
          rw [Term.evalGo.eq_def]
          simp [Term.ite, Peano.Model.iteOp, Op.ite, hcond, hvalue]
      | some condition =>
          cases hcondition : Ty.toBool ctx.primCtx condition <;>
            rw [Term.evalGo.eq_def] <;>
            simp [Term.ite, Peano.Model.iteOp, Op.ite, hcond, hvalue, hcondition]

syntax "nat(" term ")" : zagTerm
syntax "bool(" term ")" : zagTerm
syntax "primEq" zagTerm zagTerm : zagTerm
syntax "primLt" zagTerm zagTerm : zagTerm
syntax "primGt" zagTerm zagTerm : zagTerm
syntax "if" zagTerm "{" zagTerm "}" "else" "{" zagTerm "}" : zagTerm

macro_rules
  | `(zagTerm% nat($value:term)) => `(Zag.Term.nat (($value : Nat)))
  | `(zagTerm% bool($value:term)) => `(Zag.Term.bool (($value : Bool)))
  | `(zagTerm% primEq $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "eq" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% primLt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "lt" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% primGt $lhs:zagTerm $rhs:zagTerm) =>
      `(Zag.Term.op "gt" [(zagTerm% $lhs), (zagTerm% $rhs)])
  | `(zagTerm% if $cond:zagTerm { $thenTerm:zagTerm } else { $elseTerm:zagTerm }) =>
      `(Zag.Term.ite (zagTerm% $cond) (zagTerm% $thenTerm) (zagTerm% $elseTerm))

namespace Lib.Peano

abbrev natCtx : PrimitiveCtx := .ofPrims [.of "Nat" Nat, .of "Bool" Bool]
abbrev NatTy : Ty := Zag.Peano.NatTy

instance : Peano.Types natCtx where
  natType := by rfl
  boolType := by rfl

def natBinaryFunc (f : Nat → Nat → Nat) : PrimFunc natCtx where
  args := ["Nat", "Nat"]
  out := "Nat"
  hprim := by simp_all
  interp
  | [lhsVal, rhsVal] => do
      let lhs ← lhsVal.asNat?
      let rhs ← rhsVal.asNat?
      some (Val.nat (f lhs rhs))
  | _ => none

def succFunc : PrimFunc natCtx where
  args := ["Nat"]
  out := "Nat"
  hprim := by simp_all
  interp
  | [v] => do
      let n ← v.asNat?
      some (Val.nat (n + 1))
  | _ => none

def natFuncCtx : PrimFuncCtx natCtx :=
  [("add", natBinaryFunc Nat.add), ("sub", natBinaryFunc Nat.sub),
   ("mul", natBinaryFunc Nat.mul), ("div", natBinaryFunc Nat.div), ("succ", succFunc)]

def natOpCtx : OpCtx natCtx :=
  Peano.opCtx natCtx

abbrev peanoCtx : Ctx where
  primCtx := natCtx
  primFuncCtx := natFuncCtx
  opCtx := natOpCtx

instance : Peano.Model peanoCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl

end Lib.Peano

end Zag
