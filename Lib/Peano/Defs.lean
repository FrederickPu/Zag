import Zag.Theory
import Zag.Syntax

namespace Zag

namespace Peano

abbrev NatTy : Ty := .prim "Nat" []
abbrev BoolTy : Ty := .prim "Bool" []

class Types (primCtx : PrimitiveCtx) : Prop where
  natType : primCtx.get? "Nat" = some Nat
  boolType : primCtx.get? "Bool" = some Bool

end Peano

namespace Ty

def ofNat (primCtx : PrimitiveCtx) [Peano.Types primCtx] (n : Nat) :
    Ty.type primCtx Peano.NatTy :=
  cast (Ty.type_ground (Peano.Types.natType (primCtx := primCtx))).symm n

def toNat (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (v : Ty.type primCtx Peano.NatTy) : Nat :=
  cast (Ty.type_ground (Peano.Types.natType (primCtx := primCtx))) v

def ofBool (primCtx : PrimitiveCtx) [Peano.Types primCtx] (b : Bool) :
    Ty.type primCtx Peano.BoolTy :=
  cast (Ty.type_ground (Peano.Types.boolType (primCtx := primCtx))).symm b

def toBool (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (v : Ty.type primCtx Peano.BoolTy) : Bool :=
  cast (Ty.type_ground (Peano.Types.boolType (primCtx := primCtx))) v

@[simp] theorem toBool_ofBool (primCtx : PrimitiveCtx) [Peano.Types primCtx] (b : Bool) :
    toBool primCtx (ofBool primCtx b) = b := by
  simp [toBool, ofBool]

@[simp] theorem toNat_ofNat (primCtx : PrimitiveCtx) [Peano.Types primCtx] (n : Nat) :
    toNat primCtx (ofNat primCtx n) = n := by
  simp [toNat, ofNat]

@[simp] theorem toNat_cast_ofNat (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (h : Ty.type primCtx Peano.NatTy = Ty.type primCtx Peano.NatTy) (n : Nat) :
    toNat primCtx (cast h (ofNat primCtx n)) = n := by
  rw [Subsingleton.elim h rfl]
  exact toNat_ofNat primCtx n

@[simp] theorem toBool_cast_ofBool (primCtx : PrimitiveCtx) [Peano.Types primCtx]
    (h : Ty.type primCtx Peano.BoolTy = Ty.type primCtx Peano.BoolTy) (b : Bool) :
    toBool primCtx (cast h (ofBool primCtx b)) = b := by
  rw [Subsingleton.elim h rfl]
  exact toBool_ofBool primCtx b

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

def compare {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx]
    (cmp : Val primCtx → Val primCtx → Option Bool) : Op primCtx M :=
  Op.fixed 2 (fun tys => if tys 0 = tys 1 then some Peano.BoolTy else none) (.next true fun
    | none => .fail
    | some lhs => .next true fun
        | none => .fail
        | some rhs =>
            if lhs.ty = rhs.ty then
              match cmp lhs rhs with
              | none => .fail
              | some result => .done (Val.bool result)
            else .fail)

theorem applyVals_compare {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx]
    (name : String) (cmp : Val primCtx → Val primCtx → Option Bool) (va vb : Val primCtx)
    (hty : va.ty = vb.ty) :
    Op.applyValsAt (M := M) name (compare cmp) [va, vb] = (cmp va vb).map Val.bool := by
  simp [Op.applyValsAt, Op.fixed, Op.Body.applyVals, compare, hty]
  cases cmp va vb <;> simp [Op.Body.applyVals]

def eq {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx] : Op primCtx M :=
  compare Val.primEq?

@[simp] private def iteShape? (condTy thenTy elseTy : Ty) :
    Option {ty : Ty // Peano.BoolTy = condTy ∧ ty = thenTy ∧ ty = elseTy} :=
  if h : condTy = Peano.BoolTy ∧ thenTy = elseTy then
    some ⟨thenTy, h.1.symm, rfl, h.2⟩
  else none

def ite {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx] : Op primCtx M :=
  Op.fixed 3 (fun tys => (iteShape? (tys 0) (tys 1) (tys 2)).map Subtype.val)
    (.next true fun
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
                  | none => .fail)

/- The arithmetic that used to be supplied as primitive functions. A primitive function is now
  just an operator with fixed operand and result types. -/
def natBinary {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx]
    (f : Nat → Nat → Nat) : Op primCtx M :=
  Op.ofVals [Peano.NatTy, Peano.NatTy] Peano.NatTy fun
  | [lhsVal, rhsVal] => do
      let lhs ← lhsVal.asNat?
      let rhs ← rhsVal.asNat?
      some (Val.nat (f lhs rhs))
  | _ => none

def natUnary {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx]
    (f : Nat → Nat) : Op primCtx M :=
  Op.ofVals [Peano.NatTy] Peano.NatTy fun
  | [v] => do
      let n ← v.asNat?
      some (Val.nat (f n))
  | _ => none

/- The typing rule for continuation-passing `while`. The first two operands are the condition and
  body blocks; the remaining operands are the loop state. -/
def whileResultTy? [Peano.Types primCtx] : List Ty → Option Ty
| .func condArgs condOut :: .func bodyArgs bodyOut :: stateTys =>
    match stateTys.head? with
    | none => none
    | some resultTy =>
        if condArgs = stateTys ∧ condOut = Peano.BoolTy ∧
            bodyArgs = stateTys ++ [.func stateTys resultTy] ∧ bodyOut = resultTy then
          some resultTy
        else none
| _ => none

def whileAfterCondition [Peano.Types primCtx] (name : String)
    (condition body : Val primCtx) (state : List (Val primCtx)) (resultTy : Ty)
    (currentResult conditionResult : Val primCtx) : Op.Body primCtx :=
  match conditionResult.asBool? with
  | some false => .done currentResult
  | some true =>
      let stateTys := state.map Val.ty
      let nextIteration := Val.opRef name [condition, body] stateTys resultTy
      .apply body (state ++ [nextIteration]) .done
  | none => .fail

def whileBodyFromValues [Peano.Types primCtx] (name : String) (vals : List (Val primCtx)) :
    Op.Body primCtx :=
  (do
    let condition ← vals[0]?
    let body ← vals[1]?
    let state := vals.drop 2
    let resultTy ← whileResultTy? (primCtx := primCtx) (vals.map Val.ty)
    let currentResult ← state.head?
    some (Op.Body.apply condition state
      (whileAfterCondition name condition body state resultTy currentResult))).getD .fail

/- A single variadic `while` operator. Applying the continuation returns through the body call,
  so each iteration wraps the next one and remains compatible with the top-frame-only machine. -/
def whileOp {primCtx : PrimitiveCtx} {M : Type → Type} [Peano.Types primCtx] : Op primCtx M where
  out := whileResultTy? (primCtx := primCtx)
  body name arity :=
    if 3 ≤ arity then
      some (Op.Body.collect (whileBodyFromValues (primCtx := primCtx) name) arity [])
    else none

end Op

def Peano.opCtx (primCtx : PrimitiveCtx) {M : Type → Type} [Peano.Types primCtx] : OpCtx primCtx M :=
  [("eq", Op.eq), ("lt", Op.compare Val.primLt?), ("gt", Op.compare Val.primGt?),
   ("ite", Op.ite),
   ("add", Op.natBinary Nat.add), ("sub", Op.natBinary Nat.sub),
   ("mul", Op.natBinary Nat.mul), ("div", Op.natBinary Nat.div),
   ("succ", Op.natUnary Nat.succ), ("while", Op.whileOp)]

namespace Peano

class Model (ctx : Ctx) : Prop extends Types ctx.primCtx where
  eqOp : ctx.opCtx.get? "eq" = some Op.eq
  ltOp : ctx.opCtx.get? "lt" = some (Op.compare Val.primLt?)
  gtOp : ctx.opCtx.get? "gt" = some (Op.compare Val.primGt?)
  iteOp : ctx.opCtx.get? "ite" = some Op.ite
  addOp : ctx.opCtx.get? "add" = some (Op.natBinary Nat.add)
  subOp : ctx.opCtx.get? "sub" = some (Op.natBinary Nat.sub)
  mulOp : ctx.opCtx.get? "mul" = some (Op.natBinary Nat.mul)
  divOp : ctx.opCtx.get? "div" = some (Op.natBinary Nat.div)
  succOp : ctx.opCtx.get? "succ" = some (Op.natUnary Nat.succ)

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
| .prim (.prim "Nat" []) val =>
    some ⟨Ty.toNat primCtx val, by simp [Term.nat, Ty.ofNat, Ty.toNat]⟩
| _ => none

@[simp] theorem natLit?_nat {primCtx : PrimitiveCtx} [Peano.Types primCtx] (n : Nat) :
    natLit? (Term.nat (primCtx := primCtx) n) = some ⟨n, rfl⟩ := by
  simp [natLit?, Term.nat, Ty.ofNat, Ty.toNat]

end Term

def Pr.forallNat {primCtx : PrimitiveCtx} (name : String) (body : Pr (Term primCtx)) :
    Pr (Term primCtx) :=
  Pr.forallTermOfType name Peano.NatTy body

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
    simp [Op.ite, Op.fixed, Op.iteShape?]

/- Typing for ordinary two-operand operators through `OpCtx.outTy?`. -/
theorem Term.hasType.binOp {ctx : Ctx} {varCtx : VarCtx} {name : String}
    {a b : Term ctx.primCtx} {argTy outTy : Ty}
    (hout : ctx.opCtx.outTy? name [argTy, argTy] = some outTy)
    (ha : Term.hasType ctx varCtx a argTy)
    (hb : Term.hasType ctx varCtx b argTy) :
    Term.hasType ctx varCtx (.op name [a, b]) outTy := by
  refine Term.hasType.op (tys := [argTy, argTy]) rfl ?_ hout
  intro idx
  match idx with
  | ⟨0, _⟩ => simpa using ha
  | ⟨1, _⟩ => simpa using hb
  | ⟨n + 2, h⟩ =>
      have : False := by
        change n + 2 < 2 at h
        omega
      contradiction

theorem Term.hasType.unOp {ctx : Ctx} {varCtx : VarCtx} {name : String}
    {a : Term ctx.primCtx} {argTy outTy : Ty}
    (hout : ctx.opCtx.outTy? name [argTy] = some outTy)
    (ha : Term.hasType ctx varCtx a argTy) :
    Term.hasType ctx varCtx (.op name [a]) outTy := by
  refine Term.hasType.op (tys := [argTy]) rfl ?_ hout
  intro idx
  match idx with
  | ⟨0, _⟩ => simpa using ha
  | ⟨n + 1, h⟩ =>
      have : False := by
        change n + 1 < 1 at h
        omega
      contradiction

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

def natOpCtx : OpCtx natCtx :=
  Peano.opCtx natCtx

abbrev peanoCtx : Ctx where
  primCtx := natCtx
  opCtx := natOpCtx

instance : Peano.Model peanoCtx where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl
  addOp := by rfl
  subOp := by rfl
  mulOp := by rfl
  divOp := by rfl
  succOp := by rfl

end Lib.Peano
