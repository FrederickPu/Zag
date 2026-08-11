import Lang.AutoCorres.L2
import Lang.AutoCorres.CorresXF

/-!
# Word abstraction

Corresponds to [`tools/autocorres/WordAbstract.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/WordAbstract.thy).

Unsigned words abstract to `Nat` and signed words abstract to `Int`. Guards
separate C-definedness from the narrower domain on which unbounded abstraction
agrees with concrete bit patterns. In particular, unsigned wrapping is defined
by C but rejected by the `Nat` abstraction, and the pinned signed-right-shift
rule is used only for nonnegative source values.
-/

namespace Zag.Lang.AutoCorres.WordAbstract

open Zag.Lang.AutoCorres

universe u v w x y

/-- A guarded value relation, corresponding to upstream `abstract_val`. -/
def abstract_val (guard : Prop) (abstract : Abstract)
    (abstraction : Concrete → Abstract) (concrete : Concrete) : Prop :=
  guard → abstract = abstraction concrete

/-- An unconditionally related variable, corresponding to upstream `abs_var`. -/
def abs_var (abstract : Abstract) (abstraction : Concrete → Abstract)
    (concrete : Concrete) : Prop :=
  abstract_val True abstract abstraction concrete

/-- A guarded abstraction law for a result-producing binary operation. -/
def abstract_binop (guard : Abstract → Abstract → Prop)
    (abstraction : Concrete → Abstract)
    (abstractOp : Abstract → Abstract → Abstract)
    (concreteOp : Concrete → Concrete → Concrete) : Prop :=
  ∀ left right, guard (abstraction left) (abstraction right) →
    abstraction (concreteOp left right) =
      abstractOp (abstraction left) (abstraction right)

/-- A guarded abstraction law for a Boolean-valued binary operation. -/
def abstract_bool_binop (guard : Abstract → Abstract → Prop)
    (abstraction : Concrete → Abstract)
    (abstractOp : Abstract → Abstract → Bool)
    (concreteOp : Concrete → Concrete → Bool) : Prop :=
  ∀ left right, guard (abstraction left) (abstraction right) →
    concreteOp left right = abstractOp (abstraction left) (abstraction right)

/--
An explicit abstraction/concretization certificate.  Unlike an unguarded
equivalence, each round trip records exactly the domain on which it is valid.
-/
structure valid_typ_abs_fn (Abstract : Type u) (Concrete : Type v) where
  abstractGuard : Abstract → Prop
  concreteGuard : Abstract → Prop
  abstract : Concrete → Abstract
  concretize : Abstract → Concrete
  abstract_concretize : ∀ value, abstractGuard value →
    abstract (concretize value) = value
  concretize_abstract : ∀ value, concreteGuard (abstract value) →
    concretize (abstract value) = value

def product_abstraction (left : C → A) (right : D → B) : C × D → A × B :=
  fun value => (left value.1, right value.2)

def product_concretization (left : A → C) (right : B → D) : A × B → C × D :=
  fun value => (left value.1, right value.2)

/-- Identity is a total abstraction in both directions. -/
def valid_typ_abs_fn_id (α : Type u) : valid_typ_abs_fn α α where
  abstractGuard := fun _ => True
  concreteGuard := fun _ => True
  abstract := id
  concretize := id
  abstract_concretize := by simp
  concretize_abstract := by simp

/-- Product abstractions carry both component guards and round-trip laws. -/
def valid_typ_abs_fn_prod
    (left : valid_typ_abs_fn A C) (right : valid_typ_abs_fn B D) :
    valid_typ_abs_fn (A × B) (C × D) where
  abstractGuard := fun value =>
    left.abstractGuard value.1 ∧ right.abstractGuard value.2
  concreteGuard := fun value =>
    left.concreteGuard value.1 ∧ right.concreteGuard value.2
  abstract := product_abstraction left.abstract right.abstract
  concretize := product_concretization left.concretize right.concretize
  abstract_concretize := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact Prod.ext (left.abstract_concretize a ha)
      (right.abstract_concretize b hb)
  concretize_abstract := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact Prod.ext (left.concretize_abstract a ha)
      (right.concretize_abstract b hb)

/--
The exact `CorresXF` specialization used by word abstraction: states are
identical and result/exception maps do not inspect the post-state.
-/
def corresTA {State : Type u} {ConcreteResult : Type v}
    {AbstractResult : Type w} {ConcreteException : Type x}
    {AbstractException : Type y}
    (precondition : State → Prop)
    (resultMap : ConcreteResult → AbstractResult)
    (exceptionMap : ConcreteException → AbstractException)
    (abstract : L2.L2Program State AbstractException AbstractResult)
    (concrete : L2.L2Program State ConcreteException ConcreteResult) : Prop :=
  CorresXF id (fun result _ => resultMap result)
    (fun exception _ => exceptionMap exception) precondition abstract concrete

/-- Runtime-guarded refinement between the related closed L2 SSA endpoints. -/
def corresTA.toSSA
    {State ConcreteResult AbstractResult ConcreteException AbstractException : Type}
    [Repr (Except ConcreteException ConcreteResult)]
    [Repr (Except AbstractException AbstractResult)]
    {precondition : State → Prop}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {abstract : L2.L2Program State AbstractException AbstractResult}
    {concrete : L2.L2Program State ConcreteException ConcreteResult}
    (certificate : corresTA precondition resultMap exceptionMap abstract concrete) :
    SSABridge.Refinement (L2.toSSA concrete) (L2.toSSA abstract) :=
  SSABridge.Refinement.ofCorresXF id (fun result _ => resultMap result)
    (fun exception _ => exceptionMap exception) precondition certificate

/-! ## Guarded value composition -/

theorem abstract_val_trivial (abstraction : Concrete → Abstract) (value : Concrete) :
    abstract_val True (abstraction value) abstraction value := by
  simp [abstract_val]

theorem abstract_val_const (guard : Prop) (abstraction : Concrete → Abstract)
    (value : Concrete) : abstract_val guard (abstraction value) abstraction value := by
  simp [abstract_val]

theorem abstract_val_unwrap
    (condition : Prop) (value : Abstract) (concrete : Concrete)
    (abstraction : Concrete → Abstract)
    (related : abstract_val condition value abstraction concrete) :
    abstract_val condition value id (abstraction concrete) := by
  exact related

theorem abstract_val_application
    {abstractFunction concreteFunction : A → B}
    {abstractArgument concreteArgument : A}
    (functionRelated : abstract_val functionGuard abstractFunction id concreteFunction)
    (argumentRelated : abstract_val argumentGuard abstractArgument id concreteArgument) :
    abstract_val (functionGuard ∧ argumentGuard)
      (abstractFunction abstractArgument) id
      (concreteFunction concreteArgument) := by
  rintro ⟨hf, ha⟩
  have functionEq : abstractFunction = concreteFunction := by
    simpa [id] using functionRelated hf
  have argumentEq : abstractArgument = concreteArgument := by
    simpa [id] using argumentRelated ha
  simp [functionEq, argumentEq, id]

theorem abstract_binop_is_abstract_val
    {guard : Abstract → Abstract → Prop}
    {abstraction : Concrete → Abstract}
    {abstractOp : Abstract → Abstract → Abstract}
    {concreteOp : Concrete → Concrete → Concrete} :
    abstract_binop guard abstraction abstractOp concreteOp ↔
      ∀ left right, abstract_val
        (guard (abstraction left) (abstraction right))
        (abstractOp (abstraction left) (abstraction right))
        abstraction (concreteOp left right) := by
  simp [abstract_binop, abstract_val, eq_comm]

theorem abstract_expr_binop
    {operationGuard : Abstract → Abstract → Prop}
    {abstraction : Concrete → Abstract}
    {abstractOp : Abstract → Abstract → Abstract}
    {concreteOp : Concrete → Concrete → Concrete}
    (operationRelated : abstract_binop operationGuard abstraction abstractOp concreteOp)
    (leftRelated : abstract_val leftGuard left abstraction concreteLeft)
    (rightRelated : abstract_val rightGuard right abstraction concreteRight) :
    abstract_val (leftGuard ∧ rightGuard ∧ operationGuard left right)
      (abstractOp left right) abstraction (concreteOp concreteLeft concreteRight) := by
  rintro ⟨hl, hr, hop⟩
  rw [leftRelated hl, rightRelated hr] at hop ⊢
  exact (operationRelated concreteLeft concreteRight hop).symm

theorem abstract_expr_bool_binop
    {operationGuard : Abstract → Abstract → Prop}
    {abstraction : Concrete → Abstract}
    {abstractOp : Abstract → Abstract → Bool}
    {concreteOp : Concrete → Concrete → Bool}
    (operationRelated :
      abstract_bool_binop operationGuard abstraction abstractOp concreteOp)
    (leftRelated : abstract_val leftGuard left abstraction concreteLeft)
    (rightRelated : abstract_val rightGuard right abstraction concreteRight) :
    abstract_val (leftGuard ∧ rightGuard ∧ operationGuard left right)
      (abstractOp left right) id (concreteOp concreteLeft concreteRight) := by
  rintro ⟨hl, hr, hop⟩
  rw [leftRelated hl, rightRelated hr] at hop ⊢
  exact (operationRelated concreteLeft concreteRight hop).symm

/-- A guarded abstraction law for a result-producing unary operation. -/
def abstract_unop (guard : Abstract → Prop) (abstraction : Concrete → Abstract)
    (abstractOp : Abstract → Abstract) (concreteOp : Concrete → Concrete) : Prop :=
  ∀ value, guard (abstraction value) →
    abstraction (concreteOp value) = abstractOp (abstraction value)

theorem abstract_expr_unop
    {operationGuard : Abstract → Prop} {abstraction : Concrete → Abstract}
    {abstractOp : Abstract → Abstract} {concreteOp : Concrete → Concrete}
    (operationRelated : abstract_unop operationGuard abstraction abstractOp concreteOp)
    (valueRelated : abstract_val valueGuard value abstraction concreteValue) :
    abstract_val (valueGuard ∧ operationGuard value) (abstractOp value)
      abstraction (concreteOp concreteValue) := by
  rintro ⟨hv, hop⟩
  rw [valueRelated hv] at hop ⊢
  exact (operationRelated concreteValue hop).symm

/-- The right guard of `&&` is needed only when the left abstract value is true. -/
theorem abstract_val_and
    (leftRelated : abstract_val leftGuard left id concreteLeft)
    (rightRelated : abstract_val rightGuard right id concreteRight) :
    abstract_val (leftGuard ∧ (left = true → rightGuard))
      (left && right) id (concreteLeft && concreteRight) := by
  unfold abstract_val at *
  rintro ⟨hl, hr⟩
  have leftEq := leftRelated hl
  simp only [id_eq] at leftEq
  cases left with
  | false =>
      subst concreteLeft
      rfl
  | true =>
      subst concreteLeft
      simpa [id] using rightRelated (hr rfl)

/-- The right guard of `||` is needed only when the left abstract value is false. -/
theorem abstract_val_or
    (leftRelated : abstract_val leftGuard left id concreteLeft)
    (rightRelated : abstract_val rightGuard right id concreteRight) :
    abstract_val (leftGuard ∧ (left = false → rightGuard))
      (left || right) id (concreteLeft || concreteRight) := by
  unfold abstract_val at *
  rintro ⟨hl, hr⟩
  have leftEq := leftRelated hl
  simp only [id_eq] at leftEq
  cases left with
  | false =>
      subst concreteLeft
      simpa [id] using rightRelated (hr rfl)
  | true =>
      subst concreteLeft
      rfl

theorem abstract_val_prod
    {AbstractLeft ConcreteLeft AbstractRight ConcreteRight : Type}
    {leftGuard rightGuard : Prop}
    {left : AbstractLeft} {concreteLeft : ConcreteLeft}
    {right : AbstractRight} {concreteRight : ConcreteRight}
    {leftMap : ConcreteLeft → AbstractLeft}
    {rightMap : ConcreteRight → AbstractRight}
    (leftRelated : abstract_val leftGuard left leftMap concreteLeft)
    (rightRelated : abstract_val rightGuard right rightMap concreteRight) :
    abstract_val (leftGuard ∧ rightGuard) (left, right)
      (fun value : ConcreteLeft × ConcreteRight =>
        (leftMap value.1, rightMap value.2))
      (concreteLeft, concreteRight) := by
  rintro ⟨hl, hr⟩
  exact Prod.ext (leftRelated hl) (rightRelated hr)

/-! ## Generic unsigned words -/

/-- Exact maximum unsigned value at `width` bits. -/
def UWORD_MAX (width : Nat) : Nat := 2 ^ width - 1

/-- Signed two's-complement lower bound, including the degenerate zero width. -/
def SWORD_MIN (width : Nat) : Int :=
  if width = 0 then 0 else -((2 ^ (width - 1) : Nat) : Int)

/-- Signed two's-complement upper bound, including the degenerate zero width. -/
def SWORD_MAX (width : Nat) : Int :=
  if width = 0 then 0 else ((2 ^ (width - 1) : Nat) : Int) - 1

/-- Word widths supported by the upstream C scalar operation matrix. -/
inductive WordWidth where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr

def WordWidth.bits : WordWidth → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

theorem WordWidth.bits_pos (width : WordWidth) : 0 < width.bits := by
  cases width <;> decide

inductive UnsignedBinaryOp where
  | mul | div | mod | bitAnd | bitOr | bitXor
  deriving DecidableEq, Repr

inductive SignedBinaryOp where
  | add | sub | mul | tdiv | tmod | bitAnd | bitOr | bitXor
  deriving DecidableEq, Repr

inductive UnsignedUnaryOp where
  | neg | bitNot
  deriving DecidableEq, Repr

inductive SignedUnaryOp where
  | neg | bitNot
  deriving DecidableEq, Repr

inductive WordComparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive ShiftDirection where
  | left | right
  deriving DecidableEq, Repr

def unsignedBinary (operator : UnsignedBinaryOp) (left right : Nat) : Nat :=
  match operator with
  | .mul => left * right
  | .div => left / right
  | .mod => left % right
  | .bitAnd => left &&& right
  | .bitOr => left ||| right
  | .bitXor => left ^^^ right

def unsignedBinaryCDefined (operator : UnsignedBinaryOp) (_left right : Nat) : Prop :=
  match operator with | .div | .mod => right ≠ 0 | _ => True

/-- `Nat` abstraction excludes concrete unsigned wrapping; C itself permits it. -/
def unsignedBinaryAbstractable (width : Nat) (operator : UnsignedBinaryOp)
    (left right : Nat) : Prop :=
  unsignedBinary operator left right ≤ UWORD_MAX width

def unsignedBinaryGuard (width : Nat) (operator : UnsignedBinaryOp)
    (left right : Nat) : Prop :=
  unsignedBinaryCDefined operator left right ∧
    unsignedBinaryAbstractable width operator left right

theorem unsignedBinaryGuard_iff (width : Nat) (operator : UnsignedBinaryOp)
    (left right : Nat) :
    unsignedBinaryGuard width operator left right ↔
      unsignedBinaryCDefined operator left right ∧
        unsignedBinaryAbstractable width operator left right := Iff.rfl

/-- C signed-to-unsigned conversion is reduction modulo the destination width. -/
def signedToUnsignedValue (width : Nat) (value : Int) : Nat :=
  (value % ((2 ^ width : Nat) : Int)).toNat

def signedBinary (width : Nat) (operator : SignedBinaryOp) (left right : Int) : Int :=
  match operator with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .tdiv => left.tdiv right
  | .tmod => left.tmod right
  | .bitAnd => Int.bmod
      (signedToUnsignedValue width left &&& signedToUnsignedValue width right) (2 ^ width)
  | .bitOr => Int.bmod
      (signedToUnsignedValue width left ||| signedToUnsignedValue width right) (2 ^ width)
  | .bitXor => Int.bmod
      (signedToUnsignedValue width left ^^^ signedToUnsignedValue width right) (2 ^ width)

def signedInRange (width : Nat) (value : Int) : Prop :=
  SWORD_MIN width ≤ value ∧ value ≤ SWORD_MAX width

def signedBinaryCDefined (width : Nat) (operator : SignedBinaryOp)
    (left right : Int) : Prop :=
  match operator with
  | .add | .sub | .mul => signedInRange width (signedBinary width operator left right)
  | .tdiv | .tmod =>
      right ≠ 0 ∧ ¬(left = SWORD_MIN width ∧ right = -1) ∧
        signedInRange width (signedBinary width operator left right)
  | .bitAnd | .bitOr | .bitXor => True

def signedBinaryAbstractable (width : Nat) (operator : SignedBinaryOp)
    (left right : Int) : Prop :=
  signedInRange width (signedBinary width operator left right)

def signedBinaryGuard (width : Nat) (operator : SignedBinaryOp)
    (left right : Int) : Prop :=
  signedBinaryCDefined width operator left right ∧
    signedBinaryAbstractable width operator left right

theorem signedBinaryGuard_iff (width : Nat) (operator : SignedBinaryOp)
    (left right : Int) :
    signedBinaryGuard width operator left right ↔
      signedBinaryCDefined width operator left right ∧
        signedBinaryAbstractable width operator left right := Iff.rfl

def unsignedUnary (width : Nat) (operator : UnsignedUnaryOp) (value : Nat) : Nat :=
  match operator with
  | .neg => if value = 0 then 0 else UWORD_MAX width + 1 - value
  | .bitNot => UWORD_MAX width - value

def signedUnary (width : Nat) (operator : SignedUnaryOp) (value : Int) : Int :=
  match operator with
  | .neg => -value
  | .bitNot => Int.bmod
      ((2 ^ width : Int) - 1 - signedToUnsignedValue width value) (2 ^ width)

def unsignedUnaryCDefined (_width : Nat) (_op : UnsignedUnaryOp)
    (_value : Nat) : Prop := True

def unsignedUnaryAbstractable (width : Nat) (operator : UnsignedUnaryOp)
    (value : Nat) : Prop := unsignedUnary width operator value ≤ UWORD_MAX width

def signedUnaryCDefined (width : Nat) (operator : SignedUnaryOp) (value : Int) : Prop :=
  match operator with
  | .neg => signedInRange width (signedUnary width operator value)
  | .bitNot => True

def signedUnaryAbstractable (width : Nat) (operator : SignedUnaryOp)
    (value : Int) : Prop := signedInRange width (signedUnary width operator value)

def compareNat (operator : WordComparison) (left right : Nat) : Bool :=
  match operator with
  | .eq => decide (left = right)
  | .ne => decide (left ≠ right)
  | .lt => decide (left < right)
  | .le => decide (left ≤ right)
  | .gt => decide (right < left)
  | .ge => decide (right ≤ left)

def compareInt (operator : WordComparison) (left right : Int) : Bool :=
  match operator with
  | .eq => decide (left = right)
  | .ne => decide (left ≠ right)
  | .lt => decide (left < right)
  | .le => decide (left ≤ right)
  | .gt => decide (right < left)
  | .ge => decide (right ≤ left)

def unsignedShift (direction : ShiftDirection) (value count : Nat) : Nat :=
  match direction with
  | .left => value <<< count
  | .right => value >>> count

def signedShift (direction : ShiftDirection) (value : Int) (count : Nat) : Int :=
  match direction with
  | .left => value <<< count
  | .right => value >>> count

def unsignedShiftCDefined (width : Nat) (_direction : ShiftDirection)
    (_value count : Nat) : Prop := count < width

def unsignedShiftAbstractable (width : Nat) (direction : ShiftDirection)
    (value count : Nat) : Prop :=
  unsignedShift direction value count ≤ UWORD_MAX width

def unsignedShiftGuard (width : Nat) (direction : ShiftDirection)
    (value count : Nat) : Prop :=
  unsignedShiftCDefined width direction value count ∧
    unsignedShiftAbstractable width direction value count

def signedShiftCDefined (width : Nat) (direction : ShiftDirection)
    (value : Int) (count : Nat) : Prop :=
  count < width ∧
    match direction with
    | .left => 0 ≤ value ∧ signedInRange width (signedShift direction value count)
    | .right => True

/-- The pinned upstream rule abstracts signed shifts only for nonnegative sources. -/
def signedShiftAbstractable (width : Nat) (direction : ShiftDirection)
    (value : Int) (count : Nat) : Prop :=
  0 ≤ value ∧ signedInRange width (signedShift direction value count)

def signedShiftGuard (width : Nat) (direction : ShiftDirection)
    (value : Int) (count : Nat) : Prop :=
  signedShiftCDefined width direction value count ∧
    signedShiftAbstractable width direction value count

theorem unsignedShiftGuard_iff (width : Nat) (direction : ShiftDirection)
    (value count : Nat) :
    unsignedShiftGuard width direction value count ↔
      unsignedShiftCDefined width direction value count ∧
        unsignedShiftAbstractable width direction value count := Iff.rfl

theorem signedShiftGuard_iff (width : Nat) (direction : ShiftDirection)
    (value : Int) (count : Nat) :
    signedShiftGuard width direction value count ↔
      signedShiftCDefined width direction value count ∧
        signedShiftAbstractable width direction value count := Iff.rfl

theorem bitVec_signedToUnsignedValue (value : BitVec width) :
    signedToUnsignedValue width value.toInt = value.toNat := by
  unfold signedToUnsignedValue
  calc
    (value.toInt % ((2 ^ width : Nat) : Int)).toNat =
        (BitVec.ofInt width value.toInt).toNat := (BitVec.toNat_ofInt _).symm
    _ = value.toNat := by rw [BitVec.ofInt_toInt]

theorem bitVec_toInt_eq_neg_toNat_neg (value : BitVec width)
    (negative : value.msb = true) :
    value.toInt = -((-value).toNat : Int) := by
  have valuePositive : 0 < value.toNat := by
    have lower := BitVec.toNat_ge_of_msb_true negative
    have powerPositive : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
    omega
  rw [BitVec.toNat_neg_of_pos valuePositive]
  simp only [BitVec.toInt_eq_msb_cond, negative, ↓reduceIte]
  have upper := value.isLt
  rw [Int.natCast_sub (Nat.le_of_lt upper)]
  omega

theorem bitVec_sdiv_eq_ofInt_tdiv (left right : BitVec width) :
    left.sdiv right = BitVec.ofInt width (left.toInt.tdiv right.toInt) := by
  rw [BitVec.sdiv_eq, Int.tdiv_cases]
  cases leftMsb : left.msb with
  | false =>
      have leftValue := BitVec.toInt_eq_toNat_of_msb leftMsb
      cases rightMsb : right.msb with
      | false =>
          have rightValue := BitVec.toInt_eq_toNat_of_msb rightMsb
          simp [leftValue, rightValue, BitVec.udiv_def]
          rw [Int.ofNat_ediv_ofNat, BitVec.ofInt_natCast]
      | true =>
          have rightValue := bitVec_toInt_eq_neg_toNat_neg right rightMsb
          simp [rightMsb, leftValue, rightValue,
            BitVec.udiv_def, BitVec.ofInt_neg]
          rw [Int.ofNat_ediv_ofNat, BitVec.ofInt_natCast]
  | true =>
      have leftValue := bitVec_toInt_eq_neg_toNat_neg left leftMsb
      have leftMagnitudeNonzero : 2 ^ width - left.toNat ≠ 0 := by
        have upper := left.isLt
        omega
      cases rightMsb : right.msb with
      | false =>
          have rightValue := BitVec.toInt_eq_toNat_of_msb rightMsb
          simp [leftMsb, leftValue, rightValue,
            leftMagnitudeNonzero, BitVec.udiv_def, BitVec.ofInt_neg]
          rw [Int.ofNat_ediv_ofNat, BitVec.ofInt_natCast]
      | true =>
          have rightValue := bitVec_toInt_eq_neg_toNat_neg right rightMsb
          simp [leftMsb, rightMsb, leftValue, rightValue,
            leftMagnitudeNonzero, BitVec.udiv_def]
          rw [Int.ofNat_ediv_ofNat, BitVec.ofInt_natCast]

theorem bitVec_srem_eq_ofInt_tmod (left right : BitVec width) :
    left.srem right = BitVec.ofInt width (left.toInt.tmod right.toInt) := by
  rw [BitVec.srem_eq]
  cases leftMsb : left.msb with
  | false =>
      have leftValue := BitVec.toInt_eq_toNat_of_msb leftMsb
      cases rightMsb : right.msb with
      | false =>
          have rightValue := BitVec.toInt_eq_toNat_of_msb rightMsb
          simp [leftValue, rightValue, BitVec.umod_def]
          rw [← Int.ofNat_tmod, BitVec.ofInt_natCast]
      | true =>
          have rightValue := bitVec_toInt_eq_neg_toNat_neg right rightMsb
          simp [rightMsb, leftValue, rightValue, BitVec.umod_def]
          rw [← Int.ofNat_tmod, BitVec.ofInt_natCast]
  | true =>
      have leftValue := bitVec_toInt_eq_neg_toNat_neg left leftMsb
      cases rightMsb : right.msb with
      | false =>
          have rightValue := BitVec.toInt_eq_toNat_of_msb rightMsb
          simp [leftMsb, leftValue, rightValue, BitVec.umod_def,
            BitVec.ofInt_neg]
          rw [← Int.ofNat_tmod, BitVec.ofInt_natCast]
      | true =>
          have rightValue := bitVec_toInt_eq_neg_toNat_neg right rightMsb
          simp [leftMsb, rightMsb, leftValue, rightValue, BitVec.umod_def,
            BitVec.ofInt_neg]
          rw [← Int.ofNat_tmod, BitVec.ofInt_natCast]

theorem bitVec_toNat_le_max (value : BitVec width) :
    value.toNat ≤ UWORD_MAX width := by
  unfold UWORD_MAX
  have := value.isLt
  omega

theorem bitVec_toNat_add (left right : BitVec width)
    (noOverflow : left.toNat + right.toNat ≤ UWORD_MAX width) :
    (left + right).toNat = left.toNat + right.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
  unfold UWORD_MAX at noOverflow
  have positive : 0 < 2 ^ width := Nat.pow_pos (by decide)
  exact (Nat.le_sub_one_iff_lt positive).mp noOverflow

theorem bitVec_toNat_sub (left right : BitVec width)
    (noWrap : right.toNat ≤ left.toNat) :
    (left - right).toNat = left.toNat - right.toNat := by
  rw [BitVec.toNat_sub]
  have leftLt := left.isLt
  have rightLt := right.isLt
  have decomposition : 2 ^ width - right.toNat + left.toNat =
      2 ^ width + (left.toNat - right.toNat) := by omega
  rw [decomposition, Nat.add_mod]
  have differenceLt : left.toNat - right.toNat < 2 ^ width := by omega
  simp [Nat.mod_eq_of_lt differenceLt]

theorem bitVec_toNat_lt (left right : BitVec width) :
    (left < right) ↔ left.toNat < right.toNat := by
  rfl

theorem bitVec_toNat_le (left right : BitVec width) :
    (left ≤ right) ↔ left.toNat ≤ right.toNat := by
  rfl

theorem bitVec_toNat_eq (left right : BitVec width) :
    (left = right) ↔ left.toNat = right.toNat := by
  exact BitVec.toNat_inj.symm

theorem bitVec_ult_toNat (left right : BitVec width) :
    left.ult right = decide (left.toNat < right.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ult_iff_lt, bitVec_toNat_lt]

theorem bitVec_toNat_ofNat (value : Nat)
    (inRange : value ≤ UWORD_MAX width) :
    (BitVec.ofNat width value).toNat = value := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold UWORD_MAX at inRange
  have positive : 0 < 2 ^ width := Nat.pow_pos (by decide)
  exact (Nat.le_sub_one_iff_lt positive).mp inRange

theorem bitVec_ofNat_toNat (value : BitVec width) :
    BitVec.ofNat width value.toNat = value := by
  apply BitVec.toNat_inj.mp
  rw [bitVec_toNat_ofNat value.toNat (bitVec_toNat_le_max value)]

/-- `BitVec.toNat` and `BitVec.ofNat` form the exact guarded unsigned certificate. -/
def valid_typ_abs_fn_bitVec (width : Nat) : valid_typ_abs_fn Nat (BitVec width) where
  abstractGuard := fun value => value ≤ UWORD_MAX width
  concreteGuard := fun _ => True
  abstract := BitVec.toNat
  concretize := BitVec.ofNat width
  abstract_concretize := bitVec_toNat_ofNat
  concretize_abstract := by
    intro value _
    exact bitVec_ofNat_toNat value

theorem bitVec_toInt_ofInt_inRange {width : Nat} {value : Int}
    (lower : SWORD_MIN width ≤ value) (upper : value ≤ SWORD_MAX width) :
    (BitVec.ofInt width value).toInt = value := by
  by_cases zero : width = 0
  · subst zero
    simp [SWORD_MIN, SWORD_MAX] at lower upper ⊢
    omega
  · apply BitVec.toInt_ofInt_eq_self (Nat.pos_of_ne_zero zero)
    · simpa [SWORD_MIN, zero] using lower
    · simp [SWORD_MAX, zero] at upper
      omega

/-- `BitVec.toInt` and `BitVec.ofInt` form the guarded signed certificate. -/
def valid_typ_abs_fn_bitVecSigned (width : Nat) :
    valid_typ_abs_fn Int (BitVec width) where
  abstractGuard := fun value =>
    SWORD_MIN width ≤ value ∧ value ≤ SWORD_MAX width
  concreteGuard := fun _ => True
  abstract := BitVec.toInt
  concretize := BitVec.ofInt width
  abstract_concretize := by
    intro value guard
    exact bitVec_toInt_ofInt_inRange guard.1 guard.2
  concretize_abstract := by
    intro value _
    exact BitVec.ofInt_toInt

def unsignedBinaryWord (width : WordWidth) (operator : UnsignedBinaryOp)
    (left right : BitVec width.bits) : BitVec width.bits :=
  match operator with
  | .mul => left * right
  | .div => left / right
  | .mod => left % right
  | .bitAnd => left &&& right
  | .bitOr => left ||| right
  | .bitXor => left ^^^ right

def signedBinaryWord (width : WordWidth) (operator : SignedBinaryOp)
    (left right : BitVec width.bits) : BitVec width.bits :=
  match operator with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .tdiv => left.sdiv right
  | .tmod => left.srem right
  | .bitAnd => left &&& right
  | .bitOr => left ||| right
  | .bitXor => left ^^^ right

def unsignedUnaryWord (width : WordWidth) (operator : UnsignedUnaryOp)
    (value : BitVec width.bits) : BitVec width.bits :=
  match operator with
  | .neg => -value
  | .bitNot => ~~~value

def signedUnaryWord (width : WordWidth) (operator : SignedUnaryOp)
    (value : BitVec width.bits) : BitVec width.bits :=
  match operator with
  | .neg => -value
  | .bitNot => ~~~value

def unsignedShiftWord (direction : ShiftDirection) (value : BitVec width)
    (count : Nat) : BitVec width :=
  match direction with
  | .left => value <<< count
  | .right => value >>> count

def signedShiftWord (direction : ShiftDirection) (value : BitVec width)
    (count : Nat) : BitVec width :=
  match direction with
  | .left => value <<< count
  | .right => value.sshiftRight count

theorem unsignedBinaryWord_exact (width : WordWidth) (operator : UnsignedBinaryOp) :
    abstract_binop (unsignedBinaryGuard width.bits operator)
      (BitVec.toNat : BitVec width.bits → Nat) (unsignedBinary operator)
      (unsignedBinaryWord width operator) := by
  intro left right guard
  cases operator with
  | mul =>
      rw [unsignedBinaryWord, unsignedBinary, BitVec.toNat_mul, Nat.mod_eq_of_lt]
      unfold unsignedBinaryGuard unsignedBinaryAbstractable UWORD_MAX at guard
      have positive : 0 < 2 ^ width.bits := Nat.pow_pos (by decide)
      exact (Nat.le_sub_one_iff_lt positive).mp guard.2
  | div => exact BitVec.toNat_udiv
  | mod => exact BitVec.toNat_umod
  | bitAnd => exact BitVec.toNat_and left right
  | bitOr => exact BitVec.toNat_or left right
  | bitXor => exact BitVec.toNat_xor left right

theorem signedBinaryWord_exact (width : WordWidth) (operator : SignedBinaryOp) :
    abstract_binop (signedBinaryGuard width.bits operator)
      (BitVec.toInt : BitVec width.bits → Int) (signedBinary width.bits operator)
      (signedBinaryWord width operator) := by
  intro left right guard
  have range := guard.2
  unfold signedBinaryAbstractable signedInRange at range
  cases operator with
  | add =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      simpa [signedBinaryWord, signedBinary, BitVec.toInt_add] using normalized
  | sub =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      simpa [signedBinaryWord, signedBinary, BitVec.toInt_sub] using normalized
  | mul =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      simpa [signedBinaryWord, signedBinary, BitVec.toInt_mul] using normalized
  | tdiv =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      have encoded := bitVec_sdiv_eq_ofInt_tdiv left right
      calc
        (signedBinaryWord width .tdiv left right).toInt =
            (BitVec.ofInt width.bits (left.toInt.tdiv right.toInt)).toInt :=
          congrArg BitVec.toInt encoded
        _ = signedBinary width.bits .tdiv left.toInt right.toInt := by
          simpa [signedBinary] using normalized
  | tmod =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      have encoded := bitVec_srem_eq_ofInt_tmod left right
      calc
        (signedBinaryWord width .tmod left right).toInt =
            (BitVec.ofInt width.bits (left.toInt.tmod right.toInt)).toInt :=
          congrArg BitVec.toInt encoded
        _ = signedBinary width.bits .tmod left.toInt right.toInt := by
          simpa [signedBinary] using normalized
  | bitAnd =>
      simp [signedBinaryWord, signedBinary, bitVec_signedToUnsignedValue,
        BitVec.toInt_and]
  | bitOr =>
      simp [signedBinaryWord, signedBinary, bitVec_signedToUnsignedValue,
        BitVec.toInt_or]
  | bitXor =>
      simp [signedBinaryWord, signedBinary, bitVec_signedToUnsignedValue,
        BitVec.toInt_xor]

theorem unsignedUnaryWord_exact (width : WordWidth) (operator : UnsignedUnaryOp) :
    abstract_unop (fun value =>
        unsignedUnaryCDefined width.bits operator value ∧
          unsignedUnaryAbstractable width.bits operator value)
      (BitVec.toNat : BitVec width.bits → Nat) (unsignedUnary width.bits operator)
      (unsignedUnaryWord width operator) := by
  intro value guard
  have abstractable := guard.2
  cases operator with
  | neg =>
      by_cases zero : value = 0
      · simp [unsignedUnaryWord, unsignedUnary, zero]
      · have positive : 0 < value.toNat := by
          apply Nat.pos_of_ne_zero
          simpa [BitVec.toNat_eq] using zero
        rw [unsignedUnaryWord, BitVec.toNat_neg_of_pos positive]
        rw [unsignedUnary, if_neg (Nat.ne_of_gt positive)]
        unfold UWORD_MAX
        have powerPositive : 0 < 2 ^ width.bits := Nat.two_pow_pos _
        omega
  | bitNot =>
      simp [unsignedUnaryWord, unsignedUnary, UWORD_MAX, BitVec.toNat_not]

theorem signedUnaryWord_exact (width : WordWidth) (operator : SignedUnaryOp) :
    abstract_unop (fun value =>
        signedUnaryCDefined width.bits operator value ∧
          signedUnaryAbstractable width.bits operator value)
      (BitVec.toInt : BitVec width.bits → Int) (signedUnary width.bits operator)
      (signedUnaryWord width operator) := by
  intro value guard
  have abstractable := guard.2
  unfold signedUnaryAbstractable signedInRange at abstractable
  cases operator with
  | neg =>
      have normalized := bitVec_toInt_ofInt_inRange abstractable.1 abstractable.2
      simpa [signedUnaryWord, signedUnary, BitVec.toInt_neg] using normalized
  | bitNot =>
      simp [signedUnaryWord, signedUnary, bitVec_signedToUnsignedValue,
        BitVec.toInt_not]

theorem unsignedShiftWord_exact (width : WordWidth) (direction : ShiftDirection)
    (value : BitVec width.bits) (count : Nat)
    (guard : unsignedShiftGuard width.bits direction value.toNat count) :
    (unsignedShiftWord direction value count).toNat =
      unsignedShift direction value.toNat count := by
  cases direction with
  | left =>
      rw [unsignedShiftWord, unsignedShift, BitVec.toNat_shiftLeft,
        Nat.mod_eq_of_lt]
      unfold unsignedShiftGuard unsignedShiftAbstractable UWORD_MAX at guard
      have positive : 0 < 2 ^ width.bits := Nat.pow_pos (by decide)
      exact (Nat.le_sub_one_iff_lt positive).mp guard.2
  | right => exact BitVec.toNat_ushiftRight value count

theorem signedShiftWord_exact (width : WordWidth) (direction : ShiftDirection)
    (value : BitVec width.bits) (count : Nat)
    (guard : signedShiftGuard width.bits direction value.toInt count) :
    (signedShiftWord direction value count).toInt =
      signedShift direction value.toInt count := by
  have range := guard.2.2
  unfold signedInRange at range
  cases direction with
  | left =>
      have normalized := bitVec_toInt_ofInt_inRange range.1 range.2
      have msb : value.msb = false := by
        rw [BitVec.msb_eq_false_iff_two_mul_lt]
        exact BitVec.toInt_pos_iff.mp guard.2.1
      have valueEq := BitVec.toInt_eq_toNat_of_msb msb
      simpa [signedShiftWord, signedShift, BitVec.toInt_shiftLeft, valueEq] using normalized
  | right => simp [signedShiftWord, signedShift]

theorem unsignedCastWord_exact (sourceWidth targetWidth : WordWidth)
    (value : BitVec sourceWidth.bits) :
    (value.setWidth targetWidth.bits).toNat =
      value.toNat % 2 ^ targetWidth.bits := by
  exact BitVec.toNat_setWidth targetWidth.bits value

theorem signedCastWord_exact (sourceWidth targetWidth : WordWidth)
    (value : BitVec sourceWidth.bits) :
    (value.signExtend targetWidth.bits).toInt =
      value.toInt.bmod (2 ^ targetWidth.bits) := by
  change (BitVec.ofInt targetWidth.bits value.toInt).toInt = _
  exact BitVec.toInt_ofInt value.toInt

theorem unsignedToSignedWord_exact (width : WordWidth)
    (value : BitVec width.bits)
    (guard : signedInRange width.bits (Int.ofNat value.toNat)) :
    value.toInt = Int.ofNat value.toNat := by
  have normalized := bitVec_toInt_ofInt_inRange guard.1 guard.2
  change (BitVec.ofNat width.bits value.toNat).toInt = Int.ofNat value.toNat at normalized
  rw [bitVec_ofNat_toNat] at normalized
  exact normalized

theorem bitVec_abstract_binop_add :
    abstract_binop (fun left right => left + right ≤ UWORD_MAX width)
      (BitVec.toNat : BitVec width → Nat) (· + ·)
      (fun left right : BitVec width => left + right) := by
  intro left right
  exact bitVec_toNat_add left right

theorem bitVec_abstract_binop_sub :
    abstract_binop (fun left right => right ≤ left)
      (BitVec.toNat : BitVec width → Nat) (· - ·)
      (fun left right : BitVec width => left - right) := by
  intro left right
  exact bitVec_toNat_sub left right

theorem bitVec_abstract_bool_binop_ult :
    abstract_bool_binop (fun _ _ => True)
      (BitVec.toNat : BitVec width → Nat)
      (fun left right => decide (left < right))
      (fun left right : BitVec width => left.ult right) := by
  intro left right _
  exact bitVec_ult_toNat left right

theorem bitVec_abstract_bool_binop_le :
    abstract_bool_binop (fun _ _ => True)
      (BitVec.toNat : BitVec width → Nat)
      (fun left right => decide (left ≤ right))
      (fun left right : BitVec width => decide (left ≤ right)) := by
  intro left right _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using bitVec_toNat_le left right

theorem bitVec_abstract_bool_binop_eq :
    abstract_bool_binop (fun _ _ => True)
      (BitVec.toNat : BitVec width → Nat)
      (fun left right => decide (left = right))
      (fun left right : BitVec width => decide (left = right)) := by
  intro left right _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using bitVec_toNat_eq left right

theorem abstract_val_ofNat_bitVec (value : Nat) :
    abstract_val (value ≤ UWORD_MAX width) value BitVec.toNat
      (BitVec.ofNat width value) := by
  intro inRange
  exact (bitVec_toNat_ofNat value inRange).symm

/-! ## Type-abstraction correspondence rules -/

theorem corresTA_refl
    (precondition : State → Prop)
    (program : L2.L2Program State Exception ResultType) :
    corresTA precondition id id program program := by
  exact CorresXF.refl precondition program

theorem corresTA_L2_gets
    {precondition : State → Prop}
    {abstractRead : State → AbstractResult}
    {concreteRead : State → ConcreteResult}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {names : List String}
    (readRelated : ∀ state, abstract_val (precondition state)
      (abstractRead state) resultMap (concreteRead state)) :
    corresTA precondition resultMap exceptionMap
      (L2.gets abstractRead names) (L2.gets concreteRead names) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [L2.gets, L2.mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_gets] at member
    rcases member with ⟨rfl, rfl⟩
    rw [L2.gets, mem_liftE, mem_gets]
    exact ⟨(readRelated post hypothesis.1).symm, rfl⟩
  · simp [L2.gets, L2.failed_liftE, AutoCorres.gets]

theorem corresTA_L2_modify
    {precondition : State → Prop}
    {abstractUpdate concreteUpdate : State → State}
    {exceptionMap : ConcreteException → AbstractException}
    (updateRelated : ∀ state, abstract_val (precondition state)
      (abstractUpdate state) id (concreteUpdate state)) :
    corresTA precondition id exceptionMap
      (L2.modify abstractUpdate) (L2.modify concreteUpdate) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [L2.modify, L2.mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_modify] at member
    rcases member with ⟨rfl, rfl⟩
    rw [L2.modify, mem_liftE, mem_modify]
    exact ⟨rfl, (updateRelated state hypothesis.1).symm⟩
  · simp [L2.modify, L2.failed_liftE, AutoCorres.modify]

/--
The generated abstract guard is executable.  If `generated state` is false,
the abstract `L2.guard` fails; it is not silently promoted to a theorem premise.
-/
theorem corresTA_L2_guard
    {abstractGuard concreteGuard generated : State → Prop}
    {exceptionMap : ConcreteException → AbstractException}
    (guardRelated : ∀ state, abstract_val (generated state)
      (abstractGuard state) id (concreteGuard state)) :
    corresTA (fun _ => True) id exceptionMap
      (L2.guard fun state => abstractGuard state ∧ generated state)
      (L2.guard concreteGuard) := by
  intro state hypothesis
  have abstractHolds : abstractGuard state ∧ generated state := by
    exact Classical.byContradiction fun doesNotHold =>
      hypothesis.2 (by
        simpa [L2.guard, L2.failed_liftE, AutoCorres.guard] using doesNotHold)
  have concreteHolds : concreteGuard state := by
    have equality : abstractGuard state = concreteGuard state := by
      simpa [id] using guardRelated state abstractHolds.2
    exact equality.mp abstractHolds.1
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [L2.guard, L2.mem_liftE_iff] at member
    rcases member with ⟨value, rfl, member⟩
    rw [mem_guard] at member
    rcases member with ⟨_, rfl, rfl⟩
    rw [L2.guard, mem_liftE, mem_guard]
    exact ⟨abstractHolds, rfl, rfl⟩
  · simpa [L2.guard, L2.failed_liftE, AutoCorres.guard] using concreteHolds

theorem generated_guard_failed_iff
    (abstractGuard generated : State → Prop) (state : State) :
    (L2.guard (Exception := Exception)
      (fun current => abstractGuard current ∧ generated current) state).failed ↔
      ¬(abstractGuard state ∧ generated state) := by
  simp [L2.guard, L2.failed_liftE, AutoCorres.guard]

theorem corresTA_L2_throw
    {condition : Prop} {abstractException : AbstractException}
    {concreteException : ConcreteException}
    {exceptionMap : ConcreteException → AbstractException}
    {resultMap : ConcreteResult → AbstractResult} {names : List String}
    (exceptionRelated : abstract_val condition abstractException
      exceptionMap concreteException) :
    corresTA (fun _ : State => condition) resultMap exceptionMap
      (L2.throw abstractException names) (L2.throw concreteException names) := by
  intro state hypothesis
  refine ⟨?_, ?_⟩
  · intro result post member
    simp [L2.throw, AutoCorres.throw, pure] at member
    rcases member with ⟨rfl, rfl⟩
    rw [L2.throw, mem_throw]
    exact ⟨(exceptionRelated hypothesis.1).symm, rfl⟩
  · simp [L2.throw, AutoCorres.throw, pure]

theorem corresTA_L2_skip
    {exceptionMap : ConcreteException → AbstractException} :
    corresTA (fun _ : State => True) id exceptionMap L2.skip L2.skip := by
  intro state _
  refine ⟨?_, by simp [L2.skip, L2.gets, L2.failed_liftE, AutoCorres.gets]⟩
  intro result post member
  rw [L2.skip, L2.gets, L2.mem_liftE_iff] at member
  rcases member with ⟨value, rfl, member⟩
  rw [mem_gets] at member
  rcases member with ⟨rfl, rfl⟩
  rw [L2.skip, L2.gets, mem_liftE, mem_gets]
  exact ⟨rfl, rfl⟩

theorem corresTA_L2_fail
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException} :
    corresTA (fun _ : State => True) resultMap exceptionMap L2.fail L2.fail := by
  intro state hypothesis
  exact False.elim (hypothesis.2 (by simp [L2.fail]))

theorem mem_L2_seq_iff
    {first : L2.L2Program State Exception A}
    {next : A → L2.L2Program State Exception B}
    {state post : State} {result : Except Exception B} :
    (result, post) ∈ (L2.seq first next state).results ↔
      (∃ exception middle,
        (Except.error exception, middle) ∈ (first state).results ∧
        result = Except.error exception ∧ post = middle) ∨
      (∃ value middle, (Except.ok value, middle) ∈ (first state).results ∧
        (result, post) ∈ (next value middle).results) := by
  unfold L2.seq bindE
  rw [mem_bind]
  constructor
  · rintro ⟨value, middle, member, continuation⟩
    cases value with
    | error exception =>
        change (result, post) = (Except.error exception, middle) at continuation
        cases continuation
        exact Or.inl ⟨exception, post, member, rfl, rfl⟩
    | ok value => exact Or.inr ⟨value, middle, member, continuation⟩
  · rintro (⟨exception, middle, member, rfl, rfl⟩ | ⟨value, middle, member, next⟩)
    · exact ⟨Except.error exception, post, member, rfl⟩
    · exact ⟨Except.ok value, middle, member, next⟩

theorem failed_L2_seq_iff
    {first : L2.L2Program State Exception A}
    {next : A → L2.L2Program State Exception B} {state : State} :
    (L2.seq first next state).failed ↔
      (first state).failed ∨
      ∃ value middle, (Except.ok value, middle) ∈ (first state).results ∧
        (next value middle).failed := by
  unfold L2.seq bindE
  constructor
  · rintro (failed | ⟨value, middle, member, continuationFailed⟩)
    · exact Or.inl failed
    · cases value with
      | error exception => exact False.elim continuationFailed
      | ok value => exact Or.inr ⟨value, middle, member, continuationFailed⟩
  · rintro (failed | ⟨value, middle, member, continuationFailed⟩)
    · exact Or.inl failed
    · exact Or.inr ⟨Except.ok value, middle, member, continuationFailed⟩

theorem guard_member (condition : State → Prop) {state : State}
    (holds : condition state) :
    (Except.ok (), state) ∈ (L2.guard (Exception := Exception) condition state).results := by
  rw [L2.guard, mem_liftE, mem_guard]
  exact ⟨holds, rfl, rfl⟩

theorem guard_holds_of_noFail (condition : State → Prop) {state : State}
    (noFail : ¬(L2.guard (Exception := Exception) condition state).failed) :
    condition state := by
  exact Classical.byContradiction fun doesNotHold =>
    noFail (by simpa [L2.guard, L2.failed_liftE, AutoCorres.guard])

/--
Sequence converts the first result and executes the generated guard before the
abstract continuation.  Consequently a failed conversion condition is an L2
failure on the abstract side.
-/
theorem corresTA_L2_seq
    {precondition : State → Prop}
    {generated : AbstractFirst → State → Prop}
    {firstMap : ConcreteFirst → AbstractFirst}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {abstractFirst : L2.L2Program State AbstractException AbstractFirst}
    {concreteFirst : L2.L2Program State ConcreteException ConcreteFirst}
    {abstractNext : AbstractFirst →
      L2.L2Program State AbstractException AbstractResult}
    {concreteNext : ConcreteFirst →
      L2.L2Program State ConcreteException ConcreteResult}
    (firstRelated : corresTA precondition firstMap exceptionMap
      abstractFirst concreteFirst)
    (nextRelated : ∀ value, corresTA (generated (firstMap value))
      resultMap exceptionMap (abstractNext (firstMap value)) (concreteNext value)) :
    corresTA precondition resultMap exceptionMap
      (L2.seq abstractFirst fun value =>
        L2.seq (L2.guard (generated value)) fun _ => abstractNext value)
      (L2.seq concreteFirst concreteNext) := by
  intro state hypothesis
  have firstNoFail : ¬(abstractFirst state).failed := fun failed =>
    hypothesis.2 (failed_L2_seq_iff.mpr (Or.inl failed))
  have firstRule := firstRelated state ⟨hypothesis.1, firstNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_L2_seq_iff] at member ⊢
    rcases member with errorCase | normalCase
    · rcases errorCase with ⟨exception, middle, firstMember, rfl, rfl⟩
      exact Or.inl ⟨exceptionMap exception, post,
        firstRule.1 (.error exception) post firstMember, rfl, rfl⟩
    · rcases normalCase with ⟨value, middle, firstMember, nextMember⟩
      have mappedFirst := firstRule.1 (.ok value) middle firstMember
      have continuationNoFail :
          ¬(L2.seq (L2.guard (generated (firstMap value)))
            (fun _ => abstractNext (firstMap value)) middle).failed := fun failed =>
        hypothesis.2 (failed_L2_seq_iff.mpr
          (Or.inr ⟨firstMap value, middle, mappedFirst, failed⟩))
      have generatedHolds : generated (firstMap value) middle :=
        guard_holds_of_noFail _ (fun failed => continuationNoFail
          (failed_L2_seq_iff.mpr (Or.inl failed)))
      have abstractNextNoFail :
          ¬(abstractNext (firstMap value) middle).failed := fun failed =>
        continuationNoFail (failed_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds, failed⟩))
      have nextRule := nextRelated value middle
        ⟨generatedHolds, abstractNextNoFail⟩
      exact Or.inr ⟨firstMap value, middle, mappedFirst,
        mem_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds,
            nextRule.1 result post nextMember⟩)⟩
  · intro concreteFailed
    rw [failed_L2_seq_iff] at concreteFailed
    rcases concreteFailed with firstFailed | nextFailed
    · exact firstRule.2 firstFailed
    · rcases nextFailed with ⟨value, middle, firstMember, failed⟩
      have mappedFirst := firstRule.1 (.ok value) middle firstMember
      have continuationNoFail :
          ¬(L2.seq (L2.guard (generated (firstMap value)))
            (fun _ => abstractNext (firstMap value)) middle).failed := fun targetFailed =>
        hypothesis.2 (failed_L2_seq_iff.mpr
          (Or.inr ⟨firstMap value, middle, mappedFirst, targetFailed⟩))
      have generatedHolds : generated (firstMap value) middle :=
        guard_holds_of_noFail _ (fun guardFailed => continuationNoFail
          (failed_L2_seq_iff.mpr (Or.inl guardFailed)))
      have abstractNextNoFail :
          ¬(abstractNext (firstMap value) middle).failed := fun targetFailed =>
        continuationNoFail (failed_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds, targetFailed⟩))
      exact (nextRelated value middle
        ⟨generatedHolds, abstractNextNoFail⟩).2 failed

/-- Turn a correspondence precondition into an executable target-side guard. -/
theorem corresTA_precond_to_guard
    {precondition : State → Prop}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {abstract : L2.L2Program State AbstractException AbstractResult}
    {concrete : L2.L2Program State ConcreteException ConcreteResult}
    (related : corresTA precondition resultMap exceptionMap abstract concrete) :
    corresTA (fun _ => True) resultMap exceptionMap
      (L2.seq (L2.guard precondition) fun _ => abstract) concrete := by
  intro state hypothesis
  have guardNoFail :
      ¬(L2.guard (Exception := AbstractException) precondition state).failed :=
    fun failed => hypothesis.2 (failed_L2_seq_iff.mpr (Or.inl failed))
  have holds := guard_holds_of_noFail precondition guardNoFail
  have abstractNoFail : ¬(abstract state).failed := fun failed =>
    hypothesis.2 (failed_L2_seq_iff.mpr (Or.inr
      ⟨(), state, guard_member precondition holds, failed⟩))
  have rule := related state ⟨holds, abstractNoFail⟩
  refine ⟨?_, rule.2⟩
  intro result post member
  exact mem_L2_seq_iff.mpr (Or.inr
    ⟨(), state, guard_member precondition holds, rule.1 result post member⟩)

/-- Guard every normal result of a target program while returning it unchanged. -/
def guardResults (condition : AbstractResult → State → Prop)
    (program : L2.L2Program State AbstractException AbstractResult) :
    L2.L2Program State AbstractException AbstractResult :=
  L2.seq program fun value =>
    L2.seq (L2.guard (condition value)) fun _ => L2.gets (fun _ => value) []

/-- Appending a result guard preserves correspondence under target no-failure. -/
theorem corresTA_guardResults
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {condition : AbstractResult → State → Prop}
    {abstract : L2.L2Program State AbstractException AbstractResult}
    {concrete : L2.L2Program State ConcreteException ConcreteResult}
    (related : corresTA (fun _ : State => True) resultMap exceptionMap abstract concrete) :
    corresTA (fun _ : State => True) resultMap exceptionMap
      (guardResults condition abstract) concrete := by
  intro state hypothesis
  have abstractNoFail : ¬(abstract state).failed := fun failed =>
    hypothesis.2 (failed_L2_seq_iff.mpr (Or.inl failed))
  have rule := related state ⟨True.intro, abstractNoFail⟩
  refine ⟨?_, rule.2⟩
  intro result post member
  have mapped := rule.1 result post member
  cases result with
  | error exception =>
      exact mem_L2_seq_iff.mpr (Or.inl
        ⟨exceptionMap exception, post, mapped, rfl, rfl⟩)
  | ok value =>
      have continuationNoFail :
          ¬(L2.seq (L2.guard (condition (resultMap value)))
            (fun _ => L2.gets (fun _ => resultMap value) []) post).failed :=
        fun failed => hypothesis.2 (failed_L2_seq_iff.mpr
          (Or.inr ⟨resultMap value, post, mapped, failed⟩))
      have guardHolds := guard_holds_of_noFail (condition (resultMap value))
        (fun failed => continuationNoFail (failed_L2_seq_iff.mpr (Or.inl failed)))
      apply mem_L2_seq_iff.mpr
      exact Or.inr ⟨resultMap value, post, mapped,
        mem_L2_seq_iff.mpr (Or.inr ⟨(), post,
          guard_member _ guardHolds, by simp [L2.gets]⟩)⟩

/-- Successful guarded target execution proves validity of every mapped source result. -/
theorem guardResults_source_valid
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {condition : AbstractResult → State → Prop}
    {abstract : L2.L2Program State AbstractException AbstractResult}
    {concrete : L2.L2Program State ConcreteException ConcreteResult}
    (related : corresTA (fun _ : State => True) resultMap exceptionMap abstract concrete)
    {state post : State} {value : ConcreteResult}
    (noFail : ¬(guardResults condition abstract state).failed)
    (member : (Except.ok value, post) ∈ (concrete state).results) :
    condition (resultMap value) post := by
  have abstractNoFail : ¬(abstract state).failed := fun failed =>
    noFail (failed_L2_seq_iff.mpr (Or.inl failed))
  have mapped := (related state ⟨True.intro, abstractNoFail⟩).1
    (Except.ok value) post member
  have continuationNoFail :
      ¬(L2.seq (L2.guard (condition (resultMap value)))
        (fun _ => L2.gets (fun _ => resultMap value) []) post).failed :=
    fun failed => noFail (failed_L2_seq_iff.mpr
      (Or.inr ⟨resultMap value, post, mapped, failed⟩))
  exact guard_holds_of_noFail _
    (fun failed => continuationNoFail (failed_L2_seq_iff.mpr (Or.inl failed)))

private theorem mem_L2_catch_iff
    {body : L2.L2Program State Exception A}
    {handler : Exception → L2.L2Program State NewException A}
    {state post : State} {result : Except NewException A} :
    (result, post) ∈ (L2.catch body handler state).results ↔
      (∃ value middle, (Except.ok value, middle) ∈ (body state).results ∧
        result = Except.ok value ∧ post = middle) ∨
      (∃ exception middle,
        (Except.error exception, middle) ∈ (body state).results ∧
        (result, post) ∈ (handler exception middle).results) := by
  unfold L2.catch handle
  rw [mem_bind]
  constructor
  · rintro ⟨value, middle, member, continuation⟩
    cases value with
    | error exception => exact Or.inr ⟨exception, middle, member, continuation⟩
    | ok value =>
        change (result, post) = (Except.ok value, middle) at continuation
        cases continuation
        exact Or.inl ⟨value, post, member, rfl, rfl⟩
  · rintro (⟨value, middle, member, rfl, rfl⟩ |
      ⟨exception, middle, member, continuation⟩)
    · exact ⟨Except.ok value, post, member, rfl⟩
    · exact ⟨Except.error exception, middle, member, continuation⟩

private theorem failed_L2_catch_iff
    {body : L2.L2Program State Exception A}
    {handler : Exception → L2.L2Program State NewException A} {state : State} :
    (L2.catch body handler state).failed ↔
      (body state).failed ∨
      ∃ exception middle,
        (Except.error exception, middle) ∈ (body state).results ∧
        (handler exception middle).failed := by
  unfold L2.catch handle
  constructor
  · rintro (failed | ⟨value, middle, member, continuationFailed⟩)
    · exact Or.inl failed
    · cases value with
      | error exception =>
          exact Or.inr ⟨exception, middle, member, continuationFailed⟩
      | ok value => exact False.elim continuationFailed
  · rintro (failed | ⟨exception, middle, member, continuationFailed⟩)
    · exact Or.inl failed
    · exact Or.inr
        ⟨Except.error exception, middle, member, continuationFailed⟩

/-- Catch converts the caught exception and guards its abstract handler. -/
theorem corresTA_L2_catch
    {precondition : State → Prop}
    {generated : AbstractCaught → State → Prop}
    {resultMap : ConcreteResult → AbstractResult}
    {caughtMap : ConcreteCaught → AbstractCaught}
    {exceptionMap : ConcreteException → AbstractException}
    {abstractBody : L2.L2Program State AbstractCaught AbstractResult}
    {concreteBody : L2.L2Program State ConcreteCaught ConcreteResult}
    {abstractHandler : AbstractCaught →
      L2.L2Program State AbstractException AbstractResult}
    {concreteHandler : ConcreteCaught →
      L2.L2Program State ConcreteException ConcreteResult}
    (bodyRelated : corresTA precondition resultMap caughtMap
      abstractBody concreteBody)
    (handlerRelated : ∀ exception,
      corresTA (generated (caughtMap exception)) resultMap exceptionMap
        (abstractHandler (caughtMap exception)) (concreteHandler exception)) :
    corresTA precondition resultMap exceptionMap
      (L2.catch abstractBody fun exception =>
        L2.seq (L2.guard (generated exception)) fun _ => abstractHandler exception)
      (L2.catch concreteBody concreteHandler) := by
  intro state hypothesis
  have bodyNoFail : ¬(abstractBody state).failed := fun failed =>
    hypothesis.2 (failed_L2_catch_iff.mpr (Or.inl failed))
  have bodyRule := bodyRelated state ⟨hypothesis.1, bodyNoFail⟩
  refine ⟨?_, ?_⟩
  · intro result post member
    rw [mem_L2_catch_iff] at member ⊢
    rcases member with normalCase | errorCase
    · rcases normalCase with ⟨value, middle, bodyMember, rfl, rfl⟩
      exact Or.inl ⟨resultMap value, post,
        bodyRule.1 (.ok value) post bodyMember, rfl, rfl⟩
    · rcases errorCase with ⟨exception, middle, bodyMember, handlerMember⟩
      have mappedBody := bodyRule.1 (.error exception) middle bodyMember
      have continuationNoFail :
          ¬(L2.seq (L2.guard (generated (caughtMap exception)))
            (fun _ => abstractHandler (caughtMap exception)) middle).failed :=
        fun failed => hypothesis.2 (failed_L2_catch_iff.mpr (Or.inr
          ⟨caughtMap exception, middle, mappedBody, failed⟩))
      have generatedHolds : generated (caughtMap exception) middle :=
        guard_holds_of_noFail _ (fun failed => continuationNoFail
          (failed_L2_seq_iff.mpr (Or.inl failed)))
      have handlerNoFail :
          ¬(abstractHandler (caughtMap exception) middle).failed := fun failed =>
        continuationNoFail (failed_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds, failed⟩))
      have handlerRule := handlerRelated exception middle
        ⟨generatedHolds, handlerNoFail⟩
      exact Or.inr ⟨caughtMap exception, middle, mappedBody,
        mem_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds,
            handlerRule.1 result post handlerMember⟩)⟩
  · intro concreteFailed
    rw [failed_L2_catch_iff] at concreteFailed
    rcases concreteFailed with bodyFailed | handlerFailed
    · exact bodyRule.2 bodyFailed
    · rcases handlerFailed with ⟨exception, middle, bodyMember, failed⟩
      have mappedBody := bodyRule.1 (.error exception) middle bodyMember
      have continuationNoFail :
          ¬(L2.seq (L2.guard (generated (caughtMap exception)))
            (fun _ => abstractHandler (caughtMap exception)) middle).failed :=
        fun targetFailed => hypothesis.2 (failed_L2_catch_iff.mpr (Or.inr
          ⟨caughtMap exception, middle, mappedBody, targetFailed⟩))
      have generatedHolds : generated (caughtMap exception) middle :=
        guard_holds_of_noFail _ (fun guardFailed => continuationNoFail
          (failed_L2_seq_iff.mpr (Or.inl guardFailed)))
      have handlerNoFail :
          ¬(abstractHandler (caughtMap exception) middle).failed :=
        fun targetFailed => continuationNoFail (failed_L2_seq_iff.mpr (Or.inr
          ⟨(), middle, guard_member _ generatedHolds, targetFailed⟩))
      exact (handlerRelated exception middle
        ⟨generatedHolds, handlerNoFail⟩).2 failed

/-- Corresponding conditionals execute guarded abstract branches. -/
theorem corresTA_L2_condition
    {testGuard thenGuard elseGuard : State → Prop}
    {abstractTest concreteTest : State → Prop}
    {resultMap : ConcreteResult → AbstractResult}
    {exceptionMap : ConcreteException → AbstractException}
    {abstractThen abstractElse :
      L2.L2Program State AbstractException AbstractResult}
    {concreteThen concreteElse :
      L2.L2Program State ConcreteException ConcreteResult}
    (thenRelated : corresTA thenGuard resultMap exceptionMap
      abstractThen concreteThen)
    (elseRelated : corresTA elseGuard resultMap exceptionMap
      abstractElse concreteElse)
    (testRelated : ∀ state, abstract_val (testGuard state)
      (abstractTest state) id (concreteTest state)) :
    corresTA testGuard resultMap exceptionMap
      (L2.condition abstractTest
        (L2.seq (L2.guard thenGuard) fun _ => abstractThen)
        (L2.seq (L2.guard elseGuard) fun _ => abstractElse))
      (L2.condition concreteTest concreteThen concreteElse) := by
  have thenGuarded := corresTA_precond_to_guard thenRelated
  have elseGuarded := corresTA_precond_to_guard elseRelated
  intro state hypothesis
  have testEquality : abstractTest state = concreteTest state := by
    simpa [id] using testRelated state hypothesis.1
  by_cases holds : concreteTest state
  · have abstractHolds : abstractTest state := testEquality.symm ▸ holds
    have branchNoFail :
        ¬(L2.seq (L2.guard thenGuard) (fun _ => abstractThen) state).failed := by
      simpa [L2.condition, abstractHolds] using hypothesis.2
    simpa [L2.condition, holds, abstractHolds] using
      thenGuarded state ⟨True.intro, branchNoFail⟩
  · have abstractDoesNotHold : ¬abstractTest state := fun abstractHolds =>
      holds (testEquality.mp abstractHolds)
    have branchNoFail :
        ¬(L2.seq (L2.guard elseGuard) (fun _ => abstractElse) state).failed := by
      simpa [L2.condition, abstractDoesNotHold] using hypothesis.2
    simpa [L2.condition, holds, abstractDoesNotHold] using
      elseGuarded state ⟨True.intro, branchNoFail⟩

/-- A loop body cannot fail when its enclosing loop is known not to fail. -/
private theorem whileBody_noFail
    {Acc : Type u} {State : Type v}
    {test : Acc → State → Prop} {body : Acc → Nondet State Acc}
    {value : Acc} {state : State}
    (loopNoFail : ¬(whileLoop test body value state).failed)
    (holds : test value state) : ¬(body value state).failed := by
  intro failed
  exact loopNoFail (Or.inl (.bodyFailure holds failed))

/-- The rest of a successful loop branch inherits target-side no-failure. -/
private theorem whileRest_noFail
    {Acc : Type u} {State : Type v}
    {test : Acc → State → Prop} {body : Acc → Nondet State Acc}
    {value next : Acc} {state nextState : State}
    (loopNoFail : ¬(whileLoop test body value state).failed)
    (holds : test value state)
    (member : (next, nextState) ∈ (body value state).results) :
    ¬(whileLoop test body next nextState).failed := by
  intro failed
  rcases failed with finite | diverges
  · exact loopNoFail (Or.inl (.step holds member finite))
  · apply loopNoFail
    apply Or.inr
    intro terminates
    cases terminates with
    | stop doesNotHold => exact doesNotHold holds
    | step _ branches => exact diverges (branches next nextState member)

private theorem whileResult_map
    {valueMap : Concrete → Abstract}
    {valid : Concrete → Prop}
    {abstractTest : Abstract → State → Prop}
    {concreteTest : Concrete → State → Prop}
    {abstractBody : Abstract → Nondet State Abstract}
    {concreteBody : Concrete → Nondet State Concrete}
    (testRelated : ∀ value state, valid value →
      (abstractTest (valueMap value) state ↔ concreteTest value state))
    (bodyRelated : ∀ value state, valid value →
      ¬(abstractBody (valueMap value) state).failed →
      (∀ next post, (next, post) ∈ (concreteBody value state).results →
        (valueMap next, post) ∈ (abstractBody (valueMap value) state).results) ∧
      ¬(concreteBody value state).failed)
    (bodyPreserved : ∀ value state, valid value →
      ¬(abstractBody (valueMap value) state).failed →
      ∀ next post, (next, post) ∈ (concreteBody value state).results → valid next)
    {value : Concrete} {state : State}
    (initialValid : valid value)
    (loopNoFail : ¬(whileLoop abstractTest abstractBody (valueMap value) state).failed) :
    ∀ {result : Option (Concrete × State)},
      WhileResult concreteTest concreteBody (some (value, state)) result →
      WhileResult abstractTest abstractBody (some (valueMap value, state))
        (result.map fun pair => (valueMap pair.1, pair.2)) := by
  intro result execution
  generalize initialEq : some (value, state) = initial at execution
  induction execution generalizing value state with
  | stop doesNotHold =>
      cases initialEq
      exact .stop (fun holds =>
        doesNotHold ((testRelated _ _ initialValid).mp holds))
  | bodyFailure holds failed =>
      cases initialEq
      have abstractHolds := (testRelated _ _ initialValid).mpr holds
      exact False.elim ((bodyRelated _ _ initialValid (fun bodyFailed =>
        loopNoFail (Or.inl (.bodyFailure abstractHolds bodyFailed)))).2 failed)
  | step holds member rest induction =>
      cases initialEq
      have abstractHolds := (testRelated _ _ initialValid).mpr holds
      have bodyNoFail := fun bodyFailed =>
        loopNoFail (Or.inl (.bodyFailure abstractHolds bodyFailed))
      have mapped := (bodyRelated _ _ initialValid bodyNoFail).1 _ _ member
      have nextValid := bodyPreserved _ _ initialValid bodyNoFail _ _ member
      have restNoFail := whileRest_noFail (loopNoFail := loopNoFail)
        (holds := abstractHolds) (member := mapped)
      exact .step abstractHolds mapped (induction nextValid restNoFail rfl)

private theorem whileTerminates_map
    {valueMap : Concrete → Abstract}
    {valid : Concrete → Prop}
    {abstractTest : Abstract → State → Prop}
    {concreteTest : Concrete → State → Prop}
    {abstractBody : Abstract → Nondet State Abstract}
    {concreteBody : Concrete → Nondet State Concrete}
    (testRelated : ∀ value state, valid value →
      (abstractTest (valueMap value) state ↔ concreteTest value state))
    (bodyRelated : ∀ value state, valid value →
      ¬(abstractBody (valueMap value) state).failed →
      (∀ next post, (next, post) ∈ (concreteBody value state).results →
        (valueMap next, post) ∈ (abstractBody (valueMap value) state).results) ∧
      ¬(concreteBody value state).failed)
    (bodyPreserved : ∀ value state, valid value →
      ¬(abstractBody (valueMap value) state).failed →
      ∀ next post, (next, post) ∈ (concreteBody value state).results → valid next)
    {value : Concrete} {state : State}
    (initialValid : valid value)
    (loopNoFail : ¬(whileLoop abstractTest abstractBody (valueMap value) state).failed)
    (terminates : WhileTerminates abstractTest abstractBody (valueMap value) state) :
    WhileTerminates concreteTest concreteBody value state := by
  generalize mapped : valueMap value = abstractValue at terminates loopNoFail
  induction terminates generalizing value with
  | stop doesNotHold =>
      cases mapped
      exact .stop (fun holds =>
        doesNotHold ((testRelated _ _ initialValid).mpr holds))
  | step holds branches induction =>
      cases mapped
      have concreteHolds := (testRelated _ _ initialValid).mp holds
      have bodyNoFail := fun bodyFailed =>
        loopNoFail (Or.inl (.bodyFailure holds bodyFailed))
      have rule := bodyRelated _ _ initialValid bodyNoFail
      apply WhileTerminates.step concreteHolds
      intro next nextState member
      have mappedMember := rule.1 _ _ member
      have nextValid := bodyPreserved _ _ initialValid bodyNoFail _ _ member
      have restNoFail : ¬(whileLoop abstractTest abstractBody
          (valueMap next) nextState).failed := by
        intro failed
        rcases failed with finite | diverges
        · exact loopNoFail (Or.inl (.step holds mappedMember finite))
        · apply loopNoFail
          apply Or.inr
          intro terminates
          cases terminates with
          | stop doesNotHold => exact doesNotHold holds
          | step _ rest => exact diverges (rest _ _ mappedMember)
      exact induction (valueMap next) nextState mappedMember
        (value := next) nextValid rfl restNoFail

/-- Guard-aware loop correspondence carrying a source accumulator invariant. -/
theorem corresTA_L2_while_map_guarded
    {valueMap : Concrete → Abstract}
    {valid : Concrete → Prop}
    {exceptionMap : ConcreteException → AbstractException}
    {abstractTest : Abstract → State → Prop}
    {concreteTest : Concrete → State → Prop}
    {abstractBody : Abstract → L2.L2Program State AbstractException Abstract}
    {concreteBody : Concrete → L2.L2Program State ConcreteException Concrete}
    {abstractInitial : Abstract} {concreteInitial : Concrete} {names : List String}
    (testRelated : ∀ value state, valid value →
      (abstractTest (valueMap value) state ↔ concreteTest value state))
    (bodyRelated : ∀ value, valid value →
      corresTA (fun _ : State => True) valueMap exceptionMap
      (abstractBody (valueMap value)) (concreteBody value))
    (bodyPreserved : ∀ value state, valid value →
      ¬(abstractBody (valueMap value) state).failed →
      ∀ next post, (Except.ok next, post) ∈ (concreteBody value state).results →
        valid next)
    (initialValid : valid concreteInitial)
    (initialRelated : abstractInitial = valueMap concreteInitial) :
    corresTA (fun _ : State => True) valueMap exceptionMap
      (L2.while abstractTest abstractBody abstractInitial names)
      (L2.while concreteTest concreteBody concreteInitial names) := by
  subst abstractInitial
  intro state hypothesis
  unfold L2.while whileLoopE at hypothesis ⊢
  let abstractTestE : Except AbstractException Abstract → State → Prop :=
    fun value state => match value with
      | .error _ => False
      | .ok value => abstractTest value state
  let concreteTestE : Except ConcreteException Concrete → State → Prop :=
    fun value state => match value with
      | .error _ => False
      | .ok value => concreteTest value state
  let resultMap : Except ConcreteException Concrete → Except AbstractException Abstract
    | .error exception => .error (exceptionMap exception)
    | .ok value => .ok (valueMap value)
  let validE : Except ConcreteException Concrete → Prop
    | .error _ => True
    | .ok value => valid value
  have testE : ∀ value state, validE value →
      (abstractTestE (resultMap value) state ↔ concreteTestE value state) := by
    intro value state valueValid
    cases value with
    | error exception => exact Iff.rfl
    | ok value => exact testRelated value state valueValid
  have bodyE : ∀ value state, validE value →
      ¬(whileLoopEBody abstractBody (resultMap value) state).failed →
      (∀ next post,
        (next, post) ∈ (whileLoopEBody concreteBody value state).results →
        (resultMap next, post) ∈
          (whileLoopEBody abstractBody (resultMap value) state).results) ∧
      ¬(whileLoopEBody concreteBody value state).failed := by
    intro value state valueValid noFail
    cases value with
    | error exception =>
        refine ⟨?_, by simp [whileLoopEBody, pure]⟩
        intro next post member
        change (next, post) = (.error exception, state) at member
        cases member
        rfl
    | ok value => exact bodyRelated value valueValid state ⟨True.intro, noFail⟩
  have bodyPreservedE : ∀ value state, validE value →
      ¬(whileLoopEBody abstractBody (resultMap value) state).failed →
      ∀ next post,
        (next, post) ∈ (whileLoopEBody concreteBody value state).results → validE next := by
    intro value state valueValid noFail next post member
    cases value with
    | error exception =>
        change (next, post) = (.error exception, state) at member
        cases member
        trivial
    | ok value =>
        cases next with
        | error exception => trivial
        | ok next => exact bodyPreserved value state valueValid noFail next post member
  have loopNoFail := hypothesis.2
  change ¬(whileLoop abstractTestE (whileLoopEBody abstractBody)
      (resultMap (.ok concreteInitial)) state).failed at loopNoFail
  refine ⟨?_, ?_⟩
  · intro result post member
    change WhileResult concreteTestE (whileLoopEBody concreteBody)
      (some (.ok concreteInitial, state)) (some (result, post)) at member
    have mapped := whileResult_map testE bodyE bodyPreservedE initialValid
      (value := .ok concreteInitial) (state := state) loopNoFail member
    change WhileResult abstractTestE (whileLoopEBody abstractBody)
      (some (.ok (valueMap concreteInitial), state))
      (some (resultMap result, post)) at mapped
    cases result <;> exact mapped
  · intro concreteFailed
    rcases concreteFailed with finite | diverges
    · change WhileResult concreteTestE (whileLoopEBody concreteBody)
        (some (.ok concreteInitial, state)) none at finite
      have mapped := whileResult_map testE bodyE bodyPreservedE initialValid
        (value := .ok concreteInitial) (state := state) loopNoFail finite
      exact hypothesis.2 (Or.inl mapped)
    · apply diverges
      have abstractTerminates : WhileTerminates abstractTestE
          (whileLoopEBody abstractBody) (.ok (valueMap concreteInitial)) state :=
        Classical.byContradiction fun doesNotTerminate =>
          hypothesis.2 (Or.inr doesNotTerminate)
      exact whileTerminates_map testE bodyE bodyPreservedE initialValid
        (value := .ok concreteInitial) (state := state) loopNoFail abstractTerminates

/-- Total-map specialization for accumulators whose guard holds universally. -/
theorem corresTA_L2_while_map
    {valueMap : Concrete → Abstract}
    {exceptionMap : ConcreteException → AbstractException}
    {abstractTest : Abstract → State → Prop}
    {concreteTest : Concrete → State → Prop}
    {abstractBody : Abstract → L2.L2Program State AbstractException Abstract}
    {concreteBody : Concrete → L2.L2Program State ConcreteException Concrete}
    {abstractInitial : Abstract} {concreteInitial : Concrete} {names : List String}
    (testRelated : ∀ value state,
      abstractTest (valueMap value) state ↔ concreteTest value state)
    (bodyRelated : ∀ value, corresTA (fun _ : State => True) valueMap exceptionMap
      (abstractBody (valueMap value)) (concreteBody value))
    (initialRelated : abstractInitial = valueMap concreteInitial) :
    corresTA (fun _ : State => True) valueMap exceptionMap
      (L2.while abstractTest abstractBody abstractInitial names)
      (L2.while concreteTest concreteBody concreteInitial names) := by
  apply corresTA_L2_while_map_guarded (valid := fun _ => True)
  · intro value state _
    exact testRelated value state
  · intro value _
    exact bodyRelated value
  · intros
    trivial
  · trivial
  · exact initialRelated

/-- Identity-map specialization retained for exact accumulator loops. -/
theorem corresTA_L2_while
    {abstractTest concreteTest : Value → State → Prop}
    {abstractBody concreteBody :
      Value → L2.L2Program State Exception Value}
    {abstractInitial concreteInitial : Value} {names : List String}
    (testRelated : ∀ value state,
      abstractTest value state ↔ concreteTest value state)
    (bodyRelated : ∀ value, abstractBody value = concreteBody value)
    (initialRelated : abstractInitial = concreteInitial) :
    corresTA (fun _ : State => True) id id
      (L2.while abstractTest abstractBody abstractInitial names)
      (L2.while concreteTest concreteBody concreteInitial names) := by
  have testEquality : abstractTest = concreteTest := by
    funext value state
    exact propext (testRelated value state)
  have bodyEquality : abstractBody = concreteBody := funext bodyRelated
  rw [testEquality, bodyEquality, initialRelated]
  exact corresTA_refl _ _

/-! ## Pass-facing kernel -/

namespace Kernel

/-- Types visible to the certified word fragment. -/
inductive ValueType where
  | unit
  | bool
  | word (width : Nat)
  | sword (width : Nat)
  | uwordInt (width : Nat)
  | prod (left right : ValueType)
  deriving DecidableEq, Repr

/-- Value maps whose concrete round trip is valid for every source value. -/
inductive GuardTotal : ValueType -> Prop where
  | unit : GuardTotal .unit
  | bool : GuardTotal .bool
  | word (width : Nat) : GuardTotal (.word width)
  | sword (width : Nat) : GuardTotal (.sword width)
  | prod : GuardTotal left -> GuardTotal right -> GuardTotal (.prod left right)

/-- Value types whose concrete and abstract interpretations are definitionally equal. -/
inductive ExactValueType where
  | unit
  | bool
  deriving DecidableEq, Repr

def ExactValueType.type : ExactValueType -> ValueType
  | .unit => .unit
  | .bool => .bool

abbrev ExactValue : ExactValueType -> Type
  | .unit => Unit
  | .bool => Bool

namespace Source

/-- Concrete interpretation of a value type. -/
abbrev Value : ValueType -> Type
  | .unit => Unit
  | .bool => Bool
  | .word width => BitVec width
  | .sword width => BitVec width
  | .uwordInt _ => Int
  | .prod left right => Value left × Value right

def asWord {width : Nat} (value : Value (.word width)) : BitVec width := value
def asSignedWord {width : Nat} (value : Value (.sword width)) : BitVec width := value

def ofExact (type : ExactValueType) : ExactValue type -> Value type.type :=
  match type with
  | .unit => id
  | .bool => id

def toExact (type : ExactValueType) : Value type.type -> ExactValue type :=
  match type with
  | .unit => id
  | .bool => id

/-- Typed concrete expressions. There is no untyped or opaque expression node. -/
inductive Expr (Argument : ValueType) (State : Type u) : ValueType -> Type (u + 1) where
  | arg : Expr Argument State Argument
  | state (type : ValueType) (read : State -> Value type) : Expr Argument State type
  | unit : Expr Argument State .unit
  | bool (value : Bool) : Expr Argument State .bool
  | word (width : Nat) (value : BitVec width) : Expr Argument State (.word width)
  | sword (width : Nat) (value : BitVec width) : Expr Argument State (.sword width)
  | add {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State (.word width)
  | sub {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State (.word width)
  | ult {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | ule {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | eq {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | ubinary (width : WordWidth) (operator : UnsignedBinaryOp)
      (left right : Expr Argument State (.word width.bits)) :
      Expr Argument State (.word width.bits)
  | sbinary (width : WordWidth) (operator : SignedBinaryOp)
      (left right : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.sword width.bits)
  | uunary (width : WordWidth) (operator : UnsignedUnaryOp)
      (value : Expr Argument State (.word width.bits)) :
      Expr Argument State (.word width.bits)
  | sunary (width : WordWidth) (operator : SignedUnaryOp)
      (value : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.sword width.bits)
  | ucmp (width : WordWidth) (operator : WordComparison)
      (left right : Expr Argument State (.word width.bits)) :
      Expr Argument State .bool
  | scmp (width : WordWidth) (operator : WordComparison)
      (left right : Expr Argument State (.sword width.bits)) :
      Expr Argument State .bool
  | ushiftU (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.word valueWidth.bits))
      (count : Expr Argument State (.word countWidth.bits)) :
      Expr Argument State (.word valueWidth.bits)
  | ushiftS (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.word valueWidth.bits))
      (count : Expr Argument State (.sword countWidth.bits)) :
      Expr Argument State (.word valueWidth.bits)
  | sshiftU (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.sword valueWidth.bits))
      (count : Expr Argument State (.word countWidth.bits)) :
      Expr Argument State (.sword valueWidth.bits)
  | sshiftS (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.sword valueWidth.bits))
      (count : Expr Argument State (.sword countWidth.bits)) :
      Expr Argument State (.sword valueWidth.bits)
  | ucast (sourceWidth targetWidth : WordWidth)
      (value : Expr Argument State (.word sourceWidth.bits)) :
      Expr Argument State (.word targetWidth.bits)
  | scast (sourceWidth targetWidth : WordWidth)
      (value : Expr Argument State (.sword sourceWidth.bits)) :
      Expr Argument State (.sword targetWidth.bits)
  | unsignedToSigned (width : WordWidth)
      (value : Expr Argument State (.word width.bits)) :
      Expr Argument State (.sword width.bits)
  | signedToUnsigned (width : WordWidth)
      (value : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.word width.bits)
  | pair {left right : ValueType} (first : Expr Argument State left)
      (second : Expr Argument State right) : Expr Argument State (.prod left right)
  | fst {left right : ValueType} (value : Expr Argument State (.prod left right)) :
      Expr Argument State left
  | snd {left right : ValueType} (value : Expr Argument State (.prod left right)) :
      Expr Argument State right
  | uint (width : Nat) (value : Int) : Expr Argument State (.uwordInt width)
  | umod {width : Nat} (left right : Expr Argument State (.uwordInt width)) :
      Expr Argument State (.uwordInt width)
  | uneZero {width : Nat} (value : Expr Argument State (.uwordInt width)) :
      Expr Argument State .bool

def Expr.eval (argument : Value Argument) (state : State) :
    Expr Argument State type -> Value type
  | .arg => argument
  | .state _ read => read state
  | .unit => ()
  | .bool value => value
  | .word _ value => value
  | .sword _ value => value
  | .add left right => asWord (left.eval argument state) + asWord (right.eval argument state)
  | .sub left right => asWord (left.eval argument state) - asWord (right.eval argument state)
  | .ult left right => (asWord (left.eval argument state)).ult
      (asWord (right.eval argument state))
  | .ule left right => decide (asWord (left.eval argument state) <=
      asWord (right.eval argument state))
  | .eq left right => decide (asWord (left.eval argument state) =
      asWord (right.eval argument state))
  | .ubinary width operator left right => unsignedBinaryWord width operator
      (asWord (left.eval argument state)) (asWord (right.eval argument state))
  | .sbinary width operator left right => signedBinaryWord width operator
      (asSignedWord (left.eval argument state))
      (asSignedWord (right.eval argument state))
  | .uunary width operator value =>
      unsignedUnaryWord width operator (asWord (value.eval argument state))
  | .sunary width operator value =>
      signedUnaryWord width operator (asSignedWord (value.eval argument state))
  | .ucmp _ operator left right => compareNat operator
      (asWord (left.eval argument state)).toNat
      (asWord (right.eval argument state)).toNat
  | .scmp _ operator left right => compareInt operator
      (asSignedWord (left.eval argument state)).toInt
      (asSignedWord (right.eval argument state)).toInt
  | .ushiftU direction width _ value count =>
      unsignedShiftWord direction (asWord (value.eval argument state))
        (asWord (count.eval argument state)).toNat
  | .ushiftS direction width _ value count =>
      unsignedShiftWord direction (asWord (value.eval argument state))
        (asSignedWord (count.eval argument state)).toNat
  | .sshiftU direction width _ value count =>
      signedShiftWord direction (asSignedWord (value.eval argument state))
        (asWord (count.eval argument state)).toNat
  | .sshiftS direction width _ value count =>
      signedShiftWord direction (asSignedWord (value.eval argument state))
        (asSignedWord (count.eval argument state)).toNat
  | .ucast _ targetWidth value =>
      (asWord (value.eval argument state)).setWidth targetWidth.bits
  | .scast _ targetWidth value =>
      (asSignedWord (value.eval argument state)).signExtend targetWidth.bits
  | .unsignedToSigned _ value => asWord (value.eval argument state)
  | .signedToUnsigned _ value => asSignedWord (value.eval argument state)
  | .pair first second => (first.eval argument state, second.eval argument state)
  | .fst value => (value.eval argument state).1
  | .snd value => (value.eval argument state).2
  | .uint _ value => value
  | .umod left right => left.eval argument state % right.eval argument state
  | .uneZero value => decide (value.eval argument state ≠ 0)

/-- Reified concrete L2 syntax. Every executable leaf is represented explicitly. -/
inductive Syntax (Argument : ValueType) (State : Type u) :
    ValueType -> ValueType -> Type (u + 1) where
  | gets {exception result : ValueType} (value : Expr Argument State result)
      (names : List String) : Syntax Argument State exception result
  | guard {exception : ValueType} (test : Expr Argument State .bool) :
      Syntax Argument State exception .unit
  | exactGuard {exception : ValueType} (test : State -> Prop) :
      Syntax Argument State exception .unit
  | modify {exception : ValueType} (update : State -> State) :
      Syntax Argument State exception .unit
  | seq {exception middle result : ValueType}
      (first : Syntax Argument State exception middle)
      (next : Value middle -> Syntax Argument State exception result) :
      Syntax Argument State exception result
  | condition {exception result : ValueType} (test : Expr Argument State .bool)
      (thenBranch elseBranch : Syntax Argument State exception result) :
      Syntax Argument State exception result
  | «catch» {exception caught result : ValueType}
      (body : Syntax Argument State caught result)
      (handler : Value caught -> Syntax Argument State exception result) :
      Syntax Argument State exception result
  | «while» (exception result : ExactValueType)
      (test : Value result.type -> State -> Prop)
      (body : Value result.type ->
        L2.Syntax State (Value exception.type) (Value result.type))
      (initial : Value result.type) (names : List String) :
      Syntax Argument State exception.type result.type
  | whileMapped (exception result : ValueType)
      (test : Value result -> State -> Prop)
      (body : Value result -> Syntax Argument State exception result)
      (initial : Value result) (names : List String) (guardTotal : GuardTotal result) :
      Syntax Argument State exception result
  | whileMappedGuarded (exception result : ValueType)
      (test : Value result -> State -> Prop)
      (body : Value result -> Syntax Argument State exception result)
      (initial : Value result) (names : List String) :
      Syntax Argument State exception result
  | throw {exception result : ValueType} (value : Value exception)
      (names : List String) : Syntax Argument State exception result
  | skip {exception : ValueType} : Syntax Argument State exception .unit
  | fail {exception result : ValueType} : Syntax Argument State exception result

/-- Interpret source syntax only after the pure transformation phase. -/
noncomputable def Syntax.denote (argument : Value Argument) :
    Syntax Argument State Exception result ->
      L2.L2Program State (Value Exception) (Value result)
  | .gets value names => L2.gets (value.eval argument) names
  | .guard test => L2.guard fun state => test.eval argument state = true
  | .exactGuard test => L2.guard test
  | .modify update => L2.modify update
  | .seq first next =>
      L2.seq (first.denote argument) fun value => (next value).denote argument
  | .condition test thenBranch elseBranch =>
      L2.condition (fun state => test.eval argument state = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .catch body handler =>
      L2.catch (body.denote argument) fun exception =>
        (handler exception).denote argument
  | .while _ _ test body initial names =>
      L2.while test (fun value => (body value).denote) initial names
  | .whileMapped _ _ test body initial names _ =>
      L2.while test (fun value => (body value).denote argument) initial names
  | .whileMappedGuarded _ _ test body initial names =>
      L2.while test (fun value => (body value).denote argument) initial names
  | .throw exception names => L2.throw exception names
  | .skip => L2.skip
  | .fail => L2.fail

end Source

namespace Target

/-- Abstract interpretation of a value type. -/
abbrev Value : ValueType -> Type
  | .unit => Unit
  | .bool => Bool
  | .word _ => Nat
  | .sword _ => Int
  | .uwordInt _ => Nat
  | .prod left right => Value left × Value right

def asNat {width : Nat} (value : Value (.word width)) : Nat := value
def asInt {width : Nat} (value : Value (.sword width)) : Int := value

def ofExact (type : ExactValueType) : ExactValue type -> Value type.type :=
  match type with
  | .unit => id
  | .bool => id

def toExact (type : ExactValueType) : Value type.type -> ExactValue type :=
  match type with
  | .unit => id
  | .bool => id

/-- Typed abstract expressions; no constructor can contain a concrete word. -/
inductive Expr (Argument : ValueType) (State : Type u) : ValueType -> Type (u + 1) where
  | arg : Expr Argument State Argument
  | state (type : ValueType) (read : State -> Value type) : Expr Argument State type
  | unit : Expr Argument State .unit
  | bool (value : Bool) : Expr Argument State .bool
  | word (width : Nat) (value : Nat) : Expr Argument State (.word width)
  | sword (width : Nat) (value : Int) : Expr Argument State (.sword width)
  | add {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State (.word width)
  | sub {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State (.word width)
  | ult {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | ule {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | eq {width : Nat} (left right : Expr Argument State (.word width)) :
      Expr Argument State .bool
  | ubinary (width : WordWidth) (operator : UnsignedBinaryOp)
      (left right : Expr Argument State (.word width.bits)) :
      Expr Argument State (.word width.bits)
  | sbinary (width : WordWidth) (operator : SignedBinaryOp)
      (left right : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.sword width.bits)
  | uunary (width : WordWidth) (operator : UnsignedUnaryOp)
      (value : Expr Argument State (.word width.bits)) :
      Expr Argument State (.word width.bits)
  | sunary (width : WordWidth) (operator : SignedUnaryOp)
      (value : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.sword width.bits)
  | ucmp (width : WordWidth) (operator : WordComparison)
      (left right : Expr Argument State (.word width.bits)) :
      Expr Argument State .bool
  | scmp (width : WordWidth) (operator : WordComparison)
      (left right : Expr Argument State (.sword width.bits)) :
      Expr Argument State .bool
  | ushiftU (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.word valueWidth.bits))
      (count : Expr Argument State (.word countWidth.bits)) :
      Expr Argument State (.word valueWidth.bits)
  | ushiftS (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.word valueWidth.bits))
      (count : Expr Argument State (.sword countWidth.bits)) :
      Expr Argument State (.word valueWidth.bits)
  | sshiftU (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.sword valueWidth.bits))
      (count : Expr Argument State (.word countWidth.bits)) :
      Expr Argument State (.sword valueWidth.bits)
  | sshiftS (direction : ShiftDirection) (valueWidth countWidth : WordWidth)
      (value : Expr Argument State (.sword valueWidth.bits))
      (count : Expr Argument State (.sword countWidth.bits)) :
      Expr Argument State (.sword valueWidth.bits)
  | ucast (sourceWidth targetWidth : WordWidth)
      (value : Expr Argument State (.word sourceWidth.bits)) :
      Expr Argument State (.word targetWidth.bits)
  | scast (sourceWidth targetWidth : WordWidth)
      (value : Expr Argument State (.sword sourceWidth.bits)) :
      Expr Argument State (.sword targetWidth.bits)
  | unsignedToSigned (width : WordWidth)
      (value : Expr Argument State (.word width.bits)) :
      Expr Argument State (.sword width.bits)
  | signedToUnsigned (width : WordWidth)
      (value : Expr Argument State (.sword width.bits)) :
      Expr Argument State (.word width.bits)
  | pair {left right : ValueType} (first : Expr Argument State left)
      (second : Expr Argument State right) : Expr Argument State (.prod left right)
  | fst {left right : ValueType} (value : Expr Argument State (.prod left right)) :
      Expr Argument State left
  | snd {left right : ValueType} (value : Expr Argument State (.prod left right)) :
      Expr Argument State right
  | uint (width : Nat) (value : Nat) : Expr Argument State (.uwordInt width)
  | umod {width : Nat} (left right : Expr Argument State (.uwordInt width)) :
      Expr Argument State (.uwordInt width)
  | uneZero {width : Nat} (value : Expr Argument State (.uwordInt width)) :
      Expr Argument State .bool

def maxFor {Argument : ValueType} {State : Type u} {width : Nat}
    (_ : Expr Argument State (.word width)) : Nat := UWORD_MAX width

def Expr.eval (argument : Value Argument) (state : State) :
    Expr Argument State type -> Value type
  | .arg => argument
  | .state _ read => read state
  | .unit => ()
  | .bool value => value
  | .word _ value => value
  | .sword _ value => value
  | .add left right => asNat (left.eval argument state) + asNat (right.eval argument state)
  | .sub left right => asNat (left.eval argument state) - asNat (right.eval argument state)
  | .ult left right => decide (asNat (left.eval argument state) <
      asNat (right.eval argument state))
  | .ule left right => decide (asNat (left.eval argument state) <=
      asNat (right.eval argument state))
  | .eq left right => decide (asNat (left.eval argument state) =
      asNat (right.eval argument state))
  | .ubinary _ operator left right => unsignedBinary operator
      (asNat (left.eval argument state)) (asNat (right.eval argument state))
  | .sbinary width operator left right => signedBinary width.bits operator
      (asInt (left.eval argument state)) (asInt (right.eval argument state))
  | .uunary width operator value =>
      unsignedUnary width.bits operator (asNat (value.eval argument state))
  | .sunary width operator value =>
      signedUnary width.bits operator (asInt (value.eval argument state))
  | .ucmp _ operator left right => compareNat operator
      (asNat (left.eval argument state)) (asNat (right.eval argument state))
  | .scmp _ operator left right => compareInt operator
      (asInt (left.eval argument state)) (asInt (right.eval argument state))
  | .ushiftU direction _ _ value count => unsignedShift direction
      (asNat (value.eval argument state)) (asNat (count.eval argument state))
  | .ushiftS direction _ _ value count => unsignedShift direction
      (asNat (value.eval argument state)) (asInt (count.eval argument state)).toNat
  | .sshiftU direction _ _ value count => signedShift direction
      (asInt (value.eval argument state)) (asNat (count.eval argument state))
  | .sshiftS direction _ _ value count => signedShift direction
      (asInt (value.eval argument state)) (asInt (count.eval argument state)).toNat
  | .ucast _ targetWidth value =>
      asNat (value.eval argument state) % 2 ^ targetWidth.bits
  | .scast _ targetWidth value =>
      (asInt (value.eval argument state)).bmod (2 ^ targetWidth.bits)
  | .unsignedToSigned _ value => Int.ofNat (asNat (value.eval argument state))
  | .signedToUnsigned width value =>
      signedToUnsignedValue width.bits (asInt (value.eval argument state))
  | .pair first second => (first.eval argument state, second.eval argument state)
  | .fst value => (value.eval argument state).1
  | .snd value => (value.eval argument state).2
  | .uint _ value => value
  | .umod left right => left.eval argument state % right.eval argument state
  | .uneZero value => decide (value.eval argument state ≠ 0)

/-- Reified transformed L2 syntax, including every generated runtime guard. -/
inductive Syntax (Argument : ValueType) (State : Type u) :
    ValueType -> ValueType -> Type (u + 1) where
  | gets {exception result : ValueType} (value : Expr Argument State result)
      (names : List String) : Syntax Argument State exception result
  | guard {exception : ValueType} (test : Value Argument -> State -> Prop) :
      Syntax Argument State exception .unit
  | exactGuard {exception : ValueType} (test : State -> Prop) :
      Syntax Argument State exception .unit
  | modify {exception : ValueType} (update : State -> State) :
      Syntax Argument State exception .unit
  | seq {exception middle result : ValueType}
      (first : Syntax Argument State exception middle)
      (next : Value middle -> Syntax Argument State exception result) :
      Syntax Argument State exception result
  | condition {exception result : ValueType} (test : Expr Argument State .bool)
      (thenBranch elseBranch : Syntax Argument State exception result) :
      Syntax Argument State exception result
  | «catch» {exception caught result : ValueType}
      (body : Syntax Argument State caught result)
      (handler : Value caught -> Syntax Argument State exception result) :
      Syntax Argument State exception result
  | «while» (exception result : ExactValueType)
      (test : Value result.type -> State -> Prop)
      (body : Value result.type ->
        L2.Syntax State (Value exception.type) (Value result.type))
      (initial : Value result.type) (names : List String) :
      Syntax Argument State exception.type result.type
  | whileMapped (exception result : ValueType)
      (test : Value result -> State -> Prop)
      (body : Value result -> Syntax Argument State exception result)
      (initial : Value result) (names : List String) :
      Syntax Argument State exception result
  | whileMappedGuarded (exception result : ValueType)
      (test : Value result -> State -> Prop)
      (body : Value result -> Syntax Argument State exception result)
      (initial : Value result) (names : List String) :
      Syntax Argument State exception result
  | throw {exception result : ValueType} (value : Value exception)
      (names : List String) : Syntax Argument State exception result
  | skip {exception : ValueType} : Syntax Argument State exception .unit
  | fail {exception result : ValueType} : Syntax Argument State exception result

/-- Denotation is intentionally separate from the computable syntax transform. -/
noncomputable def Syntax.denote (argument : Value Argument) :
    Syntax Argument State Exception result ->
      L2.L2Program State (Value Exception) (Value result)
  | .gets value names => L2.gets (value.eval argument) names
  | .guard test => L2.guard (test argument)
  | .exactGuard test => L2.guard test
  | .modify update => L2.modify update
  | .seq first next =>
      L2.seq (first.denote argument) fun value => (next value).denote argument
  | .condition test thenBranch elseBranch =>
      L2.condition (fun state => test.eval argument state = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .catch body handler =>
      L2.catch (body.denote argument) fun exception =>
        (handler exception).denote argument
  | .while _ _ test body initial names =>
      L2.while test (fun value => (body value).denote) initial names
  | .whileMapped _ _ test body initial names =>
      L2.while test (fun value => (body value).denote argument) initial names
  | .whileMappedGuarded _ _ test body initial names =>
      L2.while test (fun value => (body value).denote argument) initial names
  | .throw exception names => L2.throw exception names
  | .skip => L2.skip
  | .fail => L2.fail

end Target

/-- The concrete/abstract interpretation pair and its guarded certificate. -/
structure TypeMap (type : ValueType) where
  certificate : valid_typ_abs_fn (Target.Value type) (Source.Value type)

def intUnsignedCanonical (width : Nat) (value : Int) : Prop :=
  0 ≤ value ∧ value < (2 ^ width : Nat)

instance (width : Nat) (value : Int) : Decidable (intUnsignedCanonical width value) := by
  unfold intUnsignedCanonical
  infer_instance

def abstractUnsignedInt (width : Nat) (value : Int) : Nat :=
  if intUnsignedCanonical width value then value.toNat else 2 ^ width

def valid_typ_abs_fn_unsignedInt (width : Nat) : valid_typ_abs_fn Nat Int where
  abstractGuard := fun value => value < 2 ^ width
  concreteGuard := fun value => value < 2 ^ width
  abstract := abstractUnsignedInt width
  concretize := Int.ofNat
  abstract_concretize := by
    intro value bounded
    have canonical : intUnsignedCanonical width (Int.ofNat value) := by
      exact ⟨by simp, Int.ofNat_lt.2 bounded⟩
    unfold abstractUnsignedInt
    rw [if_pos canonical]
    simp
  concretize_abstract := by
    intro value bounded
    unfold abstractUnsignedInt at bounded ⊢
    by_cases canonical : intUnsignedCanonical width value
    · rw [if_pos canonical] at bounded ⊢
      calc
        Int.ofNat value.toNat = max value 0 := Int.ofNat_toNat value
        _ = value := by
          unfold intUnsignedCanonical at canonical
          omega
    · rw [if_neg canonical] at bounded
      exact (Nat.lt_irrefl _ bounded).elim

theorem intUnsignedCanonical_of_abstractGuard (width : Nat) (value : Int)
    (guard : abstractUnsignedInt width value < 2 ^ width) :
    intUnsignedCanonical width value := by
  by_cases canonical : intUnsignedCanonical width value
  · exact canonical
  · have impossible : 2 ^ width < 2 ^ width := by
      unfold abstractUnsignedInt at guard
      rw [if_neg canonical] at guard
      exact guard
    exact (Nat.lt_irrefl _ impossible).elim

theorem abstractGuard_of_intUnsignedCanonical (width : Nat) (value : Int)
    (canonical : intUnsignedCanonical width value) :
    abstractUnsignedInt width value < 2 ^ width := by
  have roundTrip : Int.ofNat value.toNat = value := by
    calc
      Int.ofNat value.toNat = max value 0 := Int.ofNat_toNat value
      _ = value := by
        unfold intUnsignedCanonical at canonical
        omega
  unfold abstractUnsignedInt
  rw [if_pos canonical]
  apply Int.ofNat_lt.mp
  calc
    Int.ofNat value.toNat = value := roundTrip
    _ < Int.ofNat (2 ^ width) := canonical.2

theorem abstractUnsignedInt_ne_zero (width : Nat) (value : Int) :
    abstractUnsignedInt width value ≠ 0 ↔ value ≠ 0 := by
  by_cases canonical : intUnsignedCanonical width value
  · unfold abstractUnsignedInt
    rw [if_pos canonical]
    unfold intUnsignedCanonical at canonical
    omega
  · have nonzero : value ≠ 0 := by
      intro equality
      subst value
      apply canonical
      exact ⟨by simp, Int.ofNat_lt.2 (Nat.two_pow_pos width)⟩
    constructor
    · intro _
      exact nonzero
    · intro _
      unfold abstractUnsignedInt
      rw [if_neg canonical]
      exact Nat.ne_of_gt (Nat.two_pow_pos width)

theorem abstractUnsignedInt_emod (width : Nat) (left right : Int)
    (leftCanonical : intUnsignedCanonical width left)
    (rightCanonical : intUnsignedCanonical width right) (rightNonzero : right ≠ 0) :
    abstractUnsignedInt width left % abstractUnsignedInt width right =
      abstractUnsignedInt width (left % right) := by
  have rightPositive : 0 < right := by
    unfold intUnsignedCanonical at rightCanonical
    omega
  have resultCanonical : intUnsignedCanonical width (left % right) := by
    have nonnegative := Int.emod_nonneg left rightNonzero
    have belowRight := Int.emod_lt_of_pos left rightPositive
    unfold intUnsignedCanonical at rightCanonical ⊢
    change 0 ≤ left % right ∧ left % right < (2 ^ width : Nat)
    exact ⟨nonnegative, by omega⟩
  unfold abstractUnsignedInt
  rw [if_pos leftCanonical, if_pos rightCanonical, if_pos resultCanonical]
  exact (Int.toNat_emod leftCanonical.1 rightCanonical.1).symm

def typeMap : (type : ValueType) -> TypeMap type
  | .unit =>
      { certificate := valid_typ_abs_fn_id Unit }
  | .bool =>
      { certificate := valid_typ_abs_fn_id Bool }
  | .word width =>
      { certificate := valid_typ_abs_fn_bitVec width }
  | .sword width =>
      { certificate := valid_typ_abs_fn_bitVecSigned width }
  | .uwordInt width =>
      { certificate := valid_typ_abs_fn_unsignedInt width }
  | .prod left right =>
      let leftMap := typeMap left
      let rightMap := typeMap right
      { certificate := valid_typ_abs_fn_prod leftMap.certificate rightMap.certificate }

namespace TypeMap

def abstract (map : TypeMap type) : Source.Value type -> Target.Value type :=
  match type with
  | .unit => id
  | .bool => id
  | .word _ => BitVec.toNat
  | .sword _ => BitVec.toInt
  | .uwordInt width => abstractUnsignedInt width
  | .prod left right => fun value =>
      ((typeMap left).abstract value.1, (typeMap right).abstract value.2)

def concretize (map : TypeMap type) : Target.Value type -> Source.Value type :=
  match type with
  | .unit => id
  | .bool => id
  | .word width => BitVec.ofNat width
  | .sword width => BitVec.ofInt width
  | .uwordInt _ => Int.ofNat
  | .prod left right => fun value =>
      ((typeMap left).concretize value.1, (typeMap right).concretize value.2)

theorem sourceRoundTrip (value : Source.Value type)
    (guard : (typeMap type).certificate.concreteGuard
      ((typeMap type).abstract value)) :
    (typeMap type).concretize ((typeMap type).abstract value) = value := by
  cases type with
  | unit => rfl
  | bool => rfl
  | word width => exact bitVec_ofNat_toNat value
  | sword width => exact BitVec.ofInt_toInt
  | uwordInt width =>
      exact (valid_typ_abs_fn_unsignedInt width).concretize_abstract value guard
  | prod left right =>
      exact Prod.ext
        (sourceRoundTrip (type := left) value.1 guard.1)
        (sourceRoundTrip (type := right) value.2 guard.2)

theorem concreteGuard_abstract (total : GuardTotal type) (value : Source.Value type) :
    (typeMap type).certificate.concreteGuard ((typeMap type).abstract value) := by
  induction total with
  | unit => trivial
  | bool => trivial
  | word width => trivial
  | sword width => trivial
  | prod leftTotal rightTotal leftInduction rightInduction =>
      exact ⟨leftInduction value.1, rightInduction value.2⟩

@[simp] theorem abstract_unit (value : Unit) :
    (typeMap .unit).abstract value = value := rfl

@[simp] theorem abstract_bool (value : Bool) :
    (typeMap .bool).abstract value = value := rfl

@[simp] theorem concretize_unit (value : Unit) :
    (typeMap .unit).concretize value = value := rfl

@[simp] theorem concretize_bool (value : Bool) :
    (typeMap .bool).concretize value = value := rfl

@[simp] theorem certificate_concretize_unit (value : Unit) :
    (typeMap .unit).certificate.concretize value = value := rfl

@[simp] theorem certificate_concretize_bool (value : Bool) :
    (typeMap .bool).certificate.concretize value = value := rfl

@[simp] theorem abstract_word (value : BitVec width) :
    (typeMap (.word width)).abstract value = value.toNat := rfl

@[simp] theorem abstract_sword (value : BitVec width) :
    (typeMap (.sword width)).abstract value = value.toInt := rfl

@[simp] theorem abstract_prod (value : Source.Value (.prod left right)) :
    (typeMap (.prod left right)).abstract value =
      ((typeMap left).abstract value.1, (typeMap right).abstract value.2) := rfl

end TypeMap

/-- A generated target paired with partial, runtime-guarded `corresTA`. -/
structure Certificate {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType}
    (source : Source.Syntax Argument State Exception Result) where
  target : Target.Syntax Argument State Exception Result
  corres : forall concreteArgument,
    corresTA (fun _ => True) (typeMap Result).abstract (typeMap Exception).abstract
      (target.denote ((typeMap Argument).abstract concreteArgument))
      (source.denote concreteArgument)

end Kernel

end Zag.Lang.AutoCorres.WordAbstract
