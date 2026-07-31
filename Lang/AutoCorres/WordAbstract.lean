import Lang.AutoCorres.L2
import Lang.AutoCorres.CorresXF

/-!
# Word abstraction

Corresponds to [`tools/autocorres/WordAbstract.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/WordAbstract.thy).

This foundation intentionally omits signed-word-to-`Int` abstraction.  Lean's
generic `BitVec` API does not currently supply the complete signed arithmetic,
division, remainder, shift, and cast laws needed to reproduce the guarded
upstream package without adding a second signed-word model.  No signed wrap is
therefore identified with unbounded integer arithmetic here.
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

/-- Word abstraction as an exact refinement between its closed L2 SSA endpoints. -/
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

private theorem mem_L2_seq_iff
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

private theorem failed_L2_seq_iff
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

private theorem guard_member (condition : State → Prop) {state : State}
    (holds : condition state) :
    (Except.ok (), state) ∈ (L2.guard (Exception := Exception) condition state).results := by
  rw [L2.guard, mem_liftE, mem_guard]
  exact ⟨holds, rfl, rfl⟩

private theorem guard_holds_of_noFail (condition : State → Prop) {state : State}
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

/--
Current L2 loop semantics supports the exact-map rule: extensionally equal
tests and bodies yield identity type abstraction.  A non-identity loop result
map requires a dedicated loop bisimulation and is intentionally not asserted.
-/
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

/-- Types visible to the certified unsigned fragment. -/
inductive ValueType where
  | unit
  | bool
  | word (width : Nat)
  deriving DecidableEq, Repr

namespace Source

/-- Concrete interpretation of a value type. -/
abbrev Value : ValueType -> Type
  | .unit => Unit
  | .bool => Bool
  | .word width => BitVec width

def asWord {width : Nat} (value : Value (.word width)) : BitVec width := value

/-- Typed concrete expressions. There is no untyped or opaque expression node. -/
inductive Expr (Argument : ValueType) (State : Type u) : ValueType -> Type (u + 1) where
  | arg : Expr Argument State Argument
  | state (type : ValueType) (read : State -> Value type) : Expr Argument State type
  | unit : Expr Argument State .unit
  | bool (value : Bool) : Expr Argument State .bool
  | word (width : Nat) (value : BitVec width) : Expr Argument State (.word width)
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

def Expr.eval (argument : Value Argument) (state : State) :
    Expr Argument State type -> Value type
  | .arg => argument
  | .state _ read => read state
  | .unit => ()
  | .bool value => value
  | .word _ value => value
  | .add left right => asWord (left.eval argument state) + asWord (right.eval argument state)
  | .sub left right => asWord (left.eval argument state) - asWord (right.eval argument state)
  | .ult left right => (asWord (left.eval argument state)).ult
      (asWord (right.eval argument state))
  | .ule left right => decide (asWord (left.eval argument state) <=
      asWord (right.eval argument state))
  | .eq left right => decide (asWord (left.eval argument state) =
      asWord (right.eval argument state))

/-- Reified concrete L2 syntax. Every executable leaf is represented explicitly. -/
inductive Syntax (Argument : ValueType) (State : Type u) :
    ValueType -> ValueType -> Type (u + 1) where
  | gets {exception result : ValueType} (value : Expr Argument State result)
      (names : List String) : Syntax Argument State exception result
  | guard {exception : ValueType} (test : Expr Argument State .bool) :
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
  | .seq first next =>
      L2.seq (first.denote argument) fun value => (next value).denote argument
  | .condition test thenBranch elseBranch =>
      L2.condition (fun state => test.eval argument state = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .catch body handler =>
      L2.catch (body.denote argument) fun exception =>
        (handler exception).denote argument
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

def asNat {width : Nat} (value : Value (.word width)) : Nat := value

/-- Typed abstract expressions; no constructor can contain a concrete word. -/
inductive Expr (Argument : ValueType) (State : Type u) : ValueType -> Type (u + 1) where
  | arg : Expr Argument State Argument
  | state (type : ValueType) (read : State -> Value type) : Expr Argument State type
  | unit : Expr Argument State .unit
  | bool (value : Bool) : Expr Argument State .bool
  | word (width : Nat) (value : Nat) : Expr Argument State (.word width)
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

def maxFor {Argument : ValueType} {State : Type u} {width : Nat}
    (_ : Expr Argument State (.word width)) : Nat := UWORD_MAX width

def Expr.eval (argument : Value Argument) (state : State) :
    Expr Argument State type -> Value type
  | .arg => argument
  | .state _ read => read state
  | .unit => ()
  | .bool value => value
  | .word _ value => value
  | .add left right => asNat (left.eval argument state) + asNat (right.eval argument state)
  | .sub left right => asNat (left.eval argument state) - asNat (right.eval argument state)
  | .ult left right => decide (asNat (left.eval argument state) <
      asNat (right.eval argument state))
  | .ule left right => decide (asNat (left.eval argument state) <=
      asNat (right.eval argument state))
  | .eq left right => decide (asNat (left.eval argument state) =
      asNat (right.eval argument state))

/-- Reified transformed L2 syntax, including every generated runtime guard. -/
inductive Syntax (Argument : ValueType) (State : Type u) :
    ValueType -> ValueType -> Type (u + 1) where
  | gets {exception result : ValueType} (value : Expr Argument State result)
      (names : List String) : Syntax Argument State exception result
  | guard {exception : ValueType} (test : Value Argument -> State -> Prop) :
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
  | .seq first next =>
      L2.seq (first.denote argument) fun value => (next value).denote argument
  | .condition test thenBranch elseBranch =>
      L2.condition (fun state => test.eval argument state = true)
        (thenBranch.denote argument) (elseBranch.denote argument)
  | .catch body handler =>
      L2.catch (body.denote argument) fun exception =>
        (handler exception).denote argument
  | .throw exception names => L2.throw exception names
  | .skip => L2.skip
  | .fail => L2.fail

end Target

/-- The concrete/abstract interpretation pair and its exact WordAbstract certificate. -/
structure TypeMap (type : ValueType) where
  certificate : valid_typ_abs_fn (Target.Value type) (Source.Value type)
  sourceRoundTripGuard : forall value,
    certificate.concreteGuard (certificate.abstract value)

def typeMap : (type : ValueType) -> TypeMap type
  | .unit =>
      { certificate := valid_typ_abs_fn_id Unit
        sourceRoundTripGuard := by simp [valid_typ_abs_fn_id] }
  | .bool =>
      { certificate := valid_typ_abs_fn_id Bool
        sourceRoundTripGuard := by simp [valid_typ_abs_fn_id] }
  | .word width =>
      { certificate := valid_typ_abs_fn_bitVec width
        sourceRoundTripGuard := by simp [valid_typ_abs_fn_bitVec] }

namespace TypeMap

def abstract (map : TypeMap type) : Source.Value type -> Target.Value type :=
  match type with
  | .unit => id
  | .bool => id
  | .word _ => BitVec.toNat

def concretize (map : TypeMap type) : Target.Value type -> Source.Value type :=
  match type with
  | .unit => id
  | .bool => id
  | .word width => BitVec.ofNat width

@[simp] theorem sourceRoundTrip (map : TypeMap type) (value : Source.Value type) :
    map.concretize (map.abstract value) = value := by
  cases type with
  | unit => rfl
  | bool => rfl
  | word width => exact bitVec_ofNat_toNat value

@[simp] theorem abstract_unit (value : Unit) :
    (typeMap .unit).abstract value = value := rfl

@[simp] theorem abstract_bool (value : Bool) :
    (typeMap .bool).abstract value = value := rfl

@[simp] theorem abstract_word (value : BitVec width) :
    (typeMap (.word width)).abstract value = value.toNat := rfl

end TypeMap

/-- A generated target paired with exact, runtime-guarded `corresTA`. -/
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
