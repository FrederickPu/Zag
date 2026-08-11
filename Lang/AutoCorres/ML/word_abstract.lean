import Lang.AutoCorres.WordAbstract
import Lang.AutoCorres.L2

/-!
# Proof-producing word abstraction kernel

Corresponds only to [`tools/autocorres/word_abstract.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/word_abstract.ML).

This is the guarded local proof kernel of the upstream scalar conversion.  It
supports the 8/16/32/64-bit signed and unsigned operation matrix.  Calls, heap
operations, specifications, and recursion groups are local integration
gaps outside this typed syntax; neither identity rewriting nor `L2.fail` is a fallback.

Source and target terms have different type interpretations. In particular, a
source word is a `BitVec width`, while its target is a `Nat`. Function inputs
are represented by typed `arg` nodes. HOAS continuations carry support for every
concrete input, transformation recurses on that package, and the sequence and
catch correspondence rules prove each generated abstract continuation against
its concrete body. Program denotation is noncomputable because L2 conditionals
are noncomputable; recognition and transformation are ordinary pure functions.
-/

namespace Zag.Lang.AutoCorres.ML.WordAbstract

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.WordAbstract
open Zag.Lang.AutoCorres.WordAbstract.Kernel

namespace Source

export Zag.Lang.AutoCorres.WordAbstract.Kernel.Source
  (Value asWord asSignedWord Expr Syntax)
export Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Expr (eval)
export Zag.Lang.AutoCorres.WordAbstract.Kernel.Source.Syntax (denote)

end Source

namespace Target

export Zag.Lang.AutoCorres.WordAbstract.Kernel.Target
  (Value asNat asInt Expr maxFor Syntax)
export Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Expr (eval)
export Zag.Lang.AutoCorres.WordAbstract.Kernel.Target.Syntax (denote)

end Target

namespace TypeMap

export Zag.Lang.AutoCorres.WordAbstract.Kernel.TypeMap
  (abstract concretize sourceRoundTrip concreteGuard_abstract abstract_unit abstract_bool abstract_word
    abstract_sword abstract_prod)

end TypeMap

export Zag.Lang.AutoCorres.WordAbstract.Kernel
  (ValueType GuardTotal ExactValueType ExactValue TypeMap typeMap Certificate)

universe u

/-- A transformed value expression, its generated guard, and its value proof. -/
structure ValueEvidence {Argument : ValueType} {State : Type u} {type : ValueType}
    (source : Source.Expr Argument State type) where
  target : Target.Expr Argument State type
  guard : Target.Value Argument -> State -> Prop
  related : forall concreteArgument state,
    abstract_val (guard ((typeMap Argument).abstract concreteArgument) state)
      (target.eval ((typeMap Argument).abstract concreteArgument) state)
      (typeMap type).abstract (source.eval concreteArgument state)

theorem ValueEvidence.proposition
    {source : Source.Expr Argument State .bool} (evidence : ValueEvidence source)
    (concreteArgument : Source.Value Argument) (state : State) :
    abstract_val (evidence.guard ((typeMap Argument).abstract concreteArgument) state)
      (evidence.target.eval ((typeMap Argument).abstract concreteArgument) state = true)
      id (source.eval concreteArgument state = true) := by
  unfold abstract_val
  intro generated
  have equality : evidence.target.eval
      ((typeMap Argument).abstract concreteArgument) state =
      source.eval concreteArgument state := by
    simpa only [TypeMap.abstract_bool] using
      evidence.related concreteArgument state generated
  apply propext
  rw [equality]
  exact Iff.rfl

namespace Expr

/--
Evidence for every recognized expression rule. Operation laws are selected by
the kernel and cannot be supplied by a caller.
-/
inductive Supported {Argument : ValueType} {State : Type u} :
    Source.Expr Argument State type -> Type (u + 1) where
  | arg : Supported .arg
  | state (type : ValueType) (read : State -> Source.Value type) :
      Supported (.state type read)
  | unit : Supported .unit
  | bool (value : Bool) : Supported (.bool value)
  | word (width : Nat) (value : BitVec width) : Supported (.word width value)
  | sword (width : Nat) (value : BitVec width) : Supported (.sword width value)
  | uint (width : Nat) (value : Int) : Supported (.uint width value)
  | umod {left right : Source.Expr Argument State (.uwordInt width)} :
      Supported left -> Supported right -> Supported (.umod left right)
  | uneZero {value : Source.Expr Argument State (.uwordInt width)} :
      Supported value -> Supported (.uneZero value)
  | add {left right : Source.Expr Argument State (.word width)} :
      Supported left -> Supported right -> Supported (.add left right)
  | sub {left right : Source.Expr Argument State (.word width)} :
      Supported left -> Supported right -> Supported (.sub left right)
  | ult {left right : Source.Expr Argument State (.word width)} :
      Supported left -> Supported right -> Supported (.ult left right)
  | ule {left right : Source.Expr Argument State (.word width)} :
      Supported left -> Supported right -> Supported (.ule left right)
  | eq {left right : Source.Expr Argument State (.word width)} :
      Supported left -> Supported right -> Supported (.eq left right)
  | ubinary {left right : Source.Expr Argument State (.word width.bits)} :
      Supported left -> Supported right -> Supported (.ubinary width operator left right)
  | sbinary {left right : Source.Expr Argument State (.sword width.bits)} :
      Supported left -> Supported right -> Supported (.sbinary width operator left right)
  | uunary {value : Source.Expr Argument State (.word width.bits)} :
      Supported value -> Supported (.uunary width operator value)
  | sunary {value : Source.Expr Argument State (.sword width.bits)} :
      Supported value -> Supported (.sunary width operator value)
  | ucmp {left right : Source.Expr Argument State (.word width.bits)} :
      Supported left -> Supported right -> Supported (.ucmp width operator left right)
  | scmp {left right : Source.Expr Argument State (.sword width.bits)} :
      Supported left -> Supported right -> Supported (.scmp width operator left right)
  | ushiftU {value : Source.Expr Argument State (.word valueWidth.bits)}
      {count : Source.Expr Argument State (.word countWidth.bits)} :
      Supported value -> Supported count ->
        Supported (.ushiftU direction valueWidth countWidth value count)
  | ushiftS {value : Source.Expr Argument State (.word valueWidth.bits)}
      {count : Source.Expr Argument State (.sword countWidth.bits)} :
      Supported value -> Supported count ->
        Supported (.ushiftS direction valueWidth countWidth value count)
  | sshiftU {value : Source.Expr Argument State (.sword valueWidth.bits)}
      {count : Source.Expr Argument State (.word countWidth.bits)} :
      Supported value -> Supported count ->
        Supported (.sshiftU direction valueWidth countWidth value count)
  | sshiftS {value : Source.Expr Argument State (.sword valueWidth.bits)}
      {count : Source.Expr Argument State (.sword countWidth.bits)} :
      Supported value -> Supported count ->
        Supported (.sshiftS direction valueWidth countWidth value count)
  | ucast {value : Source.Expr Argument State (.word sourceWidth.bits)} :
      Supported value -> Supported (.ucast sourceWidth targetWidth value)
  | scast {value : Source.Expr Argument State (.sword sourceWidth.bits)} :
      Supported value -> Supported (.scast sourceWidth targetWidth value)
  | unsignedToSigned {value : Source.Expr Argument State (.word width.bits)} :
      Supported value -> Supported (.unsignedToSigned width value)
  | signedToUnsigned {value : Source.Expr Argument State (.sword width.bits)} :
      Supported value -> Supported (.signedToUnsigned width value)
  | pair {first : Source.Expr Argument State left}
      {second : Source.Expr Argument State right} :
      Supported first -> Supported second -> Supported (.pair first second)
  | fst {value : Source.Expr Argument State (.prod left right)} :
      Supported value -> Supported (.fst value)
  | snd {value : Source.Expr Argument State (.prod left right)} :
      Supported value -> Supported (.snd value)

/-- Recognition is complete for the deliberately small expression grammar. -/
def supported : (source : Source.Expr Argument State type) -> Supported source
  | .arg => .arg
  | .state type read => .state type read
  | .unit => .unit
  | .bool value => .bool value
  | .word width value => .word width value
  | .sword width value => .sword width value
  | .uint width value => .uint width value
  | .umod left right => .umod (supported left) (supported right)
  | .uneZero value => .uneZero (supported value)
  | .add left right => .add (supported left) (supported right)
  | .sub left right => .sub (supported left) (supported right)
  | .ult left right => .ult (supported left) (supported right)
  | .ule left right => .ule (supported left) (supported right)
  | .eq left right => .eq (supported left) (supported right)
  | .ubinary _ _ left right => .ubinary (supported left) (supported right)
  | .sbinary _ _ left right => .sbinary (supported left) (supported right)
  | .uunary _ _ value => .uunary (supported value)
  | .sunary _ _ value => .sunary (supported value)
  | .ucmp _ _ left right => .ucmp (supported left) (supported right)
  | .scmp _ _ left right => .scmp (supported left) (supported right)
  | .ushiftU _ _ _ value count => .ushiftU (supported value) (supported count)
  | .ushiftS _ _ _ value count => .ushiftS (supported value) (supported count)
  | .sshiftU _ _ _ value count => .sshiftU (supported value) (supported count)
  | .sshiftS _ _ _ value count => .sshiftS (supported value) (supported count)
  | .ucast _ _ value => .ucast (supported value)
  | .scast _ _ value => .scast (supported value)
  | .unsignedToSigned _ value => .unsignedToSigned (supported value)
  | .signedToUnsigned _ value => .signedToUnsigned (supported value)
  | .pair first second => .pair (supported first) (supported second)
  | .fst value => .fst (supported value)
  | .snd value => .snd (supported value)

private theorem unsignedComparison_exact (operator : WordComparison) :
    abstract_bool_binop (fun _ _ => True)
      (BitVec.toNat : BitVec width → Nat) (compareNat operator)
      (fun left right => compareNat operator left.toNat right.toNat) := by
  intro left right _
  rfl

private theorem signedComparison_exact (operator : WordComparison) :
    abstract_bool_binop (fun _ _ => True)
      (BitVec.toInt : BitVec width → Int) (compareInt operator)
      (fun left right => compareInt operator left.toInt right.toInt) := by
  intro left right _
  rfl

/-- Pure expression conversion with side-condition generation. -/
def transform : {source : Source.Expr Argument State type} ->
    Supported source -> ValueEvidence source
  | _, .arg =>
      { target := .arg
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .state type read =>
      { target := .state type fun state => (typeMap type).abstract (read state)
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .unit =>
      { target := .unit
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .bool value =>
      { target := .bool value
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .word width value =>
      { target := .word width value.toNat
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .sword width value =>
      { target := .sword width value.toInt
        guard := fun _ _ => True
        related := by intros; intro _; simp [Target.Expr.eval, Source.Expr.eval] }
  | _, .uint width value =>
      { target := .uint width (abstractUnsignedInt width value)
        guard := fun _ _ => True
        related := by intros; intro _; rfl }
  | _, .umod leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .umod left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\
            (typeMap (.uwordInt _)).certificate.concreteGuard
              (left.target.eval argument state) /\
            (typeMap (.uwordInt _)).certificate.concreteGuard
              (right.target.eval argument state) /\
            right.target.eval argument state ≠ 0
        related := by
          intro concreteArgument state guard
          have leftEq := left.related concreteArgument state guard.1
          have rightEq := right.related concreteArgument state guard.2.1
          simp only [Target.Expr.eval, Source.Expr.eval]
          rw [leftEq, rightEq] at guard ⊢
          have leftGuard := guard.2.2.1
          have rightGuard := guard.2.2.2.1
          change abstractUnsignedInt _ _ < 2 ^ _ at leftGuard
          change abstractUnsignedInt _ _ < 2 ^ _ at rightGuard
          exact abstractUnsignedInt_emod _ _ _
            (intUnsignedCanonical_of_abstractGuard _ _ leftGuard)
            (intUnsignedCanonical_of_abstractGuard _ _ rightGuard)
            ((abstractUnsignedInt_ne_zero _ _).mp guard.2.2.2.2) }
  | _, .uneZero valueSupported =>
      let value := transform valueSupported
      { target := .uneZero value.target
        guard := value.guard
        related := by
          intro concreteArgument state guard
          have equality := value.related concreteArgument state guard
          simp only [Target.Expr.eval, Source.Expr.eval, TypeMap.abstract_bool]
          rw [equality]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact abstractUnsignedInt_ne_zero _ _ }
  | _, .add leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .add left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\
            Target.asNat (left.target.eval argument state) +
              Target.asNat (right.target.eval argument state) <=
              Target.maxFor left.target
        related := by
          intro concreteArgument state
          simpa [Target.asNat, Target.maxFor, Target.Expr.eval, Source.Expr.eval,
            Source.asWord, Target.Value, Source.Value, typeMap, TypeMap.abstract,
            valid_typ_abs_fn_bitVec] using
            abstract_expr_binop bitVec_abstract_binop_add
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .sub leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .sub left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\
            Target.asNat (right.target.eval argument state) <=
              Target.asNat (left.target.eval argument state)
        related := by
          intro concreteArgument state
          simpa [Target.asNat, Target.Expr.eval, Source.Expr.eval,
            Source.asWord, Target.Value, Source.Value, typeMap, TypeMap.abstract,
            valid_typ_abs_fn_bitVec] using
            abstract_expr_binop bitVec_abstract_binop_sub
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .ult (left := sourceLeft) (right := sourceRight)
      leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .ult left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨leftGuard, rightGuard, _⟩
          have leftEquality := left.related concreteArgument state leftGuard
          have rightEquality := right.related concreteArgument state rightGuard
          have operationEquality := bitVec_abstract_bool_binop_ult
            (Source.asWord (Source.Expr.eval concreteArgument state sourceLeft))
            (Source.asWord (Source.Expr.eval concreteArgument state sourceRight)) True.intro
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_bool]
          rw [leftEquality, rightEquality]
          exact operationEquality.symm }
  | _, .ule (left := sourceLeft) (right := sourceRight)
      leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .ule left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨leftGuard, rightGuard, _⟩
          have leftEquality := left.related concreteArgument state leftGuard
          have rightEquality := right.related concreteArgument state rightGuard
          have operationEquality := bitVec_abstract_bool_binop_le
            (Source.asWord (Source.Expr.eval concreteArgument state sourceLeft))
            (Source.asWord (Source.Expr.eval concreteArgument state sourceRight)) True.intro
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_bool]
          rw [leftEquality, rightEquality]
          exact operationEquality.symm }
  | _, .eq (left := sourceLeft) (right := sourceRight)
      leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .eq left.target right.target
        guard := fun argument state =>
          left.guard argument state /\ right.guard argument state /\ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨leftGuard, rightGuard, _⟩
          have leftEquality := left.related concreteArgument state leftGuard
          have rightEquality := right.related concreteArgument state rightGuard
          have operationEquality := bitVec_abstract_bool_binop_eq
            (Source.asWord (Source.Expr.eval concreteArgument state sourceLeft))
            (Source.asWord (Source.Expr.eval concreteArgument state sourceRight)) True.intro
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_bool]
          rw [leftEquality, rightEquality]
          exact operationEquality.symm }
  | _, .ubinary (width := width) (operator := operator) leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .ubinary width operator left.target right.target
        guard := fun argument state =>
          left.guard argument state ∧ right.guard argument state ∧
            unsignedBinaryGuard width.bits operator
              (Target.asNat (left.target.eval argument state))
              (Target.asNat (right.target.eval argument state))
        related := by
          intro concreteArgument state
          simpa [Target.asNat, Target.Expr.eval, Source.Expr.eval,
            Source.asWord, Target.Value, Source.Value, typeMap, TypeMap.abstract,
            valid_typ_abs_fn_bitVec] using
            abstract_expr_binop (unsignedBinaryWord_exact width operator)
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .sbinary (width := width) (operator := operator) leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .sbinary width operator left.target right.target
        guard := fun argument state =>
          left.guard argument state ∧ right.guard argument state ∧
            signedBinaryGuard width.bits operator
              (Target.asInt (left.target.eval argument state))
              (Target.asInt (right.target.eval argument state))
        related := by
          intro concreteArgument state
          simpa [Target.asInt, Target.Expr.eval, Source.Expr.eval,
            Source.asSignedWord, Target.Value, Source.Value, typeMap,
            TypeMap.abstract, valid_typ_abs_fn_bitVecSigned] using
            abstract_expr_binop (signedBinaryWord_exact width operator)
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .uunary (width := width) (operator := operator) valueSupported =>
      let value := transform valueSupported
      { target := .uunary width operator value.target
        guard := fun argument state =>
          value.guard argument state ∧
            unsignedUnaryCDefined width.bits operator
              (Target.asNat (value.target.eval argument state)) ∧
            unsignedUnaryAbstractable width.bits operator
              (Target.asNat (value.target.eval argument state))
        related := by
          intro concreteArgument state
          simpa [Target.asNat, Target.Expr.eval, Source.Expr.eval,
            Source.asWord, Target.Value, Source.Value, typeMap, TypeMap.abstract,
            valid_typ_abs_fn_bitVec] using
            abstract_expr_unop (unsignedUnaryWord_exact width operator)
              (value.related concreteArgument state) }
  | _, .sunary (width := width) (operator := operator) valueSupported =>
      let value := transform valueSupported
      { target := .sunary width operator value.target
        guard := fun argument state =>
          value.guard argument state ∧
            signedUnaryCDefined width.bits operator
              (Target.asInt (value.target.eval argument state)) ∧
            signedUnaryAbstractable width.bits operator
              (Target.asInt (value.target.eval argument state))
        related := by
          intro concreteArgument state
          simpa [Target.asInt, Target.Expr.eval, Source.Expr.eval,
            Source.asSignedWord, Target.Value, Source.Value, typeMap,
            TypeMap.abstract, valid_typ_abs_fn_bitVecSigned] using
            abstract_expr_unop (signedUnaryWord_exact width operator)
              (value.related concreteArgument state) }
  | _, .ucmp (width := width) (operator := operator) leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .ucmp width operator left.target right.target
        guard := fun argument state =>
          left.guard argument state ∧ right.guard argument state ∧ True
        related := by
          intro concreteArgument state
          simpa [Target.asNat, Target.Expr.eval, Source.Expr.eval,
            Source.asWord, Target.Value, Source.Value, typeMap, TypeMap.abstract,
            valid_typ_abs_fn_bitVec] using
            abstract_expr_bool_binop (unsignedComparison_exact operator)
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .scmp (width := width) (operator := operator) leftSupported rightSupported =>
      let left := transform leftSupported
      let right := transform rightSupported
      { target := .scmp width operator left.target right.target
        guard := fun argument state =>
          left.guard argument state ∧ right.guard argument state ∧ True
        related := by
          intro concreteArgument state
          simpa [Target.asInt, Target.Expr.eval, Source.Expr.eval,
            Source.asSignedWord, Target.Value, Source.Value, typeMap,
            TypeMap.abstract, valid_typ_abs_fn_bitVecSigned] using
            abstract_expr_bool_binop (signedComparison_exact operator)
              (left.related concreteArgument state)
              (right.related concreteArgument state) }
  | _, .ushiftU (direction := direction) (valueWidth := valueWidth)
      (countWidth := countWidth) valueSupported countSupported =>
      let value := transform valueSupported
      let count := transform countSupported
      { target := .ushiftU direction valueWidth countWidth value.target count.target
        guard := fun argument state =>
          value.guard argument state ∧ count.guard argument state ∧
            unsignedShiftGuard valueWidth.bits direction
              (Target.asNat (value.target.eval argument state))
              (Target.asNat (count.target.eval argument state))
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, countGuard, operationGuard⟩
          have valueEquality := value.related concreteArgument state valueGuard
          have countEquality := count.related concreteArgument state countGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_word]
          rw [valueEquality, countEquality] at operationGuard ⊢
          exact (unsignedShiftWord_exact valueWidth direction _ _ operationGuard).symm }
  | _, .ushiftS (direction := direction) (valueWidth := valueWidth)
      (countWidth := countWidth) (value := sourceValue) (count := sourceCount)
      valueSupported countSupported =>
      let value := transform valueSupported
      let count := transform countSupported
      { target := .ushiftS direction valueWidth countWidth value.target count.target
        guard := fun argument state =>
          value.guard argument state ∧ count.guard argument state ∧
            0 ≤ Target.asInt (count.target.eval argument state) ∧
            unsignedShiftGuard valueWidth.bits direction
              (Target.asNat (value.target.eval argument state))
              (Target.asInt (count.target.eval argument state)).toNat
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, countGuard, countNonnegative, operationGuard⟩
          have valueEquality := value.related concreteArgument state valueGuard
          have countEquality := count.related concreteArgument state countGuard
          rw [countEquality] at countNonnegative
          have countMsb :
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).msb = false :=
            BitVec.msb_eq_false_iff_two_mul_lt.mpr
              (BitVec.toInt_pos_iff.mp countNonnegative)
          have countToNat := BitVec.toNat_toInt_of_msb
            (Source.asSignedWord
              (Source.Expr.eval concreteArgument state sourceCount)) countMsb
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Target.asInt,
            Source.asWord, Source.asSignedWord, TypeMap.abstract_word]
          rw [valueEquality, countEquality] at operationGuard ⊢
          change unsignedShiftGuard valueWidth.bits direction
              (Source.asWord
                (Source.Expr.eval concreteArgument state sourceValue)).toNat
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).toInt.toNat
            at operationGuard
          change unsignedShift direction
              (Source.asWord
                (Source.Expr.eval concreteArgument state sourceValue)).toNat
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).toInt.toNat = _
          rw [countToNat] at operationGuard ⊢
          exact (unsignedShiftWord_exact valueWidth direction _ _ operationGuard).symm }
  | _, .sshiftU (direction := direction)
      (valueWidth := valueWidth) (countWidth := countWidth)
      valueSupported countSupported =>
      let value := transform valueSupported
      let count := transform countSupported
      { target := .sshiftU direction valueWidth countWidth
          value.target count.target
        guard := fun argument state =>
          value.guard argument state ∧ count.guard argument state ∧
            signedShiftGuard valueWidth.bits direction
              (Target.asInt (value.target.eval argument state))
              (Target.asNat (count.target.eval argument state))
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, countGuard, operationGuard⟩
          have valueEquality := value.related concreteArgument state valueGuard
          have countEquality := count.related concreteArgument state countGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Target.asInt,
            Source.asWord, Source.asSignedWord,
            TypeMap.abstract_sword]
          rw [valueEquality, countEquality] at operationGuard ⊢
          exact (signedShiftWord_exact valueWidth direction _ _ operationGuard).symm }
  | _, .sshiftS (direction := direction)
      (valueWidth := valueWidth) (countWidth := countWidth)
      (value := sourceValue) (count := sourceCount)
      valueSupported countSupported =>
      let value := transform valueSupported
      let count := transform countSupported
      { target := .sshiftS direction valueWidth countWidth
          value.target count.target
        guard := fun argument state =>
          value.guard argument state ∧ count.guard argument state ∧
            0 ≤ Target.asInt (count.target.eval argument state) ∧
            signedShiftGuard valueWidth.bits direction
              (Target.asInt (value.target.eval argument state))
              (Target.asInt (count.target.eval argument state)).toNat
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, countGuard, countNonnegative, operationGuard⟩
          have valueEquality := value.related concreteArgument state valueGuard
          have countEquality := count.related concreteArgument state countGuard
          rw [countEquality] at countNonnegative
          have countMsb :
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).msb = false :=
            BitVec.msb_eq_false_iff_two_mul_lt.mpr
              (BitVec.toInt_pos_iff.mp countNonnegative)
          have countToNat := BitVec.toNat_toInt_of_msb
            (Source.asSignedWord
              (Source.Expr.eval concreteArgument state sourceCount)) countMsb
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asInt,
            Source.asSignedWord, TypeMap.abstract_sword]
          rw [valueEquality, countEquality] at operationGuard ⊢
          change signedShiftGuard valueWidth.bits direction
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceValue)).toInt
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).toInt.toNat
            at operationGuard
          change signedShift direction
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceValue)).toInt
              (Source.asSignedWord
                (Source.Expr.eval concreteArgument state sourceCount)).toInt.toNat = _
          rw [countToNat] at operationGuard ⊢
          exact (signedShiftWord_exact valueWidth direction _ _ operationGuard).symm }
  | _, .ucast (sourceWidth := sourceWidth) (targetWidth := targetWidth)
      valueSupported =>
      let value := transform valueSupported
      { target := .ucast sourceWidth targetWidth value.target
        guard := fun argument state => value.guard argument state ∧ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, _⟩
          have valueEquality := value.related concreteArgument state valueGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_word]
          rw [valueEquality]
          exact (unsignedCastWord_exact sourceWidth targetWidth _).symm }
  | _, .scast (sourceWidth := sourceWidth) (targetWidth := targetWidth)
      valueSupported =>
      let value := transform valueSupported
      { target := .scast sourceWidth targetWidth value.target
        guard := fun argument state => value.guard argument state ∧ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, _⟩
          have valueEquality := value.related concreteArgument state valueGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asInt,
            Source.asSignedWord, TypeMap.abstract_sword]
          rw [valueEquality]
          exact (signedCastWord_exact sourceWidth targetWidth _).symm }
  | _, .unsignedToSigned (width := width) valueSupported =>
      let value := transform valueSupported
      { target := .unsignedToSigned width value.target
        guard := fun argument state =>
          value.guard argument state ∧
            signedInRange width.bits
              (Int.ofNat (Target.asNat (value.target.eval argument state)))
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, conversionGuard⟩
          have valueEquality := value.related concreteArgument state valueGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asNat, Source.asWord,
            TypeMap.abstract_sword]
          rw [valueEquality] at conversionGuard ⊢
          exact (unsignedToSignedWord_exact width _ conversionGuard).symm }
  | _, .signedToUnsigned (width := width) valueSupported =>
      let value := transform valueSupported
      { target := .signedToUnsigned width value.target
        guard := fun argument state =>
          value.guard argument state ∧ True
        related := by
          intro concreteArgument state
          unfold abstract_val
          rintro ⟨valueGuard, _⟩
          have valueEquality := value.related concreteArgument state valueGuard
          simp only [Target.Expr.eval, Source.Expr.eval, Target.asInt,
            Source.asSignedWord, TypeMap.abstract_word]
          rw [valueEquality]
          exact bitVec_signedToUnsignedValue _ }
  | _, .pair firstSupported secondSupported =>
      let first := transform firstSupported
      let second := transform secondSupported
      { target := .pair first.target second.target
        guard := fun argument state =>
          first.guard argument state ∧ second.guard argument state
        related := by
          intro concreteArgument state
          exact abstract_val_prod (first.related concreteArgument state)
            (second.related concreteArgument state) }
  | _, .fst (value := sourceValue) valueSupported =>
      let value := transform valueSupported
      { target := .fst value.target
        guard := value.guard
        related := by
          intro concreteArgument state guard
          have equality := value.related concreteArgument state guard
          exact congrArg Prod.fst equality }
  | _, .snd (value := sourceValue) valueSupported =>
      let value := transform valueSupported
      { target := .snd value.target
        guard := value.guard
        related := by
          intro concreteArgument state guard
          have equality := value.related concreteArgument state guard
          exact congrArg Prod.snd equality }

end Expr

/-- Indexed evidence that the entire program is in the certified fragment. -/
inductive Supported {Argument : ValueType} {State : Type u} :
    {exception result : ValueType} ->
      Source.Syntax Argument State exception result -> Type (u + 1) where
  | gets {exception result : ValueType} {value : Source.Expr Argument State result}
      (valueSupported : Expr.Supported value)
      (names : List String) : Supported (.gets value names)
  | guard {exception : ValueType} {test : Source.Expr Argument State .bool}
      (testSupported : Expr.Supported test) :
      Supported (.guard test)
  | exactGuard {exception : ValueType} (test : State -> Prop) :
      Supported (.exactGuard test)
  | modify {exception : ValueType} (update : State -> State) :
      Supported (.modify update)
  /-- Every concrete continuation body is structurally supported. -/
  | seq {exception middle result : ValueType}
      {first : Source.Syntax Argument State exception middle} {next}
      (firstSupported : Supported first)
      (nextSupported : forall value : Source.Value middle, Supported (next value)) :
      Supported (.seq first next)
  | condition {exception result : ValueType} {test : Source.Expr Argument State .bool}
      {thenBranch elseBranch : Source.Syntax Argument State exception result}
      (testSupported : Expr.Supported test) (thenSupported : Supported thenBranch)
      (elseSupported : Supported elseBranch) :
      Supported (.condition test thenBranch elseBranch)
  /-- Every concrete handler body is structurally supported. -/
  | «catch» {exception caught result : ValueType}
      {body : Source.Syntax Argument State caught result} {handler}
      (bodySupported : Supported body)
      (handlerSupported : forall exception : Source.Value caught,
        Supported (handler exception)) : Supported (.catch body handler)
  | «while» (exception result : ExactValueType)
      (test : Source.Value result.type -> State -> Prop)
      (body : Source.Value result.type ->
        L2.Syntax State (Source.Value exception.type) (Source.Value result.type))
      (initial : Source.Value result.type) (names : List String) :
      Supported (.while exception result test body initial names)
  | whileMapped (exception result : ValueType)
      (test : Source.Value result -> State -> Prop)
      {body : Source.Value result ->
        Source.Syntax Argument State exception result}
      (bodySupported : ∀ value, Supported (body value))
      (initial : Source.Value result) (names : List String) (guardTotal : GuardTotal result) :
      Supported (.whileMapped exception result test body initial names guardTotal)
  | whileMappedGuarded (exception result : ValueType)
      (test : Source.Value result -> State -> Prop)
      {body : Source.Value result ->
        Source.Syntax Argument State exception result}
      (bodySupported : ∀ value, Supported (body value))
      (initial : Source.Value result) (names : List String) :
      Supported (.whileMappedGuarded exception result test body initial names)
  | throw {exception result : ValueType} (value : Source.Value exception)
      (names : List String) : Supported (.throw value names)
  | skip {exception : ValueType} : Supported (.skip :
      Source.Syntax Argument State exception .unit)
  | fail {exception result : ValueType} : Supported (.fail :
      Source.Syntax Argument State exception result)

def Supported.seqContinuation
    (evidence : Supported (.seq first next)) :
    ∀ value, Supported (next value) :=
  match evidence with
  | .seq _ continuation => continuation

def Supported.catchContinuation
    (evidence : Supported (.catch body handler)) :
    ∀ exception, Supported (handler exception) :=
  match evidence with
  | .catch _ continuation => continuation

/-- Structural recognition for the source grammar. -/
def supported {Argument : ValueType} {State : Type u} {Exception Result : ValueType} :
    (source : Source.Syntax Argument State Exception Result) -> Supported source
  | .gets value names => .gets (exception := Exception) (Expr.supported value) names
  | .guard test => .guard (exception := Exception) (Expr.supported test)
  | .exactGuard test => .exactGuard (exception := Exception) test
  | .modify update => .modify (exception := Exception) update
  | .seq first next => .seq (exception := Exception) (result := Result)
      (supported first) fun value =>
      supported (next value)
  | .condition test thenBranch elseBranch =>
      .condition (exception := Exception) (Expr.supported test)
        (supported thenBranch) (supported elseBranch)
  | .catch body handler =>
      .catch (exception := Exception) (supported body) fun exception =>
        supported (handler exception)
  | .while exception result test body initial names =>
      .while exception result test body initial names
  | .whileMapped exception result test body initial names guardTotal =>
      .whileMapped exception result test (fun value => supported (body value))
        initial names guardTotal
  | .whileMappedGuarded exception result test body initial names =>
      .whileMappedGuarded exception result test (fun value => supported (body value))
        initial names
  | .throw exception names => .throw (result := Result) exception names
  | .skip => .skip
  | .fail => .fail

/-- Local precursor: its precondition is inserted as a guard by its parent. -/
structure RawCertificate {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType}
    (source : Source.Syntax Argument State Exception Result) where
  target : Target.Syntax Argument State Exception Result
  required : Target.Value Argument -> State -> Prop
  corres : forall concreteArgument,
    corresTA (required ((typeMap Argument).abstract concreteArgument))
      (typeMap Result).abstract (typeMap Exception).abstract
      (target.denote ((typeMap Argument).abstract concreteArgument))
      (source.denote concreteArgument)

def transformRaw {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType} :
    {source : Source.Syntax Argument State Exception Result} ->
      Supported source -> RawCertificate source
  | _, .gets valueSupported names =>
      let value := Expr.transform valueSupported
      { target := .gets value.target names
        required := value.guard
        corres := by
          intro concreteArgument
          exact corresTA_L2_gets (value.related concreteArgument) }
  | _, .guard testSupported =>
      let test := Expr.transform testSupported
      { target := .guard fun argument state =>
          test.target.eval argument state = true /\ test.guard argument state
        required := fun _ _ => True
        corres := by
          intro concreteArgument
          apply corresTA_L2_guard
          exact test.proposition concreteArgument }
  | _, .exactGuard test =>
      { target := .exactGuard test
        required := fun _ _ => True
        corres := by
          intro _
          simpa only [Target.Syntax.denote, Source.Syntax.denote,
            typeMap, TypeMap.abstract, and_true] using
            (corresTA_L2_guard
              (abstractGuard := test) (concreteGuard := test)
              (generated := fun _ => True)
              (exceptionMap := (typeMap Exception).abstract)
              (fun state => abstract_val_const True id (test state))) }
  | _, .modify update =>
      { target := .modify update
        required := fun _ _ => True
        corres := by
          intro _
          apply corresTA_L2_modify
          intro _ _
          rfl }
  | _, .seq firstSupported nextSupported =>
      let first := transformRaw firstSupported
      let nextResult := fun value =>
        transformRaw (nextSupported ((typeMap _).concretize value))
      let nextTarget := fun value =>
        (nextResult value).target
      let nextRequired := fun value =>
        (nextResult value).required
      let nextGenerated := fun value argument state =>
        (typeMap _).certificate.concreteGuard value ∧
          nextRequired value argument state
      { target := .seq first.target fun value =>
          .seq (.guard (nextGenerated value)) fun _ => nextTarget value
        required := first.required
        corres := by
          intro concreteArgument
          apply corresTA_L2_seq (first.corres concreteArgument)
          intro value
          intro state hypothesis
          have valueEquality := TypeMap.sourceRoundTrip value hypothesis.1.1
          simp only [nextGenerated, nextTarget, nextRequired, nextResult] at hypothesis ⊢
          rw [valueEquality] at hypothesis ⊢
          exact (transformRaw (nextSupported value)).corres concreteArgument state
            ⟨hypothesis.1.2, hypothesis.2⟩ }
  | _, .condition testSupported thenSupported elseSupported =>
      let test := Expr.transform testSupported
      let thenResult := transformRaw thenSupported
      let elseResult := transformRaw elseSupported
      { target := .condition test.target
          (.seq (.guard thenResult.required) fun _ => thenResult.target)
          (.seq (.guard elseResult.required) fun _ => elseResult.target)
        required := test.guard
        corres := by
          intro concreteArgument
          apply corresTA_L2_condition
            (thenResult.corres concreteArgument) (elseResult.corres concreteArgument)
          exact test.proposition concreteArgument }
  | _, .catch bodySupported handlerSupported =>
      let body := transformRaw bodySupported
      let handlerResult := fun exception =>
        transformRaw (handlerSupported ((typeMap _).concretize exception))
      let handlerTarget := fun exception =>
        (handlerResult exception).target
      let handlerRequired := fun exception =>
        (handlerResult exception).required
      let handlerGenerated := fun exception argument state =>
        (typeMap _).certificate.concreteGuard exception ∧
          handlerRequired exception argument state
      { target := .catch body.target fun exception =>
          .seq (.guard (handlerGenerated exception)) fun _ => handlerTarget exception
        required := body.required
        corres := by
          intro concreteArgument
          apply corresTA_L2_catch (body.corres concreteArgument)
          intro exception
          intro state hypothesis
          have valueEquality := TypeMap.sourceRoundTrip exception hypothesis.1.1
          simp only [handlerGenerated, handlerTarget, handlerRequired, handlerResult]
            at hypothesis ⊢
          rw [valueEquality] at hypothesis ⊢
          exact (transformRaw (handlerSupported exception)).corres concreteArgument state
            ⟨hypothesis.1.2, hypothesis.2⟩ }
  | _, .while exception result test body initial names =>
      match exception, result with
      | .unit, .unit =>
          { target := .while .unit .unit test body initial names
            required := fun _ _ => True
            corres := fun _ => corresTA_L2_while (fun _ _ => Iff.rfl)
              (fun _ => rfl) rfl }
      | .unit, .bool =>
          { target := .while .unit .bool test body initial names
            required := fun _ _ => True
            corres := fun _ => corresTA_L2_while (fun _ _ => Iff.rfl)
              (fun _ => rfl) rfl }
      | .bool, .unit =>
          { target := .while .bool .unit test body initial names
            required := fun _ _ => True
            corres := fun _ => corresTA_L2_while (fun _ _ => Iff.rfl)
              (fun _ => rfl) rfl }
      | .bool, .bool =>
          { target := .while .bool .bool test body initial names
            required := fun _ _ => True
            corres := fun _ => corresTA_L2_while (fun _ _ => Iff.rfl)
              (fun _ => rfl) rfl }
  | _, .whileMapped exception result test bodySupported initial names guardTotal =>
      let bodyTarget := fun value =>
        let raw := transformRaw (bodySupported ((typeMap result).concretize value))
        Target.Syntax.seq (.guard raw.required) fun _ => raw.target
      { target := .whileMapped exception result
          (fun value state => test ((typeMap result).concretize value) state)
          bodyTarget ((typeMap result).abstract initial) names
        required := fun _ _ => True
        corres := by
          intro concreteArgument
          apply corresTA_L2_while_map
          · intro value state
            rw [TypeMap.sourceRoundTrip value
              (TypeMap.concreteGuard_abstract guardTotal value)]
          · intro value
            simp only [bodyTarget]
            rw [TypeMap.sourceRoundTrip value
              (TypeMap.concreteGuard_abstract guardTotal value)]
            exact corresTA_precond_to_guard
              ((transformRaw (bodySupported value)).corres concreteArgument)
          · rfl }
  | _, .whileMappedGuarded exception result test bodySupported initial names =>
      let bodyResult := fun value =>
        transformRaw (bodySupported ((typeMap result).concretize value))
      let bodyPreTarget := fun value =>
        Target.Syntax.seq (.guard (bodyResult value).required) fun _ =>
          (bodyResult value).target
      let resultGuard := fun value (_ : Target.Value Argument) (_ : State) =>
        (typeMap result).certificate.concreteGuard value
      let bodyTarget := fun value =>
        Target.Syntax.seq (bodyPreTarget value) fun next =>
          .seq (.guard (resultGuard next)) fun _ =>
            .gets (.state result fun _ => next) []
      { target := .whileMappedGuarded exception result
          (fun value state => test ((typeMap result).concretize value) state)
          bodyTarget ((typeMap result).abstract initial) names
        required := fun _ _ => (typeMap result).certificate.concreteGuard
          ((typeMap result).abstract initial)
        corres := by
          intro concreteArgument state hypothesis
          refine (corresTA_L2_while_map_guarded
            (valid := fun value => (typeMap result).certificate.concreteGuard
              ((typeMap result).abstract value))
            (abstractInitial := (typeMap result).abstract initial)
            (concreteInitial := initial) ?_ ?_ ?_ hypothesis.1 rfl) state ?_
          · intro value current valid
            rw [TypeMap.sourceRoundTrip value valid]
          · intro value valid
            simp only [bodyTarget, bodyPreTarget, bodyResult, resultGuard,
              Target.Syntax.denote]
            rw [TypeMap.sourceRoundTrip value valid]
            exact corresTA_guardResults (corresTA_precond_to_guard
              ((transformRaw (bodySupported value)).corres concreteArgument))
          · intro value current valid noFail next post member
            simp only [bodyTarget, bodyPreTarget, bodyResult, resultGuard,
              Target.Syntax.denote] at noFail
            rw [TypeMap.sourceRoundTrip value valid] at noFail
            exact guardResults_source_valid
              (corresTA_precond_to_guard
                ((transformRaw (bodySupported value)).corres concreteArgument))
              noFail member
          · exact ⟨True.intro, hypothesis.2⟩ }
  | _, .throw value names =>
      { target := .throw ((typeMap _).abstract value) names
        required := fun _ _ => True
        corres := by
          intro concreteArgument
          exact corresTA_L2_throw (abstract_val_trivial _ value) }
  | _, .skip =>
      { target := .skip
        required := fun _ _ => True
        corres := fun _ => corresTA_L2_skip }
  | _, .fail =>
      { target := .fail
        required := fun _ _ => True
        corres := fun _ => corresTA_L2_fail }

/-- Pure transformation that recursively consumes all structural evidence. -/
def transform {Argument : ValueType} {State : Type u} {Exception Result : ValueType}
    {source : Source.Syntax Argument State Exception Result}
    (evidence : Supported source) : Certificate source :=
  let raw := transformRaw evidence
  { target := .seq (.guard raw.required) fun _ => raw.target
    corres := fun concreteArgument =>
      corresTA_precond_to_guard (raw.corres concreteArgument) }

/-- Source-total pass interface for the typed grammar. -/
def transformSource {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType}
    (source : Source.Syntax Argument State Exception Result) : Certificate source :=
  transform (supported source)

/--
A certified HOAS function boundary over an abstract argument. Continuation
support is consumed recursively and related by the sequence and catch rules.
-/
structure FunctionCertificate {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType}
    (source : Source.Syntax Argument State Exception Result) where
  target : Target.Syntax Argument State Exception Result
  corres : forall concreteArgument,
    corresTA (fun _ => True) (typeMap Result).abstract (typeMap Exception).abstract
      (target.denote ((typeMap Argument).abstract concreteArgument))
      (source.denote concreteArgument)

def transformFunction {Argument : ValueType} {State : Type u}
    {Exception Result : ValueType}
    {source : Source.Syntax Argument State Exception Result}
    (evidence : Supported source) : FunctionCertificate source :=
  let certificate := transform evidence
  { target := certificate.target
    corres := certificate.corres }

/-- Integration work not represented by this typed local syntax. -/
inductive LocalGap where
  | callTranslation
  | automaticHeapGetter
  | specificationTranslation
  | recursionGroup
  | customRuleRegistry
  | functionOptionDispatch
  deriving DecidableEq, Repr

/-- These are repository-local gaps, not limitations of upstream semantics. -/
def LocalGap.reason : LocalGap -> String
  | .callTranslation => "this local kernel has no typed call node or callee scheduler"
  | .automaticHeapGetter => "automatic HeapLift getter recognition is not connected here"
  | .specificationTranslation => "the local typed syntax has no specification relation node"
  | .recursionGroup => "recursive function-group generation is outside this local kernel"
  | .customRuleRegistry => "mutable user-installed WordAbstract rules are not implemented locally"
  | .functionOptionDispatch => "parser-driven per-function abstraction options are not connected"

/-- A source term dependently packaged with its structurally generated evidence. -/
structure PackagedInput (Argument : ValueType) (State : Type u)
    (Exception Result : ValueType) where
  source : Source.Syntax Argument State Exception Result
  evidence : Supported source

/-- Feed recognized evidence to the existing pure certified transformation. -/
def PackagedInput.certificate
    {Argument : ValueType} {State : Type u} {Exception Result : ValueType}
    (input : PackagedInput Argument State Exception Result) :
    Certificate input.source :=
  transform input.evidence

/-- Package already-reified typed syntax; this is not a recognizer for arbitrary L2 terms. -/
def package {Argument : ValueType} {State : Type u} {Exception Result : ValueType}
    (source : Source.Syntax Argument State Exception Result) :
    PackagedInput Argument State Exception Result :=
  { source, evidence := supported source }

/-! ## Reduction and semantic pins -/

theorem exactBoolLoopTarget
    (Argument : ValueType)
    (test : Bool -> State -> Prop)
    (body : Bool -> L2.Syntax State Bool Bool)
    (initial : Bool) (names : List String) :
    (transformRaw (Argument := Argument)
      (Supported.while .bool .bool test body initial names)).target =
      Target.Syntax.while (Argument := Argument) .bool .bool
        test body initial names := by
  simp [transformRaw]

private abbrev PinArgument := ValueType.unit
private abbrev PinState := Unit
private abbrev PinException := ValueType.unit

private def word8 (value : Nat) : Source.Expr PinArgument PinState (.word 8) :=
  .word 8 (BitVec.ofNat 8 value)

private def addProgram (left right : Nat) :
    Source.Syntax PinArgument PinState PinException (.word 8) :=
  .gets (.add (word8 left) (word8 right)) []

private def subExpr : Source.Expr PinArgument PinState (.word 8) :=
  .sub (word8 19) (word8 7)

private def comparisonExpr : Source.Expr PinArgument PinState .bool :=
  .ult (word8 7) (word8 19)

private def intRemainderExpr : Source.Expr PinArgument PinState (.uwordInt 32) :=
  .umod (.uint 32 19) (.uint 32 7)

private def nestedProgram :
    Source.Syntax PinArgument PinState PinException .unit :=
  .seq .skip fun _ =>
    .condition (.ult (word8 7) (word8 20)) .skip .fail

/-- A packaged in-range addition flows through the existing transformation. -/
theorem inRangeAddGuardPin :
    let packaged := package (addProgram 7 9)
    match packaged.certificate.target with
    | .seq (.guard guard) _ => guard () () <-> 7 + 9 <= UWORD_MAX 8
    | _ => False := by
  change (True ∧ True ∧ 7 + 9 ≤ UWORD_MAX 8) ↔ 7 + 9 ≤ UWORD_MAX 8
  simp

/-- Subtraction reduces to unbounded Nat subtraction under its generated guard. -/
theorem subtractionReductionPin :
    let evidence := Expr.transform (Expr.supported subExpr)
    evidence.target.eval () () = 19 - 7 /\ evidence.guard () () := by
  change 19 - 7 = 19 - 7 ∧ (True ∧ True ∧ 7 ≤ 19)
  decide

/-- Unsigned comparison reduces to the corresponding Nat comparison. -/
theorem comparisonReductionPin :
    let evidence := Expr.transform (Expr.supported comparisonExpr)
    evidence.target.eval () () = true /\ evidence.guard () () := by
  change decide (7 < 19) = true ∧ (True ∧ True ∧ True)
  decide

/-- Canonical Int-backed u32 remainder reduces to Nat remainder with all guards discharged. -/
theorem intRemainderReductionPin :
    let evidence := Expr.transform (Expr.supported intRemainderExpr)
    evidence.target.eval () () = 19 % 7 /\ evidence.guard () () := by
  change 19 % 7 = 19 % 7 /\
    (True /\ True /\ abstractUnsignedInt 32 19 < 2 ^ 32 /\
      abstractUnsignedInt 32 7 < 2 ^ 32 /\ abstractUnsignedInt 32 7 ≠ 0)
  native_decide

/-- A negative Int is outside the concrete round-trip guard for an unsigned word. -/
theorem negativeIntRejectedPin :
    ¬(typeMap (.uwordInt 32)).certificate.concreteGuard
      ((typeMap (.uwordInt 32)).abstract (-1)) := by
  change ¬abstractUnsignedInt 32 (-1) < 2 ^ 32
  native_decide

/-- Sequence and condition conversion retain guards before both continuations. -/
theorem nestedSequenceConditionPin :
    let certificate := transform (supported nestedProgram)
    match certificate.target with
    | .seq (.guard _) outerNext =>
        match outerNext () with
        | .seq .skip continuation =>
            match continuation () with
            | .seq (.guard _) afterGuard =>
                match afterGuard () with
                | .condition _ (.seq (.guard _) _) (.seq (.guard _) _) => True
                | _ => False
            | _ => False
        | _ => False
    | _ => False := by
  change True
  trivial

/-- Overflow is an executable target failure, not a correspondence assumption. -/
theorem overflowTargetFailurePin :
    ((transform (supported (addProgram 250 10))).target.denote () ()).failed := by
  simp only [transform, Target.Syntax.denote, L2.seq, bindE, L2.guard]
  left
  rw [L2.failed_liftE]
  change ¬(transformRaw (supported (addProgram 250 10))).required () ()
  change ¬(True ∧ True ∧ 250 + 10 ≤ UWORD_MAX 8)
  decide

end Zag.Lang.AutoCorres.ML.WordAbstract
