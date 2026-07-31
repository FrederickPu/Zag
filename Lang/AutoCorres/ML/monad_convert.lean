import Lang.AutoCorres.TypeStrengthen
import Lang.AutoCorres.ML.monad_types
import Lang.AutoCorres.ML.type_strengthen

/-!
# Certified monad conversion

Corresponds only to [`tools/autocorres/monad_convert.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/monad_convert.ML).

The upstream unlift/relift proof search is represented by carrier-indexed
values and exact conversion certificates. The computable recognizer only
constructs the standard weakening conversions; it does not inspect syntax or
use a lifting head as evidence. Other conversions remain available when a
caller supplies their exact `TypeStrengthen.embed` equality.
-/

namespace Zag.Lang.AutoCorres.ML.MonadConvert

open Zag.Lang.AutoCorres
open MonadTypes

universe u

/-- A source program paired with its known carrier, rather than inferred from syntax. -/
structure Source (carrier : Carrier) (State Result : Type u) where
  program : Repr carrier State Result

/--
The target program and an exact equality between the source and target L2
embeddings. The equality is uniform in the exception type.
-/
structure Conversion {sourceCarrier : Carrier} {State Result : Type u}
    (source : Source sourceCarrier State Result) (targetCarrier : Carrier) where
  target : Source targetCarrier State Result
  exact : ∀ (Exception : Type u),
    TypeStrengthen.embed (Exception := Exception) sourceCarrier source.program =
      TypeStrengthen.embed (Exception := Exception) targetCarrier target.program

/--
Indexed evidence for sound carrier conversion. `certified` is the only way to
add a conversion outside the built-in weakening ladder.
-/
inductive Convertible {State Result : Type u} :
    {sourceCarrier : Carrier} ->
      (source : Source sourceCarrier State Result) -> Carrier -> Type (u + 1) where
  | same (source : Source carrier State Result) : Convertible source carrier
  | pureGets (source : Source .pure State Result) : Convertible source .gets
  | pureOption (source : Source .pure State Result) : Convertible source .option
  | pureNondet (source : Source .pure State Result) : Convertible source .nondet
  | getsOption (source : Source .gets State Result) : Convertible source .option
  | getsNondet (source : Source .gets State Result) : Convertible source .nondet
  | optionNondet (source : Source .option State Result) : Convertible source .nondet
  | certified (certificate : Conversion source targetCarrier) :
      Convertible source targetCarrier

/-- Total pure conversion over indexed evidence. -/
def convert {sourceCarrier targetCarrier : Carrier} {State Result : Type u}
    {source : Source sourceCarrier State Result} :
    Convertible source targetCarrier -> Conversion source targetCarrier
  | .same source =>
      { target := source
        exact := fun _ => rfl }
  | .pureGets source =>
      { target := ⟨fun _ => source.program⟩
        exact := fun _ => rfl }
  | .pureOption source =>
      { target := ⟨fun _ => some source.program⟩
        exact := fun _ => rfl }
  | .pureNondet source =>
      { target := ⟨AutoCorres.pure source.program⟩
        exact := fun _ => rfl }
  | .getsOption source =>
      { target := ⟨fun state => some (source.program state)⟩
        exact := fun _ => rfl }
  | .getsNondet source =>
      { target := ⟨AutoCorres.gets source.program⟩
        exact := fun _ => rfl }
  | .optionNondet source =>
      { target := ⟨TypeStrengthen.optionNondet source.program⟩
        exact := fun _ => rfl }
  | .certified certificate => certificate

/-- A failed built-in recognition says only that no certificate was constructed. -/
structure Diagnostic where
  source : Carrier
  target : Carrier
  reason : String
  deriving DecidableEq

private def unsupported (source target : Carrier) : Diagnostic :=
  { source
    target
    reason := s!"no built-in {source.name} to {target.name} certificate; supply an exact TypeStrengthen embedding certificate" }

/--
Computably recognize the built-in carrier conversions. Every success contains
the exact conversion certificate produced from typed evidence.
-/
def recognize {sourceCarrier : Carrier} {State Result : Type u}
    (source : Source sourceCarrier State Result) (targetCarrier : Carrier) :
    Except Diagnostic (Conversion source targetCarrier) :=
  match sourceCarrier, targetCarrier with
  | .pure, .pure => .ok (convert (.same source))
  | .pure, .gets => .ok (convert (.pureGets source))
  | .pure, .option => .ok (convert (.pureOption source))
  | .pure, .nondet => .ok (convert (.pureNondet source))
  | .gets, .gets => .ok (convert (.same source))
  | .gets, .option => .ok (convert (.getsOption source))
  | .gets, .nondet => .ok (convert (.getsNondet source))
  | .option, .option => .ok (convert (.same source))
  | .option, .nondet => .ok (convert (.optionNondet source))
  | .nondet, .nondet => .ok (convert (.same source))
  | sourceCarrier, targetCarrier => .error (unsupported sourceCarrier targetCarrier)

/-! ## Exactness and reduction pins -/

private def purePin : Source .pure Nat Nat := ⟨7⟩

private def getsPin : Source .gets Nat Nat := ⟨fun state => state + 1⟩

private def optionPin : Source .option Nat Nat :=
  ⟨fun state => if state = 0 then none else some (state + 1)⟩

theorem pure_gets_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .pure purePin.program =
      TypeStrengthen.embed (Exception := Exception) .gets
        (convert (.pureGets purePin)).target.program :=
  (convert (.pureGets purePin)).exact Exception

theorem pure_option_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .pure purePin.program =
      TypeStrengthen.embed (Exception := Exception) .option
        (convert (.pureOption purePin)).target.program :=
  (convert (.pureOption purePin)).exact Exception

theorem pure_nondet_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .pure purePin.program =
      TypeStrengthen.embed (Exception := Exception) .nondet
        (convert (.pureNondet purePin)).target.program :=
  (convert (.pureNondet purePin)).exact Exception

theorem gets_option_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .gets getsPin.program =
      TypeStrengthen.embed (Exception := Exception) .option
        (convert (.getsOption getsPin)).target.program :=
  (convert (.getsOption getsPin)).exact Exception

theorem gets_nondet_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .gets getsPin.program =
      TypeStrengthen.embed (Exception := Exception) .nondet
        (convert (.getsNondet getsPin)).target.program :=
  (convert (.getsNondet getsPin)).exact Exception

theorem option_nondet_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .option optionPin.program =
      TypeStrengthen.embed (Exception := Exception) .nondet
        (convert (.optionNondet optionPin)).target.program :=
  (convert (.optionNondet optionPin)).exact Exception

theorem pure_gets_reduction_pin :
    (convert (.pureGets purePin)).target.program 11 = 7 := by
  rfl

theorem pure_option_reduction_pin :
    (convert (.pureOption purePin)).target.program 11 = some 7 := by
  rfl

theorem pure_nondet_reduction_pin :
    (7, 11) ∈ ((convert (.pureNondet purePin)).target.program 11).results ∧
      ¬ ((convert (.pureNondet purePin)).target.program 11).failed := by
  exact ⟨rfl, id⟩

theorem gets_option_reduction_pin :
    (convert (.getsOption getsPin)).target.program 11 = some 12 := by
  rfl

theorem gets_nondet_reduction_pin :
    (12, 11) ∈ ((convert (.getsNondet getsPin)).target.program 11).results ∧
      ¬ ((convert (.getsNondet getsPin)).target.program 11).failed := by
  exact ⟨rfl, id⟩

theorem option_nondet_reduction_pin :
    (12, 11) ∈ ((convert (.optionNondet optionPin)).target.program 11).results ∧
      ¬ ((convert (.optionNondet optionPin)).target.program 11).failed := by
  exact ⟨rfl, id⟩

private def nondetPin : Source .nondet Nat Nat :=
  ⟨AutoCorres.gets fun state => state + 1⟩

private def recognitionFailed {sourceCarrier : Carrier}
    (source : Source sourceCarrier Nat Nat) (targetCarrier : Carrier) : Bool :=
  match recognize source targetCarrier with
  | .error _ => true
  | .ok _ => false

theorem reverse_strengthening_rejected_pin :
    [ recognitionFailed getsPin .pure
    , recognitionFailed optionPin .pure
    , recognitionFailed optionPin .gets
    , recognitionFailed nondetPin .pure
    , recognitionFailed nondetPin .gets
    , recognitionFailed nondetPin .option ] =
      [true, true, true, true, true, true] := by
  rfl

private def constantGetsPin : Source .gets Nat Nat := ⟨fun _ => 7⟩

private def exactGetsPure : Conversion constantGetsPin .pure :=
  { target := purePin
    exact := fun _ => rfl }

theorem supplied_reverse_exact_pin (Exception : Type) :
    TypeStrengthen.embed (Exception := Exception) .gets constantGetsPin.program =
      TypeStrengthen.embed (Exception := Exception) .pure
        (convert (.certified exactGetsPure)).target.program :=
  (convert (.certified exactGetsPure)).exact Exception

theorem supplied_reverse_reduction_pin :
    (convert (.certified exactGetsPure)).target.program = 7 := by
  rfl

end Zag.Lang.AutoCorres.ML.MonadConvert
