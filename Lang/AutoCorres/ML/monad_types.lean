import Lang.AutoCorres.TypeStrengthen

/-!
# Monad carrier types

Corresponds only to [`tools/autocorres/monad_types.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/monad_types.ML).

The upstream mutable registry and head-symbol test are represented here by
closed, typed data. Conversion rules and the embeddings and equalities from
`TypeStrengthen.thy` are deliberately outside this module. A candidate is
eligible for ordering only when its caller supplies a certificate.
-/

namespace Zag.Lang.AutoCorres.ML.MonadTypes

universe u w

/-- Static replacement for the descriptive and precedence registry fields. -/
structure Metadata where
  name : String
  description : String
  precedence : Int
  deriving DecidableEq

/-- The exact metadata of each upstream registration. -/
def metadata : Carrier -> Metadata
  | .pure =>
      { name := "pure"
        description := "Pure function"
        precedence := 100 }
  | .gets =>
      { name := "gets"
        description := "Read-only function"
        precedence := 80 }
  | .option =>
      { name := "option"
        description := "Option monad"
        precedence := 60 }
  | .nondet =>
      { name := "nondet"
        description := "Nondeterministic state monad (default)"
        precedence := 0 }

end Zag.Lang.AutoCorres.ML.MonadTypes

namespace Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Carrier

def name (carrier : Carrier) : String := (ML.MonadTypes.metadata carrier).name

def description (carrier : Carrier) : String := (ML.MonadTypes.metadata carrier).description

def precedence (carrier : Carrier) : Int := (ML.MonadTypes.metadata carrier).precedence

end Zag.Lang.AutoCorres.TypeStrengthen.Kernel.Carrier

namespace Zag.Lang.AutoCorres.ML.MonadTypes

/-- Capabilities whose availability differs between the registered carriers. -/
inductive Capability where
  | monotonicityTransfer
  deriving DecidableEq

/-- Typed evidence that a carrier provides a capability; no term syntax is inspected. -/
inductive Supports : Carrier -> Capability -> Type where
  | optionMonotonicity : Supports .option .monotonicityTransfer
  | nondetMonotonicity : Supports .nondet .monotonicityTransfer

/-- A successful carrier-specific conversion certificate supplied by a caller. -/
structure Candidate (Certificate : Carrier -> Type w) where
  carrier : Carrier
  certificate : Certificate carrier

/-- Existential result of selecting one already-certified candidate. -/
structure Selected (Certificate : Carrier -> Type w) where
  carrier : Carrier
  certificate : Certificate carrier

/-- Insert a certified candidate into descending precedence order. -/
def insertCandidate (candidate : Candidate Certificate) :
    List (Candidate Certificate) -> List (Candidate Certificate)
  | [] => [candidate]
  | current :: rest =>
      if candidate.carrier.precedence >= current.carrier.precedence then
        candidate :: current :: rest
      else
        current :: insertCandidate candidate rest

/-- Order successful conversion candidates by highest precedence first. -/
def orderCandidates : List (Candidate Certificate) -> List (Candidate Certificate)
  | [] => []
  | candidate :: rest => insertCandidate candidate (orderCandidates rest)

/-- Select the highest-precedence successful conversion without manufacturing evidence. -/
def select (candidates : List (Candidate Certificate)) : Option (Selected Certificate) :=
  match orderCandidates candidates with
  | [] => none
  | candidate :: _ => some
      { carrier := candidate.carrier
        certificate := candidate.certificate }

/-! ## Reduction pins -/

theorem precedence_reduction_pin :
    ([.pure, .gets, .option, .nondet] : List Carrier).map (fun carrier => carrier.precedence) =
      [100, 80, 60, 0] := by
  rfl

private abbrev PinCertificate (_ : Carrier) : Type := Unit

private def unorderedPins : List (Candidate PinCertificate) :=
  [ { carrier := .nondet, certificate := () }
  , { carrier := .gets, certificate := () }
  , { carrier := .option, certificate := () }
  , { carrier := .pure, certificate := () } ]

theorem order_reduction_pin :
    (orderCandidates unorderedPins).map (fun candidate => candidate.carrier) =
      [.pure, .gets, .option, .nondet] := by
  rfl

theorem selection_reduction_pin :
    (select unorderedPins).map (fun selected => selected.carrier) = some .pure := by
  rfl

end Zag.Lang.AutoCorres.ML.MonadTypes
