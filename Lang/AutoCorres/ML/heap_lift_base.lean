import Lang.AutoCorres.HeapLift
import Lang.AutoCorres.TypHeapSimple

/-!
# Heap-lift base generation

Corresponds only to [`tools/autocorres/heap_lift_base.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/heap_lift_base.ML).

This module is the pure-data counterpart of the upstream ML record generator.
The local model cannot inspect Isabelle terms, C parser environments, UMM type
descriptors, or generated record layouts. Consequently, term signatures,
copied globals, heap codecs, structure fields, and their layout-obligation
descriptions are explicit typed inputs.
`getProgStructInfo` indexes caller-supplied structure descriptions; it does not
discover C structures or assert that their field getters match a C layout.
Every field selects either the current or legacy `ValidStructField` obligation,
whose proof belongs in the later setup certificate.

The pure `setup` function only packages generated data and functions. Logical
facts that a codec and concrete globals operations cannot establish are fields
of `CertificateObligations` and are assembled separately by
`assembleCertificate`. No parser theorem goal is silently omitted.
-/

namespace Zag.Lang.AutoCorres.ML.HeapLiftBase

open Zag.Lang.AutoCorres
open TypHeapSimple

universe u v w

/-! ## Computable input type descriptions -/

/--
A computable view of the type constructors inspected by upstream ML. Named
types cover parser-defined structures, whose definitions are intentionally not
reconstructed here.
-/
inductive TypeDescriptor where
  | unit
  | word (width : Nat)
  | signedWord (width : Nat)
  | pointer (pointee : TypeDescriptor)
  | array (element : TypeDescriptor) (length : Nat)
  | named (name : String)
  deriving DecidableEq, Repr

/-! ## Typed generated descriptions -/

/-- A copied field retains its Lean value type and concrete globals operations. -/
structure FieldInfo (Globals : Type u) where
  Value : Type u
  oldName : String
  newName : String
  typeDescriptor : TypeDescriptor
  getter : Globals -> Value
  setter : (Value -> Value) -> Globals -> Globals

/--
One selected heap kind. The default is operational data: it is returned at an
invalid pointer when the partial `simpleLift` is made into a total typed heap.
-/
structure HeapKind (Tag : Type u) where
  Value : Type u
  descriptor : TypeDescriptor
  spec : TypeSpec Tag Value
  defaultValue : Value

/-- Finite, dependently typed descriptions of copied globals and selected heaps. -/
structure Schema (Globals : Type u) (Tag : Type u)
    (globalCount heapCount : Nat) where
  globals : Fin globalCount -> FieldInfo Globals
  heaps : Fin heapCount -> HeapKind Tag

/--
The record generated upstream: copied values, one total typed heap per selected
kind, and one validity predicate per selected kind.
-/
structure LiftedGlobals {Globals : Type u} {Tag : Type u}
    {globalCount heapCount : Nat} (schema : Schema Globals Tag globalCount heapCount) where
  copied : (field : Fin globalCount) -> (schema.globals field).Value
  heap : (kind : Fin heapCount) ->
    Ptr (schema.heaps kind).Value -> (schema.heaps kind).Value
  valid : (kind : Fin heapCount) -> Ptr (schema.heaps kind).Value -> Prop

/-! ## Explicit structure-field obligation descriptions -/

/--
Computable parameters for one of the two structure-field certificates. The
concrete raw heap and generated state map are supplied later by `HeapInfo`, so
the description cannot detach its proof from the setup being certified.
-/
inductive StructFieldObligation {Globals Tag : Type u}
    {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount)
    (Parent Field : Type u) where
  | valid
      (parserLayout : TypeSpec Tag Parent -> List String -> TypeSpec Tag Field ->
        (Parent -> Field) -> ((Field -> Field) -> Parent -> Parent) ->
        (Ptr Parent -> Ptr Field) -> Prop)
      (parentSpec : TypeSpec Tag Parent) (fieldName : List String)
      (fieldSpec : TypeSpec Tag Field) (fieldAddress : Ptr Parent -> Ptr Field)
  | legacy
      (fieldName : List String)
      (fieldAddress : List String -> Ptr Parent -> Ptr Field)
      (read : LiftedGlobals schema -> Ptr Parent -> Parent)
      (write : ((Ptr Parent -> Parent) -> Ptr Parent -> Parent) ->
        LiftedGlobals schema -> LiftedGlobals schema)
      (validRead : LiftedGlobals schema -> Ptr Parent -> Prop)
      (validWrite : ((Ptr Parent -> Prop) -> Ptr Parent -> Prop) ->
        LiftedGlobals schema -> LiftedGlobals schema)
      (parentSpec : TypeSpec Tag Parent) (fieldSpec : TypeSpec Tag Field)

/-- Explicit information and certificate parameters for one structure field. -/
structure StructFieldInfo {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount) (Parent : Type u) where
  Value : Type u
  name : String
  typeDescriptor : TypeDescriptor
  getter : Parent -> Value
  setter : (Value -> Value) -> Parent -> Parent
  obligation : StructFieldObligation schema Parent Value

/-- A typed structure description with one explicit obligation per field. -/
structure StructInfo {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount) where
  Value : Type u
  name : String
  typeDescriptor : TypeDescriptor
  fields : List (StructFieldInfo schema Value)

/-- A generated getter and modifying setter. -/
structure FieldLens (State : Type u) (View : Type v) where
  get : State -> View
  modify : (View -> View) -> State -> State

/-! ## Computable type selection and canonicalization -/

/-- Produce the pleasant field-name fragment used for a selected descriptor. -/
def nameFromType : TypeDescriptor -> String
  | .unit => "unit"
  | .word width => "w" ++ toString width
  | .signedWord width => "signed_w" ++ toString width
  | .pointer pointee => nameFromType pointee ++ "'ptr"
  | .array element length => nameFromType element ++ "'array_" ++ toString length
  | .named name => name

def heapNameFromType (descriptor : TypeDescriptor) : String :=
  "heap_" ++ nameFromType descriptor

def heapValidNameFromType (descriptor : TypeDescriptor) : String :=
  "is_valid_" ++ nameFromType descriptor

/-- A reified term carrying only the type views available to upstream traversal. -/
inductive TypedTerm where
  | atom (result : TypeDescriptor) (binders : List TypeDescriptor)
  | abs (body : TypedTerm)
  | app (function argument : TypedTerm)
  deriving DecidableEq, Repr

private def pointee? : TypeDescriptor -> Option TypeDescriptor
  | .pointer pointee => some pointee
  | _ => none

/-- Determine pointed-to heap types mentioned by one explicit term type view. -/
def getTermHeapTypes : TypedTerm -> List TypeDescriptor
  | .abs body => getTermHeapTypes body
  | .app function argument => getTermHeapTypes function ++ getTermHeapTypes argument
  | .atom result binders => (result :: binders).filterMap pointee?

/-- Signed words use the corresponding unsigned word heap. -/
def signedToUnsigned : TypeDescriptor -> TypeDescriptor
  | .unit => .unit
  | .word width => .word width
  | .signedWord width => .word width
  | .pointer pointee => .pointer (signedToUnsigned pointee)
  | .array element length => .array (signedToUnsigned element) length
  | .named name => .named name

/-- Arrays select their element heap; this policy also applies below pointers. -/
def arraysToElements : TypeDescriptor -> TypeDescriptor
  | .unit => .unit
  | .word width => .word width
  | .signedWord width => .signedWord width
  | .pointer pointee => .pointer (arraysToElements pointee)
  | .array element _ => arraysToElements element
  | .named name => .named name

/-- Apply the two upstream heap canonicalization policies in explicit order. -/
def canonicalHeapType (descriptor : TypeDescriptor) : TypeDescriptor :=
  arraysToElements (signedToUnsigned descriptor)

private def insertDescriptor (descriptor : TypeDescriptor) :
    List TypeDescriptor -> List TypeDescriptor
  | [] => [descriptor]
  | head :: tail =>
      if descriptor = head then head :: tail
      else head :: insertDescriptor descriptor tail

private def canonicalizeDescriptors (descriptors : List TypeDescriptor) :
    List TypeDescriptor :=
  descriptors.foldl (fun selected descriptor =>
    let canonical := canonicalHeapType descriptor
    if canonical = .unit then selected else insertDescriptor canonical selected) []

/--
Select all canonical heap types used by explicit function bodies, optionally
including the four standard word heaps generated upstream.
-/
def getProgramHeapTypes (functionBodies : List TypedTerm)
    (generateWordHeaps : Bool) : List TypeDescriptor :=
  let discovered := functionBodies.flatMap getTermHeapTypes
  let words := if generateWordHeaps then
      [.word 8, .word 16, .word 32, .word 64]
    else []
  canonicalizeDescriptors (words ++ discovered)

/-- The parser-level role needed to identify the distinguished raw heap field. -/
inductive GlobalFieldRole where
  | copied
  | rawHeap
  deriving DecidableEq, Repr

/-- Computable metadata used before callers construct typed `FieldInfo` values. -/
structure GlobalFieldDescriptor where
  name : String
  typeDescriptor : TypeDescriptor
  role : GlobalFieldRole
  deriving DecidableEq, Repr

/-- Select fields copied to the generated globals, excluding the raw heap field. -/
def getRealGlobalVars (fields : List GlobalFieldDescriptor) :
    List GlobalFieldDescriptor :=
  fields.filter fun field => field.role == .copied

/-- Select the explicitly marked analogue of upstream's `t_hrs_'` field. -/
def getGlobalsRawHeap? (fields : List GlobalFieldDescriptor) :
    Option GlobalFieldDescriptor :=
  fields.find? fun field => field.role == .rawHeap

/-! ## Pure generated record and state abstraction -/

/-- Construct the dependent replacement for upstream record generation. -/
def genNewHeap {Globals Tag : Type u} {globalCount heapCount : Nat}
    (globals : Fin globalCount -> FieldInfo Globals)
    (heaps : Fin heapCount -> HeapKind Tag) :
    Schema Globals Tag globalCount heapCount :=
  { globals, heaps }

/--
Generate the state abstraction from concrete globals and an already-projected
raw heap. `Option.getD` uses the selected kind's explicit `defaultValue`; the
definition inspects no proof fields from `TypeSpec`.
-/
def liftGlobalHeap {Globals Tag : Type u} {globalCount heapCount : Nat}
    [DecidableEq Tag]
    (schema : Schema Globals Tag globalCount heapCount)
    (globals : Globals) (raw : HeapRawState Tag) : LiftedGlobals schema where
  copied field := (schema.globals field).getter globals
  heap kind pointer :=
    (simpleLift raw (schema.heaps kind).spec pointer).getD
      (schema.heaps kind).defaultValue
  valid kind pointer :=
    (simpleLift raw (schema.heaps kind).spec pointer).isSome = true

private def updateDependent {Index : Type u} [DecidableEq Index]
    {Family : Index -> Type v} (values : (index : Index) -> Family index)
    (selected : Index) (value : Family selected) :
    (index : Index) -> Family index := fun index =>
  if equal : index = selected then equal.symm ▸ value else values index

/-- Generated copied-global field lens. -/
def copiedGlobalLens {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount)
    (field : Fin globalCount) :
    FieldLens (LiftedGlobals schema) (schema.globals field).Value where
  get state := state.copied field
  modify transform state :=
    { state with copied :=
        updateDependent state.copied field (transform (state.copied field)) }

/-- Generated total typed-heap field lens. -/
def typedHeapLens {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount)
    (kind : Fin heapCount) :
    FieldLens (LiftedGlobals schema)
      (Ptr (schema.heaps kind).Value -> (schema.heaps kind).Value) where
  get state := state.heap kind
  modify transform state :=
    { state with heap :=
        updateDependent state.heap kind (transform (state.heap kind)) }

/-- Generated validity-map field lens. -/
def validityLens {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount)
    (kind : Fin heapCount) :
    FieldLens (LiftedGlobals schema) (Ptr (schema.heaps kind).Value -> Prop) where
  get state := state.valid kind
  modify transform state :=
    { state with valid :=
        updateDependent state.valid kind (transform (state.valid kind)) }

/-- Explicit typed structure tables; no C parser discovery occurs. -/
structure StructTables {Globals Tag : Type u} {globalCount heapCount : Nat}
    (schema : Schema Globals Tag globalCount heapCount) where
  entries : List (StructInfo schema)

def StructTables.findByName (tables : StructTables schema) (name : String) :
    Option (StructInfo schema) :=
  tables.entries.find? fun info => info.name == name

def StructTables.findByType (tables : StructTables schema)
    (descriptor : TypeDescriptor) : Option (StructInfo schema) :=
  tables.entries.find? fun info => info.typeDescriptor == descriptor

/--
Index explicit structure descriptions. The caller remains responsible for C
type conversion, parser field discovery, padding, offsets, and layout proofs.
-/
def getProgStructInfo (structures : List (StructInfo schema)) : StructTables schema :=
  { entries := structures }

/-! ## Generated metadata and separate logical certificates -/

/-- Pure generated metadata corresponding to upstream `heap_info`. -/
structure HeapInfo
    (schema : Schema Globals Tag globalCount heapCount) where
  rawRead : Globals -> HeapRawState Tag
  rawWrite : (HeapRawState Tag -> HeapRawState Tag) -> Globals -> Globals
  structures : StructTables schema

namespace HeapInfo

def stateMap {Globals Tag : Type u} {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) (globals : Globals) : LiftedGlobals schema :=
  liftGlobalHeap schema globals (info.rawRead globals)

end HeapInfo

/-- Pure setup corresponding to the data-producing upstream `setup`. -/
def setup [DecidableEq Tag]
    (schema : Schema Globals Tag globalCount heapCount)
    (rawRead : Globals -> HeapRawState Tag)
    (rawWrite : (HeapRawState Tag -> HeapRawState Tag) -> Globals -> Globals)
    (structures : List (StructInfo schema)) : HeapInfo schema :=
  { rawRead, rawWrite, structures := getProgStructInfo structures }

/-- The exact proposition selected by one field's computable description. -/
def StructFieldObligation.Holds {Globals Tag : Type u}
    {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) {Parent Field : Type u}
    (description : StructFieldObligation schema Parent Field)
    (fieldGet : Parent -> Field)
    (fieldSet : (Field -> Field) -> Parent -> Parent) : Prop :=
  match description with
  | .valid parserLayout parentSpec fieldName fieldSpec fieldAddress =>
      HeapLift.ValidStructField parserLayout parentSpec fieldName fieldSpec
        fieldGet fieldSet fieldAddress info.rawRead info.rawWrite
  | .legacy fieldName fieldAddress read write validRead validWrite parentSpec
      fieldSpec =>
      HeapLift.ValidStructFieldLegacy info.stateMap fieldName fieldGet
        (fun value => fieldSet (fun _ => value)) fieldAddress read write
        validRead validWrite info.rawRead info.rawWrite parentSpec fieldSpec

/-- The certificate proposition attached to one exact structure-field entry. -/
def StructFieldInfo.Valid {Globals Tag : Type u} {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) {Parent : Type u}
    (field : StructFieldInfo schema Parent) : Prop :=
  field.obligation.Holds info field.getter field.setter

/-- Setter commutation for one copied global field. -/
def CopiedGlobalSetterCommutes {Globals Tag : Type u}
    {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) (field : Fin globalCount) : Prop :=
  forall (transform : (schema.globals field).Value ->
      (schema.globals field).Value) globals,
    info.stateMap ((schema.globals field).setter transform globals) =
      (copiedGlobalLens schema field).modify transform (info.stateMap globals)

/--
All non-generic obligations emitted as theorem goals upstream. Raw-heap lens
laws, byte commutation, guards, validity preservation, and copied setter
commutation are inputs rather than consequences claimed from a codec alone.
-/
structure CertificateObligations {Globals Tag : Type u}
    {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) : Prop where
  validTypedHeap : forall kind : Fin heapCount,
    HeapLift.ValidTypedHeap info.stateMap
      (typedHeapLens schema kind).get (typedHeapLens schema kind).modify
      (validityLens schema kind).get (validityLens schema kind).modify
      info.rawRead info.rawWrite (schema.heaps kind).spec
  copiedSetterCommutes : forall field : Fin globalCount,
    CopiedGlobalSetterCommutes info field
  validStructFields : forall (entry : StructInfo schema),
    entry ∈ info.structures.entries ->
    forall field : StructFieldInfo schema entry.Value,
      field ∈ entry.fields -> field.Valid info

/-- The assembled setup certificate, including both copied-field laws. -/
structure HeapLiftSetup {Globals Tag : Type u} {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema) : Prop where
  validTypedHeap : forall kind : Fin heapCount,
    HeapLift.ValidTypedHeap info.stateMap
      (typedHeapLens schema kind).get (typedHeapLens schema kind).modify
      (validityLens schema kind).get (validityLens schema kind).modify
      info.rawRead info.rawWrite (schema.heaps kind).spec
  copiedGetterCommutes : forall (field : Fin globalCount) globals,
    (copiedGlobalLens schema field).get (info.stateMap globals) =
      (schema.globals field).getter globals
  copiedSetterCommutes : forall field : Fin globalCount,
    CopiedGlobalSetterCommutes info field
  validStructFields : forall (entry : StructInfo schema),
    entry ∈ info.structures.entries ->
    forall field : StructFieldInfo schema entry.Value,
      field ∈ entry.fields -> field.Valid info

/-- Logical certificate assembly is deliberately separate from pure `setup`. -/
theorem assembleCertificate {Globals Tag : Type u} {globalCount heapCount : Nat}
    {schema : Schema Globals Tag globalCount heapCount} [DecidableEq Tag]
    (info : HeapInfo schema)
    (obligations : CertificateObligations info) : HeapLiftSetup info where
  validTypedHeap := obligations.validTypedHeap
  copiedGetterCommutes := by
    intro field globals
    simp [HeapInfo.stateMap, liftGlobalHeap, copiedGlobalLens]
  copiedSetterCommutes := obligations.copiedSetterCommutes
  validStructFields := obligations.validStructFields

/-! ## Reduction pins -/

/-- Signed array elements below pointers select the unsigned element heap. -/
theorem canonicalHeapType_pin :
    canonicalHeapType (.pointer (.array (.signedWord 32) 7)) =
      .pointer (.word 32) := by
  rfl

/-- Selection canonicalizes, removes `unit`, and deduplicates selected heaps. -/
theorem getProgramHeapTypes_pin :
    getProgramHeapTypes
      [.atom (.pointer (.array (.signedWord 16) 4))
        [.pointer .unit, .pointer (.word 16)]] false = [.word 16] := by
  rfl

private structure PinGlobals where
  counter : Nat

private def pinField : FieldInfo PinGlobals where
  Value := Nat
  oldName := "counter_'"
  newName := "counter"
  typeDescriptor := .word 32
  getter := PinGlobals.counter
  setter := fun transform globals => { counter := transform globals.counter }

private def pinSpec : TypeSpec String UInt8 where
  info := { tag := "u8", size := 1 }
  guard := fun address => decide (address = 4)
  encode := fun value => [value]
  decode := fun bytes => bytes[0]?.getD 0
  sizePositive := by decide
  encodeLength := by intro value; simp
  decodeEncode := by intro value; simp

private def pinKind : HeapKind String where
  Value := UInt8
  descriptor := .word 8
  spec := pinSpec
  defaultValue := 99

private def pinSchema : Schema PinGlobals String 1 1 :=
  genNewHeap (fun _ => pinField) (fun _ => pinKind)

private def pinRaw : HeapRawState String where
  mem := fun address => if address = 4 then 42 else 0
  htd := ptrRetype 4 pinSpec.info fun _ => .heapEmpty

/-- Generated copied and validity projections reduce from genuine input state. -/
theorem generatedProjection_pin :
    let lifted := liftGlobalHeap pinSchema { counter := 37 } pinRaw
    (show Nat from lifted.copied 0) = 37 /\ lifted.valid 0 ⟨4⟩ /\
      Not (lifted.valid 0 ⟨5⟩) /\
        (show UInt8 from lifted.heap 0 ⟨5⟩) = 99 := by
  change 37 = 37 /\
    (simpleLift pinRaw pinSpec ⟨4⟩).isSome = true /\
    Not ((simpleLift pinRaw pinSpec ⟨5⟩).isSome = true) /\
    (simpleLift pinRaw pinSpec ⟨5⟩).getD 99 = 99
  native_decide

end Zag.Lang.AutoCorres.ML.HeapLiftBase
