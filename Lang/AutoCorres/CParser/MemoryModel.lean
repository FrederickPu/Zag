import Lang.AutoCorres.CParser.MemoryLayout
import Lang.AutoCorres.CParser.ScalarSimpl

/-! # Bounded ARM byte memory for analyzed C -/

namespace Zag.Lang.AutoCorres.CParser.MemoryModel

open ProgramAnalysis
open MemoryLayout
open ScalarSimpl

abbrev Address := BitVec 32
abbrev ByteHeap := Address → UInt8

structure Pointer where
  address : Address
  provenance : Option Nat
deriving Repr, DecidableEq

namespace Pointer

def null : Pointer := { address := 0, provenance := none }

def ofGlobal? (layout : Layout) (symbolId : Nat) : Option Pointer := do
  if layout.pointerWidth != 32 then none
  let object ← layout.objectBySymbolId? symbolId
  if 2 ^ 32 ≤ object.limit then none
  return { address := BitVec.ofNat 32 object.base, provenance := some symbolId }

def add? (layout : Layout) (pointer : Pointer) (elementSize : Nat)
    (index : Int) : Option Pointer := do
  if layout.pointerWidth != 32 then none
  if elementSize = 0 then none
  let symbolId ← pointer.provenance
  let object ← layout.objectBySymbolId? symbolId
  if 2 ^ 32 ≤ object.limit then none
  let address := pointer.address.toNat
  if address < object.base || object.limit < address then none
  let count ← match object.type with
    | .array _ (some count) => if 0 < count then some count.toNat else none
    | _ => none
  if object.size % count != 0 then none
  let expectedElementSize := object.size / count
  if elementSize != expectedElementSize then none
  if (address - object.base) % elementSize != 0 then none
  let offset : Int := Int.ofNat (address - object.base)
  let next := offset + index * Int.ofNat elementSize
  if next < 0 || Int.ofNat object.size < next then none
  let nextAddress := object.base + next.toNat
  if 2 ^ 32 ≤ nextAddress then none
  return { address := BitVec.ofNat 32 nextAddress, provenance := some symbolId }

end Pointer

def zeroHeap : ByteHeap := fun _ => 0

private def addressRange? (start size : Nat) : Option (List Address) :=
  if start + size ≤ 2 ^ 32 then
    some (List.ofFn fun offset : Fin size => BitVec.ofNat 32 (start + offset.val))
  else none

def readBytes? (heap : ByteHeap) (start size : Nat) : Option (List UInt8) := do
  let addresses ← addressRange? start size
  return addresses.map heap

def writeBytes? (heap : ByteHeap) (start : Nat) (bytes : List UInt8) : Option ByteHeap := do
  let _ ← addressRange? start bytes.length
  return fun address =>
    let value := address.toNat
    if start ≤ value && value < start + bytes.length then
      (bytes[value - start]?).getD (heap address)
    else heap address

private def normalizeUnsigned (width : Nat) (value : Int) : Int :=
  let modulus := (2 : Int) ^ width
  ((value % modulus) + modulus) % modulus

def encodeIntegerLE (byteCount : Nat) (value : Int) : List UInt8 :=
  let value := normalizeUnsigned (byteCount * 8) value
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofNat ((value / (2 : Int) ^ (index.val * 8)) % 256).toNat

def decodeUnsignedLE (bytes : List UInt8) : Int :=
  bytes.zipIdx.foldl (fun value (byte, index) =>
    value + Int.ofNat byte.toNat * (2 : Int) ^ (index * 8)) 0

def decodeIntegerLE (type : ScalarType) (bytes : List UInt8) : Int :=
  type.cast (decodeUnsignedLE bytes)

/-- Caller-owned storage made available to an analyzed C function. -/
structure ExternalObject where
  provenance : Nat
  base : Nat
  size : Nat
  type : AnalyzedCType
deriving Repr, DecidableEq, Inhabited

abbrev ExternalMemory := List ExternalObject

def authorized {program : Program} (certificate : MemoryLayout.Certificate program)
    (type : AnalyzedCType) (pointer : Pointer) : Bool :=
  if program.target != Target.arm then false
  else match pointer.provenance with
    | none => false
    | some symbolId =>
        (certificate.layout.leafAt? symbolId pointer.address.toNat type).isSome

private def armScalarType : AnalyzedCType → Option ScalarType
  | .signed kind => some ⟨.signed, Target.arm.intWidthOf kind⟩
  | .unsigned kind => some ⟨.unsigned, Target.arm.intWidthOf kind⟩
  | .plainChar => some ⟨if Target.arm.charSigned then .signed else .unsigned,
      Target.arm.charWidth⟩
  | .bool => some ⟨.unsigned, Target.arm.boolWidth⟩
  | .enumTy _ => some ⟨.signed, Target.arm.intWidth⟩
  | _ => none

def ExternalObject.authorizes (object : ExternalObject) (type : AnalyzedCType)
    (pointer : Pointer) : Bool :=
  match pointer.provenance, armScalarType type with
  | some provenance, some scalarType =>
      let byteCount := scalarType.width / 8
      provenance = object.provenance && type == object.type &&
        scalarType.width % 8 = 0 && byteCount > 0 &&
        object.base ≤ pointer.address.toNat &&
        pointer.address.toNat + byteCount ≤ object.base + object.size &&
        object.base + object.size ≤ 2 ^ 32 &&
        pointer.address.toNat % byteCount = 0
  | _, _ => false

def externalObject? (memory : ExternalMemory) (type : AnalyzedCType)
    (pointer : Pointer) : Option ExternalObject :=
  match memory.filter (·.authorizes type pointer) with
  | [object] => some object
  | _ => none

private def castArmInteger (type : AnalyzedCType) (scalarType : ScalarType)
    (value : Int) : Int :=
  match type with
  | .bool => if value = 0 then 0 else 1
  | _ => scalarType.cast value

def loadExternalInteger? (memory : ExternalMemory) (type : AnalyzedCType)
    (pointer : Pointer) (heap : ByteHeap) : Option Int := do
  let _ ← externalObject? memory type pointer
  let scalarType ← armScalarType type
  if scalarType.width % 8 != 0 then none
  let bytes ← readBytes? heap pointer.address.toNat (scalarType.width / 8)
  return castArmInteger type scalarType (decodeIntegerLE scalarType bytes)

def storeExternalInteger? (memory : ExternalMemory) (type : AnalyzedCType)
    (pointer : Pointer) (value : Int) (heap : ByteHeap) : Option ByteHeap := do
  let _ ← externalObject? memory type pointer
  let scalarType ← armScalarType type
  if scalarType.width % 8 != 0 then none
  writeBytes? heap pointer.address.toNat
    (encodeIntegerLE (scalarType.width / 8) (castArmInteger type scalarType value))

def loadInteger? {program : Program} (certificate : MemoryLayout.Certificate program)
    (type : AnalyzedCType) (pointer : Pointer) (heap : ByteHeap) : Option Int := do
  if program.target != Target.arm then none
  let symbolId ← pointer.provenance
  let leaf ← certificate.layout.leafAt? symbolId pointer.address.toNat type
  let scalarType ← armScalarType type
  if leaf.size * 8 != scalarType.width then none
  let bytes ← readBytes? heap pointer.address.toNat leaf.size
  return castArmInteger type scalarType (decodeIntegerLE scalarType bytes)

def storeInteger? {program : Program} (certificate : MemoryLayout.Certificate program)
    (type : AnalyzedCType) (pointer : Pointer) (value : Int)
    (heap : ByteHeap) : Option ByteHeap := do
  if program.target != Target.arm then none
  let symbolId ← pointer.provenance
  let leaf ← certificate.layout.leafAt? symbolId pointer.address.toNat type
  let scalarType ← armScalarType type
  if leaf.size * 8 != scalarType.width then none
  writeBytes? heap pointer.address.toNat
    (encodeIntegerLE leaf.size (castArmInteger type scalarType value))

def loadIntegerIn? {program : Program} (certificate : MemoryLayout.Certificate program)
    (external : ExternalMemory) (type : AnalyzedCType) (pointer : Pointer)
    (heap : ByteHeap) : Option Int :=
  (loadInteger? certificate type pointer heap).orElse fun _ =>
    loadExternalInteger? external type pointer heap

def storeIntegerIn? {program : Program} (certificate : MemoryLayout.Certificate program)
    (external : ExternalMemory) (type : AnalyzedCType) (pointer : Pointer)
    (value : Int) (heap : ByteHeap) : Option ByteHeap :=
  (storeInteger? certificate type pointer value heap).orElse fun _ =>
    storeExternalInteger? external type pointer value heap

@[simp] theorem loadIntegerIn_of_static {program : Program}
    (certificate : MemoryLayout.Certificate program) (external : ExternalMemory)
    (type : AnalyzedCType) (pointer : Pointer) (heap : ByteHeap)
    (value : Int) (loaded : loadInteger? certificate type pointer heap = some value) :
    loadIntegerIn? certificate external type pointer heap = some value := by
  simp [loadIntegerIn?, loaded]

@[simp] theorem storeIntegerIn_of_static {program : Program}
    (certificate : MemoryLayout.Certificate program) (external : ExternalMemory)
    (type : AnalyzedCType) (pointer : Pointer) (value : Int) (heap result : ByteHeap)
    (stored : storeInteger? certificate type pointer value heap = some result) :
    storeIntegerIn? certificate external type pointer value heap = some result := by
  simp [storeIntegerIn?, stored]

structure Image (program : Program) where
  layout : MemoryLayout.Certificate program
  bytes : ByteHeap

inductive InitializationError where
  | layout (error : MemoryLayout.Error)
  | unsupportedTarget
  | unsupportedInitializer (symbolId : Nat)
  | initializerValueCount (symbolId expected actual : Nat)
  | initializerStore (symbolId : Nat)
deriving Repr, Inhabited

private def writeInitialValues {program : Program}
    (certificate : MemoryLayout.Certificate program) (symbolId : Nat) :
    List ScalarLeaf → List Int → ByteHeap → Except InitializationError ByteHeap
  | _, [], heap => .ok heap
  | [], _ :: _, _ => .error (.initializerStore symbolId)
  | leaf :: leaves, value :: values, heap => do
      let address ← match certificate.layout.leafAddress? leaf with
        | some address => .ok address
        | none => .error (.initializerStore symbolId)
      let pointer : Pointer :=
        { address := BitVec.ofNat 32 address, provenance := some symbolId }
      let stored := match leaf.type with
        | .ptr _ =>
            if value = 0 then writeBytes? heap address (List.replicate leaf.size 0)
            else none
        | _ => storeInteger? certificate leaf.type pointer value heap
      let heap ← match stored with
        | some heap => .ok heap
        | none => .error (.initializerStore symbolId)
      writeInitialValues certificate symbolId leaves values heap

private def applyInitializer {program : Program}
    (certificate : MemoryLayout.Certificate program) (object : StaticObjectInfo)
    (heap : ByteHeap) : Except InitializationError ByteHeap := do
  let values ← match object.initializerValues with
    | some values => .ok values
    | none => .error (.unsupportedInitializer object.symbolId)
  let leaves := certificate.layout.leaves.filter (·.objectSymbolId = object.symbolId)
  if leaves.length < values.length then
    .error (.initializerValueCount object.symbolId leaves.length values.length)
  writeInitialValues certificate object.symbolId leaves values heap

private def initializeObjects {program : Program}
    (certificate : MemoryLayout.Certificate program) :
    List StaticObjectInfo → ByteHeap → Except InitializationError ByteHeap
  | [], heap => .ok heap
  | object :: objects, heap => do
      let heap ← match object.initialization with
        | .zero => .ok heap
        | .explicit _ => applyInitializer certificate object heap
      initializeObjects certificate objects heap

/-- Construct the ARM static image, including the supported integer initializers. -/
def initializeWith {program : Program} (layout : MemoryLayout.Certificate program) :
    Except InitializationError (Image program) := do
  if program.target != Target.arm then
    .error InitializationError.unsupportedTarget
  let bytes ← initializeObjects layout program.staticObjects zeroHeap
  return { layout := layout, bytes := bytes }

def initializeImage (program : Program) : Except InitializationError (Image program) := do
  if program.target != Target.arm then
    .error InitializationError.unsupportedTarget
  let layout ← (MemoryLayout.certify program).mapError InitializationError.layout
  initializeWith layout

/-- The zero-only entry point rejects any explicit initializer. -/
def initializeZero (program : Program) : Except InitializationError (Image program) := do
  for object in program.staticObjects do
    match object.initialization with
    | .zero => .ok ()
    | .explicit _ =>
        .error (InitializationError.unsupportedInitializer object.symbolId)
  initializeImage program

end Zag.Lang.AutoCorres.CParser.MemoryModel
