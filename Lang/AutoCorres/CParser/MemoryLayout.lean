import Lang.AutoCorres.CParser.ProgramAnalysis

/-!
# Certified global object layout

Global and static-duration objects receive deterministic aligned byte ranges in
the target pointer address space. This module allocates objects only; byte
initialization and expression lowering are separate semantic layers.
-/

namespace Zag.Lang.AutoCorres.CParser.MemoryLayout

open ProgramAnalysis

inductive Error where
  | missingSymbol (symbolId : Nat)
  | unsupportedType (symbolId : Nat) (type : AnalyzedCType)
  | invalidSize (symbolId : Nat) (size : Int)
  | invalidAlignment (symbolId : Nat)
  | addressSpaceOverflow (symbolId base size limit : Nat)
  | invalidTarget
  | invariantFailure
deriving Repr, Inhabited

structure Object where
  symbolId : Nat
  type : AnalyzedCType
  base : Nat
  size : Nat
  alignment : Nat
deriving Repr, Inhabited

inductive PathStep where
  | index (index : Nat)
  | field (structId fieldIndex : Nat)
deriving Repr, BEq, Inhabited

structure ScalarLeaf where
  objectSymbolId : Nat
  path : List PathStep
  type : AnalyzedCType
  offset : Nat
  size : Nat
  alignment : Nat
deriving Repr, BEq, Inhabited

namespace Object

def limit (object : Object) : Nat := object.base + object.size

def contains (object : Object) (address : Nat) : Bool :=
  object.base ≤ address && address < object.limit

def aligned (object : Object) : Bool :=
  object.alignment > 0 && object.base % object.alignment = 0

def disjoint (left right : Object) : Bool :=
  left.limit ≤ right.base || right.limit ≤ left.base

end Object

structure Layout where
  pointerWidth : Nat
  objects : List Object
  leaves : List ScalarLeaf
  nextAddress : Nat
deriving Repr, Inhabited

namespace Layout

def addressLimit (layout : Layout) : Nat := 2 ^ layout.pointerWidth

def objectBySymbolId? (layout : Layout) (symbolId : Nat) : Option Object :=
  layout.objects.find? (·.symbolId = symbolId)

def objectAt? (layout : Layout) (address : Nat) : Option Object :=
  layout.objects.find? (·.contains address)

def leafAddress? (layout : Layout) (leaf : ScalarLeaf) : Option Nat := do
  let object ← layout.objectBySymbolId? leaf.objectSymbolId
  return object.base + leaf.offset

def leafAt? (layout : Layout) (symbolId address : Nat)
    (type : AnalyzedCType) : Option ScalarLeaf :=
  layout.leaves.find? fun leaf =>
    leaf.objectSymbolId = symbolId && leaf.type == type &&
      layout.leafAddress? leaf == some address

end Layout

private def structInfo? (program : Program) (name : String) : Option StructInfo :=
  program.structs.find? (·.canonicalName = name)

private def structSize (program : Program) (name : String) : Int :=
  (structInfo? program name).map (Int.ofNat ·.size) |>.getD (-1)

private def sizeOf (program : Program) (symbolId : Nat) (type : AnalyzedCType) :
    Except Error Nat := do
  let size ← CType.sizeof program.target (structSize program) type |>.mapError fun _ =>
    .unsupportedType symbolId type
  if size ≤ 0 then .error (.invalidSize symbolId size)
  return size.toNat

private def alignmentOf (program : Program) (symbolId : Nat) :
    AnalyzedCType → Except Error Nat
  | type@(.signed kind) | type@(.unsigned kind) => do
      let size ← CType.intSizeOf program.target kind |>.mapError fun _ =>
        .unsupportedType symbolId type
      if size = 0 then .error (.invalidAlignment symbolId) else return size
  | .plainChar => .ok 1
  | .bool =>
      if program.target.charWidth = 0 then .error (.invalidAlignment symbolId)
      else
        let size := program.target.boolWidth / program.target.charWidth
        if size = 0 then .error (.invalidAlignment symbolId) else .ok size
  | .enumTy _ => do
      let type : AnalyzedCType := .signed .int
      let size ← CType.intSizeOf program.target .int |>.mapError fun _ =>
        .unsupportedType symbolId type
      if size = 0 then .error (.invalidAlignment symbolId) else return size
  | .ptr _ =>
      if program.target.charWidth = 0 then .error (.invalidAlignment symbolId)
      else
        let size := program.target.pointerWidth / program.target.charWidth
        if size = 0 then .error (.invalidAlignment symbolId) else .ok size
  | .array element _ => alignmentOf program symbolId element
  | .structTy name =>
      match structInfo? program name with
      | some info =>
          if info.complete && info.alignment > 0 then .ok info.alignment
          else .error (.invalidAlignment symbolId)
      | none => .error (.unsupportedType symbolId (.structTy name))
  | type => .error (.unsupportedType symbolId type)

def alignUp (address alignment : Nat) : Nat :=
  if alignment = 0 then address
  else ((address + alignment - 1) / alignment) * alignment

private def allocateObject (program : Program) (limit : Nat) (nextAddress : Nat)
    (symbolId : Nat) : Except Error (Object × Nat) := do
  let symbol ← match program.symbolById? symbolId with
    | some symbol => .ok symbol
    | none => .error (.missingSymbol symbolId)
  let size ← sizeOf program symbolId symbol.type
  let alignment ← alignmentOf program symbolId symbol.type
  let base := alignUp nextAddress alignment
  -- Keep the exclusive limit representable so every object has a numeric
  -- one-past pointer in the target-width pointer model.
  if limit ≤ base + size then
    .error (.addressSpaceOverflow symbolId base size limit)
  let object : Object := { symbolId, type := symbol.type, base, size, alignment }
  return (object, base + size)

private def allocateAll (program : Program) (limit : Nat) :
    List Nat → Nat → Except Error (List Object × Nat)
  | [], nextAddress => .ok ([], nextAddress)
  | symbolId :: symbolIds, nextAddress => do
      let (object, nextAddress) ← allocateObject program limit nextAddress symbolId
      let (objects, finalAddress) ← allocateAll program limit symbolIds nextAddress
      return (object :: objects, finalAddress)

private def scalarLeavesAtAux (program : Program) (symbolId : Nat) :
    List Nat → AnalyzedCType → Nat → List PathStep → Except Error (List ScalarLeaf)
  | _, type@(.signed _), offset, path
  | _, type@(.unsigned _), offset, path
  | _, type@(.plainChar), offset, path
  | _, type@(.bool), offset, path
  | _, type@(.enumTy _), offset, path
  | _, type@(.ptr _), offset, path => do
      let size ← sizeOf program symbolId type
      let alignment ← alignmentOf program symbolId type
      return [{ objectSymbolId := symbolId, path, type, offset, size, alignment }]
  | remainingStructIds, .array element (some count), offset, path => do
      if count < 0 then .error (.invalidSize symbolId count)
      let elementSize ← sizeOf program symbolId element
      let mut leaves := []
      for index in List.range count.toNat do
        let nested ← scalarLeavesAtAux program symbolId remainingStructIds element
          (offset + index * elementSize) (path ++ [.index index])
        leaves := leaves ++ nested
      return leaves
  | remainingStructIds, .structTy name, offset, path => do
      let info ← match structInfo? program name with
        | some info => .ok info
        | none => .error (.unsupportedType symbolId (.structTy name))
      if h : info.id ∈ remainingStructIds then
        let remainingStructIds := remainingStructIds.erase info.id
        let mut leaves := []
        for (field, fieldIndex) in info.fields.zipIdx do
          let nested ← scalarLeavesAtAux program symbolId remainingStructIds field.type
            (offset + field.offset) (path ++ [.field info.id fieldIndex])
          leaves := leaves ++ nested
        return leaves
      else
        .error .invariantFailure
  | _, type, _, _ => .error (.unsupportedType symbolId type)
termination_by remainingStructIds type _ _ =>
  (remainingStructIds.length, SizeOf.sizeOf type)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.right
      simp_wf <;> omega
    | apply Prod.Lex.left
      rw [List.length_erase_of_mem h]
      have := List.length_pos_of_mem h
      omega

private def scalarLeavesAt (program : Program) (symbolId : Nat)
    (type : AnalyzedCType) (offset : Nat) (path : List PathStep) :
    Except Error (List ScalarLeaf) :=
  scalarLeavesAtAux program symbolId (program.structs.map (·.id)) type offset path

private def scalarLeaves (program : Program) (objects : List Object) :
    Except Error (List ScalarLeaf) := do
  let mut leaves := []
  for object in objects do
    let nested ← scalarLeavesAt program object.symbolId object.type 0 []
    leaves := leaves ++ nested
  return leaves

/-- Reserve low addresses so generated object pointers are never null. -/
def firstAddress : Nat := 4096

private def staticObjectIds (program : Program) : List Nat :=
  program.staticObjects.map (·.symbolId)

private def validTarget (target : Target) : Bool :=
  let widths := [target.boolWidth, target.charWidth, target.shortWidth,
    target.intWidth, target.longWidth, target.longLongWidth, target.pointerWidth]
  target.charWidth > 0 && target.charWidth % 8 = 0 &&
    widths.all fun width =>
      width > 0 && width ≤ 64 && width % target.charWidth = 0

def generate (program : Program) : Except Error Layout := do
  if !validTarget program.target then .error .invalidTarget
  let limit := 2 ^ program.target.pointerWidth
  if limit ≤ firstAddress then
    .error (.addressSpaceOverflow 0 firstAddress 0 limit)
  let (objects, nextAddress) ← allocateAll program limit (staticObjectIds program) firstAddress
  let leaves ← scalarLeaves program objects
  return { pointerWidth := program.target.pointerWidth, objects, leaves, nextAddress }

structure Checks where
  pointerWidthExact : Bool
  exactSymbols : Bool
  uniqueSymbols : Bool
  metadataExact : Bool
  leavesExact : Bool
  leavesInsideObjects : Bool
  leavesPairwiseDisjoint : Bool
  leavesAligned : Bool
  positiveSizes : Bool
  aligned : Bool
  placementExact : Bool
  pairwiseDisjoint : Bool
  bounded : Bool
  nextAddressExact : Bool
deriving Repr, DecidableEq, Inhabited

namespace Checks

def all (checks : Checks) : Bool :=
  checks.pointerWidthExact && checks.exactSymbols && checks.uniqueSymbols &&
    checks.metadataExact && checks.positiveSizes && checks.aligned &&
    checks.leavesExact && checks.leavesInsideObjects && checks.leavesPairwiseDisjoint &&
    checks.leavesAligned && checks.placementExact && checks.pairwiseDisjoint &&
    checks.bounded && checks.nextAddressExact

end Checks

private def pairwise (values : List α) (relation : α → α → Bool) : Bool :=
  match values with
  | [] => true
  | value :: values => values.all (relation value) && pairwise values relation

private def metadataValid (program : Program) (object : Object) : Bool :=
  match program.symbolById? object.symbolId,
      sizeOf program object.symbolId object.type,
      alignmentOf program object.symbolId object.type with
  | some symbol, .ok size, .ok alignment =>
      object.type == symbol.type && object.size = size && object.alignment = alignment
  | _, _, _ => false

private def placementValid : List Object → Nat → Bool
  | [], _ => true
  | object :: objects, nextAddress =>
      object.base = alignUp nextAddress object.alignment &&
        placementValid objects object.limit

private def leavesDisjoint (layout : Layout) (left right : ScalarLeaf) : Bool :=
  match layout.leafAddress? left, layout.leafAddress? right with
  | some leftAddress, some rightAddress =>
      leftAddress + left.size ≤ rightAddress || rightAddress + right.size ≤ leftAddress
  | _, _ => false

private def expectedLeaves? (program : Program) (objects : List Object) :
    Option (List ScalarLeaf) :=
  (scalarLeaves program objects).toOption

def check (program : Program) (layout : Layout) : Checks :=
  let symbolIds := layout.objects.map (·.symbolId)
  let limit := layout.addressLimit
  let expectedNext := layout.objects.getLast?.map Object.limit |>.getD firstAddress
  { pointerWidthExact := layout.pointerWidth = program.target.pointerWidth
    exactSymbols := symbolIds == staticObjectIds program
    uniqueSymbols := symbolIds.eraseDups.length = symbolIds.length
    metadataExact := layout.objects.all (metadataValid program)
    leavesExact := expectedLeaves? program layout.objects == some layout.leaves
    leavesInsideObjects := layout.leaves.all fun leaf =>
      match layout.objectBySymbolId? leaf.objectSymbolId with
      | some object => leaf.offset + leaf.size ≤ object.size
      | none => false
    leavesPairwiseDisjoint := pairwise layout.leaves (leavesDisjoint layout)
    leavesAligned := layout.leaves.all fun leaf =>
      match layout.leafAddress? leaf with
      | some address => leaf.alignment > 0 && address % leaf.alignment = 0
      | none => false
    positiveSizes := layout.objects.all (·.size > 0)
    aligned := layout.objects.all (·.aligned)
    placementExact := placementValid layout.objects firstAddress
    pairwiseDisjoint := pairwise layout.objects Object.disjoint
    bounded := layout.objects.all fun object => object.limit < limit
    nextAddressExact := layout.nextAddress = expectedNext }

structure Certificate (program : Program) where
  layout : Layout
  generated : generate program = .ok layout
  valid : (check program layout).all = true

def certify (program : Program) : Except Error (Certificate program) :=
  match generated : generate program with
  | .error error => .error error
  | .ok layout =>
      if valid : (check program layout).all = true then
        .ok { layout, generated, valid }
      else
        .error .invariantFailure

end Zag.Lang.AutoCorres.CParser.MemoryLayout
