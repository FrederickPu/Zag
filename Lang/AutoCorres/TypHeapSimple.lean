import Std

/-!
# Simple typed heaps

Corresponds only to [`tools/autocorres/TypHeapSimple.thy`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/TypHeapSimple.thy).

The C parser's nested UMM descriptors are deliberately represented by their
already-collapsed top-level tags. `TypeSpec` makes the unavailable concrete C
type information explicit: object size, pointer guard, and byte codec are data.
Addresses are unbounded naturals, so byte ranges do not wrap.
-/

namespace Zag.Lang.AutoCorres.TypHeapSimple

universe u v

variable {Tag : Type u}

/-- The top-level information committed to an object's first byte. -/
structure TypeInfo (Tag : Type u) where
  tag : Tag
  size : Nat
deriving DecidableEq, Repr

/-- A byte is an object head, a later byte of one object, or uncommitted. -/
inductive HeapTypContents (Tag : Type u) where
  | heapType (info : TypeInfo Tag)
  | heapFootprint
  | heapEmpty
deriving DecidableEq, Repr

/-- The simple projection of a heap type description. -/
abbrev HeapTypDesc (Tag : Type u) := Nat → HeapTypContents Tag

/-- In this generic model the descriptor has already been reduced to one tag. -/
def heapTypeTag (description : HeapTypDesc Tag) (address : Nat) :
    HeapTypContents Tag :=
  description address

/-- The half-open byte range `[start, start + size)`. -/
def ByteRange (start size address : Nat) : Prop :=
  start ≤ address ∧ address < start + size

/-- A head tag followed only by footprint bytes for the declared size. -/
def ValidSimpleFootprint (description : HeapTypDesc Tag) (start : Nat)
    (info : TypeInfo Tag) : Prop :=
  heapTypeTag description start = .heapType info ∧
    ∀ offset : Fin info.size, offset.val ≠ 0 →
      heapTypeTag description (start + offset.val) = .heapFootprint

theorem validSimpleFootprintI
    (head : heapTypeTag description start = .heapType info)
    (rest : ∀ offset, 0 < offset → offset < info.size →
      heapTypeTag description (start + offset) = .heapFootprint) :
    ValidSimpleFootprint description start info := by
  refine ⟨head, ?_⟩
  intro offset nonzero
  exact rest offset.val (Nat.pos_of_ne_zero nonzero) offset.isLt

theorem validSimpleFootprintD
    (valid : ValidSimpleFootprint description start info) :
    heapTypeTag description start = .heapType info :=
  valid.1

theorem validSimpleFootprintD2
    (valid : ValidSimpleFootprint description start info)
    (positive : 0 < offset) (inside : offset < info.size) :
    heapTypeTag description (start + offset) = .heapFootprint :=
  valid.2 ⟨offset, inside⟩ (Nat.ne_of_gt positive)

/-- Commit a range directly in the simple descriptor. -/
def ptrRetype (start : Nat) (info : TypeInfo Tag)
    (description : HeapTypDesc Tag) : HeapTypDesc Tag := fun address =>
  if address = start then .heapType info
  else if start < address ∧ address < start + info.size then .heapFootprint
  else description address

@[simp] theorem heapTypeTagPtrRetype {start : Nat} {info : TypeInfo Tag}
    {description : HeapTypDesc Tag} :
    heapTypeTag (ptrRetype start info description) start = .heapType info := by
  simp [heapTypeTag, ptrRetype]

theorem heapTypeTagPtrRetypeRest {start offset : Nat} {info : TypeInfo Tag}
    {description : HeapTypDesc Tag}
    (positive : 0 < offset) (inside : offset < info.size) :
    heapTypeTag (ptrRetype start info description) (start + offset) =
      .heapFootprint := by
  simp [heapTypeTag, ptrRetype, Nat.ne_of_gt positive]
  omega

theorem validSimpleFootprintPtrRetype {start : Nat} {info : TypeInfo Tag}
    {description : HeapTypDesc Tag}
    (_positiveSize : 0 < info.size) :
    ValidSimpleFootprint (ptrRetype start info description) start info := by
  apply validSimpleFootprintI
  · exact heapTypeTagPtrRetype
  · intro offset positive inside
    exact heapTypeTagPtrRetypeRest positive inside

/-- All C-specific data needed to read and write values of one Lean type. -/
structure TypeSpec (Tag : Type u) (α : Type v) where
  info : TypeInfo Tag
  guard : Nat → Bool
  encode : α → List UInt8
  decode : List UInt8 → α
  sizePositive : 0 < info.size
  encodeLength : ∀ value, (encode value).length = info.size
  decodeEncode : ∀ value, decode (encode value) = value

/-- A typed pointer; its runtime representation is only its byte address. -/
structure Ptr (α : Type u) where
  val : Nat
deriving Repr

namespace Ptr

@[ext] theorem ext {left right : Ptr α} (equal : left.val = right.val) :
    left = right := by
  cases left
  cases right
  simp_all

end Ptr

instance : DecidableEq (Ptr α) := fun left right =>
  if equal : left.val = right.val then
    isTrue (Ptr.ext equal)
  else
    isFalse fun pointersEqual => equal (congrArg Ptr.val pointersEqual)

/-- Pointer validity is exactly a committed footprint and the explicit guard. -/
def HeapPtrValid (description : HeapTypDesc Tag) (spec : TypeSpec Tag α)
    (pointer : Ptr α) : Prop :=
  ValidSimpleFootprint description pointer.val spec.info ∧
    spec.guard pointer.val = true

instance [DecidableEq Tag] (description : HeapTypDesc Tag) (spec : TypeSpec Tag α)
    (pointer : Ptr α) : Decidable (HeapPtrValid description spec pointer) := by
  unfold HeapPtrValid ValidSimpleFootprint
  infer_instance

/-- Raw byte memory. -/
abbrev ByteHeap := Nat → UInt8

/-- Read `size` consecutive bytes. -/
def heapList (heap : ByteHeap) (size start : Nat) : List UInt8 :=
  List.ofFn fun offset : Fin size => heap (start + offset)

/-- Update exactly the range covered by `bytes`. -/
def heapUpdateList (start : Nat) (bytes : List UInt8) (heap : ByteHeap) :
    ByteHeap := fun address =>
  if start ≤ address ∧ address < start + bytes.length then
    (bytes[address - start]?).getD (heap address)
  else
    heap address

/-- Decode one typed object from raw bytes. -/
def hVal (spec : TypeSpec Tag α) (heap : ByteHeap) (pointer : Ptr α) : α :=
  spec.decode (heapList heap spec.info.size pointer.val)

/-- Encode and overwrite one typed object. -/
def heapUpdate (spec : TypeSpec Tag α) (pointer : Ptr α) (value : α)
    (heap : ByteHeap) : ByteHeap :=
  heapUpdateList pointer.val (spec.encode value) heap

/-- A raw heap state separates bytes from their simple type description. -/
structure HeapRawState (Tag : Type u) where
  mem : ByteHeap
  htd : HeapTypDesc Tag

/-- Lift raw bytes only at a valid typed pointer. -/
def simpleLift {Tag : Type u} [DecidableEq Tag] (state : HeapRawState Tag)
    (spec : TypeSpec Tag α) (pointer : Ptr α) : Option α :=
  if HeapPtrValid state.htd spec pointer then
    some (hVal spec state.mem pointer)
  else
    none

theorem simpleLiftHeapPtrValid {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    {value : α}
    (lifted : simpleLift state spec pointer = some value) :
    HeapPtrValid state.htd spec pointer := by
  by_cases valid : HeapPtrValid state.htd spec pointer
  · exact valid
  · simp [simpleLift, valid] at lifted

theorem simpleLiftGuard {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    {value : α}
    (lifted : simpleLift state spec pointer = some value) :
    spec.guard pointer.val = true :=
  (simpleLiftHeapPtrValid state spec pointer lifted).2

/-- Distinct valid object heads cannot occur inside one another's ranges. -/
theorem validSimpleFootprintNeq
    (validP : ValidSimpleFootprint description p s)
    (validQ : ValidSimpleFootprint description q t) (different : p ≠ q) :
    ¬ ByteRange q t.size p := by
  intro member
  have qltp : q < p := by
    have notEqual : q ≠ p := Ne.symm different
    unfold ByteRange at member
    omega
  have offsetPositive : 0 < p - q := by omega
  have offsetInside : p - q < t.size := by
    unfold ByteRange at member
    omega
  have footprint := validSimpleFootprintD2 validQ offsetPositive offsetInside
  have addressEq : q + (p - q) = p := by omega
  rw [addressEq, validSimpleFootprintD validP] at footprint
  cases footprint

/-- Valid footprints with unequal type information cannot overlap at their heads. -/
theorem validSimpleFootprintTypeNeq
    (validP : ValidSimpleFootprint description p s)
    (validQ : ValidSimpleFootprint description q t) (different : s ≠ t) :
    ¬ ByteRange q t.size p := by
  apply validSimpleFootprintNeq validP validQ
  intro equal
  subst q
  have heads := (validSimpleFootprintD validP).symm.trans
    (validSimpleFootprintD validQ)
  exact different (HeapTypContents.heapType.inj heads)

/-- Two ranges are disjoint when they have no common byte. -/
def DisjointRanges (p pSize q qSize : Nat) : Prop :=
  ∀ address, ByteRange p pSize address → ByteRange q qSize address → False

theorem validSimpleFootprintNeqDisjoint
    (validP : ValidSimpleFootprint description p s)
    (validQ : ValidSimpleFootprint description q t) (different : p ≠ q) :
    DisjointRanges p s.size q t.size := by
  intro address inP inQ
  by_cases order : p < q
  · apply validSimpleFootprintNeq validQ validP (Ne.symm different)
    unfold ByteRange at inP inQ ⊢
    omega
  · apply validSimpleFootprintNeq validP validQ different
    unfold ByteRange at inP inQ ⊢
    omega

theorem validSimpleFootprintTypeNeqDisjoint
    (validP : ValidSimpleFootprint description p s)
    (validQ : ValidSimpleFootprint description q t) (different : s ≠ t) :
    DisjointRanges p s.size q t.size := by
  apply validSimpleFootprintNeqDisjoint validP validQ
  intro equal
  subst q
  have heads := (validSimpleFootprintD validP).symm.trans
    (validSimpleFootprintD validQ)
  exact different (HeapTypContents.heapType.inj heads)

theorem heapPtrValidNeqDisjoint
    (validP : HeapPtrValid description specP pointerP)
    (validQ : HeapPtrValid description specQ pointerQ)
    (different : pointerP.val ≠ pointerQ.val) :
    DisjointRanges pointerP.val specP.info.size
      pointerQ.val specQ.info.size :=
  validSimpleFootprintNeqDisjoint validP.1 validQ.1 different

theorem heapPtrValidTypeNeqDisjoint
    (validP : HeapPtrValid description specP pointerP)
    (validQ : HeapPtrValid description specQ pointerQ)
    (different : specP.info ≠ specQ.info) :
    DisjointRanges pointerP.val specP.info.size
      pointerQ.val specQ.info.size :=
  validSimpleFootprintTypeNeqDisjoint validP.1 validQ.1 different

theorem heapUpdateListOutside (outside : ¬ ByteRange start bytes.length address) :
    heapUpdateList start bytes heap address = heap address := by
  unfold heapUpdateList
  split
  · rename_i inside
    exact False.elim (outside inside)
  · rfl

theorem heapListUpdateDisjointSame
    (disjoint : DisjointRanges readStart readSize writeStart bytes.length) :
    heapList (heapUpdateList writeStart bytes heap) readSize readStart =
      heapList heap readSize readStart := by
  refine List.ext_getElem (by simp [heapList]) ?_
  intro index left right
  simp only [heapList, List.getElem_ofFn]
  apply heapUpdateListOutside
  intro inWrite
  have indexInside : index < readSize := by
    simpa [heapList] using left
  exact disjoint (readStart + index)
    (by unfold ByteRange; omega) inWrite

theorem heapListUpdateSame
    (lengthEq : bytes.length = size) :
    heapList (heapUpdateList start bytes heap) size start = bytes := by
  subst size
  refine List.ext_getElem (by simp [heapList]) ?_
  intro index left right
  simp only [heapList, List.getElem_ofFn]
  simp [heapUpdateList, Nat.add_sub_cancel_left, right]

@[simp] theorem hValHeapUpdate
    (spec : TypeSpec Tag α) (pointer : Ptr α) (value : α) (heap : ByteHeap) :
    hVal spec (heapUpdate spec pointer value heap) pointer = value := by
  unfold hVal heapUpdate
  rw [heapListUpdateSame (spec.encodeLength value)]
  exact spec.decodeEncode value

theorem heapPtrValidHeapUpdateOther
    (validP : HeapPtrValid description specP pointerP)
    (validQ : HeapPtrValid description specQ pointerQ)
    (different : pointerP.val ≠ pointerQ.val) :
    hVal specQ (heapUpdate specP pointerP value heap) pointerQ =
      hVal specQ heap pointerQ := by
  unfold hVal heapUpdate
  rw [heapListUpdateDisjointSame]
  simpa [specP.encodeLength value] using
    heapPtrValidNeqDisjoint validQ validP (Ne.symm different)

theorem heapPtrValidHeapUpdateOtherType
    (validP : HeapPtrValid description specP pointerP)
    (validQ : HeapPtrValid description specQ pointerQ)
    (different : specP.info ≠ specQ.info) :
    hVal specQ (heapUpdate specP pointerP value heap) pointerQ =
      hVal specQ heap pointerQ := by
  unfold hVal heapUpdate
  rw [heapListUpdateDisjointSame]
  simpa [specP.encodeLength value] using
    heapPtrValidTypeNeqDisjoint validQ validP (Ne.symm different)

/-- Updating bytes does not alter the type description. -/
def memUpdate (update : ByteHeap → ByteHeap) (state : HeapRawState Tag) :
    HeapRawState Tag :=
  { state with mem := update state.mem }

/-- Functional update, kept local to avoid importing a map implementation. -/
def updateAt [DecidableEq ι] (function : ι → α) (key : ι) (value : α) : ι → α :=
  fun query => if query = key then value else function query

theorem simpleLiftHeapUpdate {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    (value : α)
    (valid : HeapPtrValid state.htd spec pointer) :
    simpleLift (memUpdate (heapUpdate spec pointer value) state) spec =
      updateAt (simpleLift state spec) pointer (some value) := by
  funext query
  by_cases equal : query = pointer
  · subst query
    simp [simpleLift, memUpdate, updateAt, valid]
  · by_cases queryValid : HeapPtrValid state.htd spec query
    · simp only [simpleLift, memUpdate, queryValid, if_true, updateAt, equal,
        if_false]
      congr 1
      exact heapPtrValidHeapUpdateOther valid queryValid (Ne.symm fun equality =>
        equal (Ptr.ext equality))
    · simp [simpleLift, memUpdate, updateAt, queryValid, equal]

theorem simpleLiftHeapUpdateOther {α β : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (specP : TypeSpec Tag α) (pointer : Ptr α)
    (value : α) (specQ : TypeSpec Tag β)
    (valid : HeapPtrValid state.htd specP pointer)
    (different : specQ.info ≠ specP.info) :
    simpleLift (memUpdate (heapUpdate specP pointer value) state) specQ =
      simpleLift state specQ := by
  funext query
  by_cases queryValid : HeapPtrValid state.htd specQ query
  · simp [simpleLift, memUpdate, queryValid]
    exact heapPtrValidHeapUpdateOtherType valid queryValid
      (Ne.symm different)
  · simp [simpleLift, memUpdate, queryValid]

theorem hValSimpleLift {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    {value : α}
    (lifted : simpleLift state spec pointer = some value) :
    hVal spec state.mem pointer = value := by
  have valid := simpleLiftHeapPtrValid state spec pointer lifted
  simpa [simpleLift, valid] using lifted

theorem simpleLiftHeapUpdate' {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    (value : α)
    {oldValue : α}
    (lifted : simpleLift state spec pointer = some oldValue) :
    simpleLift (memUpdate (heapUpdate spec pointer value) state) spec =
      updateAt (simpleLift state spec) pointer (some value) :=
  simpleLiftHeapUpdate state spec pointer value
    (simpleLiftHeapPtrValid state spec pointer lifted)

@[simp] theorem simpleLiftMemUpdateNone {α : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (spec : TypeSpec Tag α) (pointer : Ptr α)
    (update : ByteHeap → ByteHeap) :
    (simpleLift (memUpdate update state) spec pointer = none) ↔
      simpleLift state spec pointer = none := by
  simp [simpleLift, memUpdate]

theorem simpleLiftDataEq {α : Type v} [DecidableEq Tag]
    (state state' : HeapRawState Tag) (spec : TypeSpec Tag α)
    (spec' : TypeSpec Tag α) (pointer pointer' : Ptr α)
    (dataEq : hVal spec state.mem pointer = hVal spec' state'.mem pointer')
    (validEq : HeapPtrValid state.htd spec pointer ↔
      HeapPtrValid state'.htd spec' pointer') :
    simpleLift state spec pointer = simpleLift state' spec' pointer' := by
  by_cases valid : HeapPtrValid state.htd spec pointer
  · have valid' := validEq.mp valid
    simp [simpleLift, valid, valid', dataEq]
  · have valid' : ¬ HeapPtrValid state'.htd spec' pointer' := by
      exact fun holds => valid (validEq.mpr holds)
    simp [simpleLift, valid, valid']

theorem hValHeapUpdateDisjoint
    (disjoint : DisjointRanges pointerP.val specP.info.size
      pointerQ.val specQ.info.size) :
    hVal specP (heapUpdate specQ pointerQ value heap) pointerP =
      hVal specP heap pointerP := by
  unfold hVal heapUpdate
  rw [heapListUpdateDisjointSame]
  simpa [specQ.encodeLength value] using disjoint

theorem simpleHeapDifferentTypesImplDifferentPointers
    (validP : HeapPtrValid description specP pointerP)
    (validQ : HeapPtrValid description specQ pointerQ)
    (different : specP.info ≠ specQ.info) :
    pointerP.val ≠ pointerQ.val := by
  intro equal
  apply different
  have headP := validSimpleFootprintD validP.1
  have headQ := validSimpleFootprintD validQ.1
  rw [equal, headQ] at headP
  exact (HeapTypContents.heapType.inj headP).symm

theorem simpleLiftHeapUpdateOther' {α β : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (specP : TypeSpec Tag α) (pointer : Ptr α)
    (value : α) (specQ : TypeSpec Tag β)
    {oldValue : α}
    (lifted : simpleLift state specP pointer = some oldValue)
    (different : specQ.info ≠ specP.info) :
    simpleLift (memUpdate (heapUpdate specP pointer value) state) specQ =
      simpleLift state specQ :=
  simpleLiftHeapUpdateOther state specP pointer value specQ
    (simpleLiftHeapPtrValid state specP pointer lifted) different

/-- Updating a subrange of one object cannot affect valid objects of another type. -/
theorem simpleLiftHeapUpdateBytesInOther {α β γ : Type v} [DecidableEq Tag]
    (state : HeapRawState Tag) (specP : TypeSpec Tag α) (pointerP : Ptr α)
    (specQ : TypeSpec Tag β) (specW : TypeSpec Tag γ) (pointerW : Ptr γ)
    (value : γ)
    {oldValue : α}
    (lifted : simpleLift state specP pointerP = some oldValue)
    (different : specP.info ≠ specQ.info)
    (contained : ∀ address, ByteRange pointerW.val specW.info.size address →
      ByteRange pointerP.val specP.info.size address) :
    simpleLift (memUpdate (heapUpdate specW pointerW value) state) specQ =
      simpleLift state specQ := by
  funext query
  by_cases validQ : HeapPtrValid state.htd specQ query
  · have validP := simpleLiftHeapPtrValid state specP pointerP lifted
    have outerDisjoint := heapPtrValidTypeNeqDisjoint validP validQ different
    have disjoint : DisjointRanges query.val specQ.info.size
        pointerW.val specW.info.size := by
      intro address inQ inW
      exact outerDisjoint address (contained address inW) inQ
    simp [simpleLift, memUpdate, validQ]
    exact hValHeapUpdateDisjoint disjoint
  · simp [simpleLift, memUpdate, validQ]

/-! ## Semantic regression pins -/

private def pinInfo : TypeInfo String := ⟨"u16", 2⟩

private def pinSpec : TypeSpec String (UInt8 × UInt8) where
  info := pinInfo
  guard := fun address => decide (address ≠ 0)
  encode := fun value => [value.1, value.2]
  decode := fun bytes => (bytes[0]?.getD 0, bytes[1]?.getD 0)
  sizePositive := by decide
  encodeLength := by intro value; simp [pinInfo]
  decodeEncode := by intro value; simp

private def pinDescription : HeapTypDesc String :=
  ptrRetype 4 pinInfo (ptrRetype 8 pinInfo fun _ => .heapEmpty)

private def pinState : HeapRawState String where
  mem := fun address =>
    if address = 4 then 10
    else if address = 5 then 20
    else if address = 8 then 50
    else if address = 9 then 60
    else 0
  htd := pinDescription

/-- Retyping commits a genuine two-byte head/footprint layout. -/
theorem retypeLawPin :
    heapTypeTag pinDescription 4 = .heapType pinInfo ∧
      heapTypeTag pinDescription 5 = .heapFootprint := by
  constructor
  · exact heapTypeTagPtrRetype (Tag := String)
  · exact heapTypeTagPtrRetypeRest (Tag := String) (offset := 1)
      (by decide) (by decide)

/-- The concrete codec and valid footprint lift both bytes, not a fixed result. -/
theorem simpleLiftLawPin :
    simpleLift (Tag := String) pinState pinSpec ⟨4⟩ = some (10, 20) := by
  native_decide

/-- A typed write changes its own lift and leaves a disjoint typed lift untouched. -/
theorem updateLawPin :
    simpleLift (Tag := String)
      (memUpdate (heapUpdate pinSpec ⟨4⟩ (30, 40)) pinState)
      pinSpec ⟨4⟩ = some (30, 40) ∧
    simpleLift (Tag := String)
      (memUpdate (heapUpdate pinSpec ⟨4⟩ (30, 40)) pinState)
      pinSpec ⟨8⟩ = some (50, 60) := by
  native_decide

end Zag.Lang.AutoCorres.TypHeapSimple
