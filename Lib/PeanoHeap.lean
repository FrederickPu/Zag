import Lib.Peano.Eval
import Std.Tactic.Do

namespace Zag

namespace Lib.PeanoHeap

structure Ptr where
  addr : Nat
deriving Repr, DecidableEq

abbrev null : Ptr := ⟨0⟩

structure Heap where
  next : Nat
  cells : List (Nat × Nat)
deriving Repr, DecidableEq

abbrev HeapArray := List Nat

namespace Heap

def empty : Heap := { next := 1, cells := [] }

def read (heap : Heap) (ptr : Ptr) : Nat :=
  ((heap.cells.find? (fun cell => cell.1 = ptr.addr)).map Prod.snd).getD 0

def write (heap : Heap) (ptr : Ptr) (value : Nat) : Heap :=
  { heap with cells := (ptr.addr, value) :: heap.cells }

def zeroCells (start size : Nat) : List (Nat × Nat) :=
  (List.range size).map fun offset => (start + offset, 0)

def allocPtr (heap : Heap) : Ptr :=
  ⟨heap.next⟩

def allocHeap (heap : Heap) (size : Nat) : Heap :=
  { next := heap.next + size, cells := zeroCells heap.next size ++ heap.cells }

def free (heap : Heap) (_ptr : Ptr) (_size : Nat) : Heap :=
  heap

def copy : Heap → Ptr → Ptr → Nat → Heap
| heap, _, _, 0 => heap
| heap, dst, src, len + 1 =>
    copy (write heap dst (read heap src)) ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ len

def fill : Heap → Ptr → Nat → Nat → Heap
| heap, _, _, 0 => heap
| heap, start, value, len + 1 =>
    fill (write heap start value) ⟨start.addr + 1⟩ value len

end Heap

/-! ### Ambient heap actions -/

def load (ptr : Ptr) : StateM Heap Nat :=
  modifyGet fun heap => (Heap.read heap ptr, heap)

def store (ptr : Ptr) (value : Nat) : StateM Heap PUnit :=
  modifyGet fun heap => (⟨⟩, Heap.write heap ptr value)

def alloc (size : Nat) : StateM Heap Ptr :=
  modifyGet fun heap => (Heap.allocPtr heap, Heap.allocHeap heap size)

def free (ptr : Ptr) (size : Nat) : StateM Heap PUnit :=
  modifyGet fun heap => (⟨⟩, Heap.free heap ptr size)

def memcpy (dst src : Ptr) (len : Nat) : StateM Heap Ptr :=
  modifyGet fun heap => (dst, Heap.copy heap dst src len)

def memset (start : Ptr) (value len : Nat) : StateM Heap Ptr :=
  modifyGet fun heap => (start, Heap.fill heap start (value % 256) len)

@[zspec] theorem load_spec (ptr : Ptr) (Q : Std.Do.PostCond Nat (.arg Heap .pure)) :
    Std.Do.Triple (load ptr) (fun heap => Q.1 (Heap.read heap ptr) heap) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, load, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem store_spec (ptr : Ptr) (value : Nat)
    (Q : Std.Do.PostCond PUnit (.arg Heap .pure)) :
    Std.Do.Triple (store ptr value)
      (fun heap => Q.1 ⟨⟩ (Heap.write heap ptr value)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, store, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem alloc_spec (size : Nat) (Q : Std.Do.PostCond Ptr (.arg Heap .pure)) :
    Std.Do.Triple (alloc size)
      (fun heap => Q.1 (Heap.allocPtr heap) (Heap.allocHeap heap size)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, alloc, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem free_spec (ptr : Ptr) (size : Nat)
    (Q : Std.Do.PostCond PUnit (.arg Heap .pure)) :
    Std.Do.Triple (free ptr size)
      (fun heap => Q.1 ⟨⟩ (Heap.free heap ptr size)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, free, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem memcpy_spec (dst src : Ptr) (len : Nat)
    (Q : Std.Do.PostCond Ptr (.arg Heap .pure)) :
    Std.Do.Triple (memcpy dst src len)
      (fun heap => Q.1 dst (Heap.copy heap dst src len)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, memcpy, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem memset_spec (start : Ptr) (value len : Nat)
    (Q : Std.Do.PostCond Ptr (.arg Heap .pure)) :
    Std.Do.Triple (memset start value len)
      (fun heap => Q.1 start (Heap.fill heap start (value % 256) len)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, memset, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

namespace HeapArray

def get (xs : HeapArray) (idx : Nat) : Nat :=
  xs[idx]?.getD 0

def set : HeapArray → Nat → Nat → HeapArray
| [], _, _ => []
| _ :: xs, 0, value => value :: xs
| x :: xs, idx + 1, value => x :: set xs idx value

def swap (xs : HeapArray) (i j : Nat) : HeapArray :=
  let vi := get xs i
  let vj := get xs j
  set (set xs i vj) j vi

def fill : HeapArray → Nat → Nat → Nat → HeapArray
| xs, _, 0, _ => xs
| xs, start, len + 1, value => fill (set xs start value) (start + 1) len value

def copy : HeapArray → Nat → Nat → Nat → HeapArray
| xs, _, _, 0 => xs
| xs, dst, src, len + 1 =>
    copy (set xs dst (get xs src)) (dst + 1) (src + 1) len

def insertSorted (value : Nat) : HeapArray → HeapArray
| [] => [value]
| x :: xs => if value ≤ x then value :: x :: xs else x :: insertSorted value xs

def sort : HeapArray → HeapArray
| [] => []
| x :: xs => insertSorted x (sort xs)

end HeapArray

def parseDigit (code : Nat) : Nat :=
  code - 48

def isDigit (code : Nat) : Bool :=
  decide (48 ≤ code ∧ code ≤ 57)

def bitAnd : Nat → Nat → Nat
| 0, _ => 0
| _, 0 => 0
| a + 1, b + 1 =>
    let low := ((a + 1) % 2) * ((b + 1) % 2)
    low + 2 * bitAnd ((a + 1) / 2) ((b + 1) / 2)
termination_by a b => a + b
decreasing_by all_goals omega

def bitOr : Nat → Nat → Nat
| 0, b => b
| a, 0 => a
| a + 1, b + 1 =>
    let low := if (a + 1) % 2 = 0 ∧ (b + 1) % 2 = 0 then 0 else 1
    low + 2 * bitOr ((a + 1) / 2) ((b + 1) / 2)
termination_by a b => a + b
decreasing_by all_goals omega

def bitXor : Nat → Nat → Nat
| 0, b => b
| a, 0 => a
| a + 1, b + 1 =>
    let low := if (a + 1) % 2 = (b + 1) % 2 then 0 else 1
    low + 2 * bitXor ((a + 1) / 2) ((b + 1) / 2)
termination_by a b => a + b
decreasing_by all_goals omega

def pow2 (shift : Nat) : Nat :=
  2 ^ shift

/-- A genuine unary array primitive. The element type is interpreted from its type argument. -/
def arrayPrim : Primitive where
  name := "Array"
  arity := 1
  type := fun
    | [element] => List element
    | _ => Empty
  repr := fun _ => none

def heapCtx : PrimitiveCtx := .ofPrims [
  .of "Nat" Nat,
  .of "Bool" Bool,
  .of "Unit" PUnit,
  .of "Ptr" Ptr,
  arrayPrim
]

instance : Peano.Types heapCtx where
  natType := by rfl
  boolType := by rfl

abbrev NatTy : Ty := Peano.NatTy
abbrev BoolTy : Ty := Peano.BoolTy
abbrev UnitTy : Ty := .prim "Unit" []
abbrev PtrTy : Ty := .prim "Ptr" []
abbrev ArrayTy : Ty := .prim "Array" [NatTy]

def ofPtr (ptr : Ptr) : Ty.type heapCtx PtrTy :=
  PrimitiveCtx.toPrimitiveValue heapCtx "Ptr" ptr (by rfl)

def toPtr (raw : Ty.type heapCtx PtrTy) : Ptr :=
  cast (Ty.type_ground (primCtx := heapCtx) (name := "Ptr") (type := Ptr) (by rfl)) raw

@[simp] theorem toPtr_ofPtr (ptr : Ptr) : toPtr (ofPtr ptr) = ptr := by
  unfold toPtr ofPtr PrimitiveCtx.toPrimitiveValue
  rw [cast_cast]
  simp

theorem type_array : Ty.type heapCtx ArrayTy = List Nat := by
  rw [Ty.type_prim_of_find (primitive := arrayPrim) [NatTy] rfl, Ty.types_cons, Ty.types_nil]
  change List (Ty.type heapCtx NatTy) = List Nat
  rw [Ty.type_ground (Peano.Types.natType (primCtx := heapCtx))]

def ofArray (xs : HeapArray) : Ty.type heapCtx ArrayTy :=
  cast type_array.symm xs

def toArray (raw : Ty.type heapCtx ArrayTy) : HeapArray :=
  cast type_array raw

def valUnit : Val heapCtx :=
  .mk UnitTy (PrimitiveCtx.toPrimitiveValue heapCtx "Unit" PUnit.unit (by rfl))

def valPtr (ptr : Ptr) : Val heapCtx :=
  .mk PtrTy (ofPtr ptr)

def valArray (xs : HeapArray) : Val heapCtx :=
  .mk ArrayTy (ofArray xs)

def asPtr? (value : Val heapCtx) : Option Ptr := do
  let raw ← value.as? PtrTy
  some (toPtr raw)

def asArray? (value : Val heapCtx) : Option HeapArray := do
  let raw ← value.as? ArrayTy
  some (toArray raw)

def termUnit : Term heapCtx :=
  .prim UnitTy (PrimitiveCtx.toPrimitiveValue heapCtx "Unit" PUnit.unit (by rfl))

def termPtr (addr : Nat) : Term heapCtx :=
  .prim PtrTy (ofPtr ⟨addr⟩)

def termArray (xs : HeapArray) : Term heapCtx :=
  .prim ArrayTy (ofArray xs)

def unaryNatOp {M : Type → Type} (f : Nat → Nat) : Op heapCtx M :=
  Op.ofVals [NatTy] NatTy fun
  | [value] => do
      let n ← value.asNat?
      some (Val.nat (f n))
  | _ => none

def binaryNatOp {M : Type → Type} (f : Nat → Nat → Nat) : Op heapCtx M :=
  Op.ofVals [NatTy, NatTy] NatTy fun
  | [lhs, rhs] => do
      let a ← lhs.asNat?
      let b ← rhs.asNat?
      some (Val.nat (f a b))
  | _ => none

def binaryNatBoolOp {M : Type → Type} (f : Nat → Nat → Bool) : Op heapCtx M :=
  Op.ofVals [NatTy, NatTy] BoolTy fun
  | [lhs, rhs] => do
      let a ← lhs.asNat?
      let b ← rhs.asNat?
      some (Val.bool (f a b))
  | _ => none

/-- Ambient heap read. The heap is neither an operand nor part of the returned value. -/
def loadOp : Op heapCtx (StateM Heap) :=
  Op.effectful 1 (fun tys => if tys 0 = PtrTy then some NatTy else none) fun
  | [ptrVal] =>
      match asPtr? ptrVal with
      | some ptr => do
          let value ← load ptr
          pure (some (Val.nat value))
      | none => pure none
  | _ => pure none

/-- Ambient heap write with an ordinary unit result. -/
def storeOp : Op heapCtx (StateM Heap) :=
  Op.effectful 2
    (fun tys => if tys 0 = PtrTy ∧ tys 1 = NatTy then some UnitTy else none) fun
  | [ptrVal, valueVal] =>
      match asPtr? ptrVal, valueVal.asNat? with
      | some ptr, some value => do
          let _ ← store ptr value
          pure (some valUnit)
      | _, _ => pure none
  | _ => pure none

/-- Allocate and zero `size` cells, returning their first pointer. -/
def allocPtrOp : Op heapCtx (StateM Heap) :=
  Op.effectful 1 (fun tys => if tys 0 = NatTy then some PtrTy else none) fun
  | [sizeVal] =>
      match sizeVal.asNat? with
      | some size => do
          let ptr ← alloc size
          pure (some (valPtr ptr))
      | none => pure none
  | _ => pure none

/-- Free a region in the ambient heap model. `Heap.free` is currently a no-op. -/
def freeHeapOp : Op heapCtx (StateM Heap) :=
  Op.effectful 2
    (fun tys => if tys 0 = PtrTy ∧ tys 1 = NatTy then some UnitTy else none) fun
  | [ptrVal, sizeVal] => fun heap =>
      match asPtr? ptrVal, sizeVal.asNat? with
      | some ptr, some size => (some valUnit, Heap.free heap ptr size)
      | _, _ => (none, heap)
  | _ => fun heap => (none, heap)

def memcpyOp : Op heapCtx (StateM Heap) :=
  Op.effectful 3
    (fun tys => if tys 0 = PtrTy ∧ tys 1 = PtrTy ∧ tys 2 = NatTy then some PtrTy else none) fun
  | [dstVal, srcVal, lenVal] => fun heap =>
      match asPtr? dstVal, asPtr? srcVal, lenVal.asNat? with
      | some dst, some src, some len => (some (valPtr dst), Heap.copy heap dst src len)
      | _, _, _ => (none, heap)
  | _ => fun heap => (none, heap)

def memsetOp : Op heapCtx (StateM Heap) :=
  Op.effectful 3
    (fun tys => if tys 0 = PtrTy ∧ tys 1 = NatTy ∧ tys 2 = NatTy then some PtrTy else none) fun
  | [startVal, valueVal, lenVal] => fun heap =>
      match asPtr? startVal, valueVal.asNat?, lenVal.asNat? with
      | some start, some value, some len =>
          (some (valPtr start), Heap.fill heap start (value % 256) len)
      | _, _, _ => (none, heap)
  | _ => fun heap => (none, heap)

def ptrAddOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [PtrTy, NatTy] PtrTy fun
  | [ptrVal, offsetVal] => do
      let ptr ← asPtr? ptrVal
      let offset ← offsetVal.asNat?
      some (valPtr ⟨ptr.addr + offset⟩)
  | _ => none

def ptrAddrOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [PtrTy] NatTy fun
  | [ptrVal] => do
      let ptr ← asPtr? ptrVal
      some (Val.nat ptr.addr)
  | _ => none

def ptrOfNatOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [NatTy] PtrTy fun
  | [addrVal] => do
      let addr ← addrVal.asNat?
      some (valPtr ⟨addr⟩)
  | _ => none

def ptrEqOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [PtrTy, PtrTy] BoolTy fun
  | [lhsVal, rhsVal] => do
      let lhs ← asPtr? lhsVal
      let rhs ← asPtr? rhsVal
      some (Val.bool (decide (lhs = rhs)))
  | _ => none

def ptrIsNullOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [PtrTy] BoolTy fun
  | [ptrVal] => do
      let ptr ← asPtr? ptrVal
      some (Val.bool (decide (ptr = null)))
  | _ => none

def arrayGetOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy] NatTy fun
  | [xsVal, idxVal] => do
      let xs ← asArray? xsVal
      let idx ← idxVal.asNat?
      some (Val.nat (HeapArray.get xs idx))
  | _ => none

def arraySetOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, idxVal, valueVal] => do
      let xs ← asArray? xsVal
      let idx ← idxVal.asNat?
      let value ← valueVal.asNat?
      some (valArray (HeapArray.set xs idx value))
  | _ => none

def arraySwapOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, iVal, jVal] => do
      let xs ← asArray? xsVal
      let i ← iVal.asNat?
      let j ← jVal.asNat?
      some (valArray (HeapArray.swap xs i j))
  | _ => none

def arrayLenOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy] NatTy fun
  | [xsVal] => do
      let xs ← asArray? xsVal
      some (Val.nat xs.length)
  | _ => none

def arrayCopyOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, dstVal, srcVal, lenVal] => do
      let xs ← asArray? xsVal
      let dst ← dstVal.asNat?
      let src ← srcVal.asNat?
      let len ← lenVal.asNat?
      some (valArray (HeapArray.copy xs dst src len))
  | _ => none

def arrayFillOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, startVal, lenVal, valueVal] => do
      let xs ← asArray? xsVal
      let start ← startVal.asNat?
      let len ← lenVal.asNat?
      let value ← valueVal.asNat?
      some (valArray (HeapArray.fill xs start len value))
  | _ => none

def arraySortOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy] ArrayTy fun
  | [xsVal] => do
      let xs ← asArray? xsVal
      some (valArray (HeapArray.sort xs))
  | _ => none

def arrayInsertSortedOp {M : Type → Type} : Op heapCtx M :=
  Op.ofVals [ArrayTy, NatTy] ArrayTy fun
  | [xsVal, valueVal] => do
      let xs ← asArray? xsVal
      let value ← valueVal.asNat?
      some (valArray (HeapArray.insertSorted value xs))
  | _ => none

@[eval_step] def heapOpCtx : OpCtx heapCtx (StateM Heap) :=
  Peano.opCtx heapCtx ++ [
    ("mod", binaryNatOp Nat.mod),
    ("le", binaryNatBoolOp fun a b => decide (a ≤ b)),
    ("not", Op.ofVals [BoolTy] BoolTy fun
      | [value] => do
          let b ← value.asBool?
          some (Val.bool (!b))
      | _ => none),
    ("bitAnd", binaryNatOp bitAnd),
    ("bitOr", binaryNatOp bitOr),
    ("bitXor", binaryNatOp bitXor),
    ("shl", binaryNatOp fun a b => a * pow2 b),
    ("shr", binaryNatOp fun a b => a / pow2 b),
    ("isDigit", Op.ofVals [NatTy] BoolTy fun
      | [value] => do
          let code ← value.asNat?
          some (Val.bool (isDigit code))
      | _ => none),
    ("digit", unaryNatOp parseDigit),
    ("load", loadOp),
    ("store", storeOp),
    ("allocPtr", allocPtrOp),
    ("freeHeap", freeHeapOp),
    ("memcpy", memcpyOp),
    ("memset", memsetOp),
    ("ptrAdd", ptrAddOp),
    ("ptrAddr", ptrAddrOp),
    ("ptrOfNat", ptrOfNatOp),
    ("ptrEq", ptrEqOp),
    ("ptrIsNull", ptrIsNullOp),
    ("arrayGet", arrayGetOp),
    ("arraySet", arraySetOp),
    ("arraySwap", arraySwapOp),
    ("arrayLen", arrayLenOp),
    ("arrayCopy", arrayCopyOp),
    ("arrayFill", arrayFillOp),
    ("arraySort", arraySortOp),
    ("arrayInsertSorted", arrayInsertSortedOp)
  ]

@[eval_step] theorem heapOpCtx_get_add :
    heapOpCtx.get? "add" =
      some (Op.natBinary (primCtx := heapCtx) (M := StateM Heap) Nat.add) := by
  rfl

@[eval_step] theorem heapOpCtx_get_sub :
    heapOpCtx.get? "sub" =
      some (Op.natBinary (primCtx := heapCtx) (M := StateM Heap) Nat.sub) := by
  rfl

@[eval_step] theorem heapOpCtx_get_gt :
    heapOpCtx.get? "gt" =
      some (Op.compare (primCtx := heapCtx) (M := StateM Heap) Val.primGt?) := by
  rfl

@[eval_step] theorem heapOpCtx_get_while :
    heapOpCtx.get? "while" =
      some (Op.whileOp (primCtx := heapCtx) (M := StateM Heap)) := by
  rfl

@[simp] theorem heapOpCtx_get_load :
    heapOpCtx.get? "load" = some loadOp := by
  rfl

@[simp] theorem heapOpCtx_get_store :
    heapOpCtx.get? "store" = some storeOp := by
  rfl

@[simp] theorem heapOpCtx_get_allocPtr :
    heapOpCtx.get? "allocPtr" = some allocPtrOp := by
  rfl

theorem loadOp_step (blockCtx : BlockCtx heapCtx) (env : Env heapCtx)
    (stack : List (Frame heapCtx)) (heap : Heap) (ptr : Ptr) :
    Id.run ((Machine.step (Machine.stateCtx heapCtx heapOpCtx blockCtx)
      { control := .apply (.opRef "load" [] [PtrTy] NatTy)
          [Val.mk PtrTy (ofPtr ptr)], env, stack }).run heap) =
      (some { control := .ret (Val.nat (Heap.read heap ptr)), env, stack }, heap) := by
  have hop : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  set_option linter.unusedSimpArgs false in
    simp [Machine.step, Machine.applyValue, Machine.stateCtx, hop,
      loadOp, Op.effectful, load, asPtr?, valPtr, OptionT.mk, OptionT.run,
      OptionT.lift, OptionT.bind, OptionT.pure, StateT.mk, StateT.run, StateT.bind,
      StateT.instMonad, StateT.pure, StateT.map, StateT.run_bind, StateT.run_pure,
      Id.run, Id.run_bind, Id.run_pure, Pure.pure, Bind.bind, Functor.map,
      MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Option.elimM, monadLift, MonadLift.monadLift]

theorem storeOp_step (blockCtx : BlockCtx heapCtx) (env : Env heapCtx)
    (stack : List (Frame heapCtx)) (heap : Heap) (ptr : Ptr) (value : Nat) :
    Id.run ((Machine.step (Machine.stateCtx heapCtx heapOpCtx blockCtx)
      { control := .apply (.opRef "store" [] [PtrTy, NatTy] UnitTy)
          [Val.mk PtrTy (ofPtr ptr), Val.nat value], env, stack }).run heap) =
      (some { control := .ret valUnit, env, stack }, Heap.write heap ptr value) := by
  have hop : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  set_option linter.unusedSimpArgs false in
    simp [Machine.step, Machine.applyValue, Machine.stateCtx, hop,
      storeOp, Op.effectful, store, asPtr?, valPtr, valUnit, OptionT.mk, OptionT.run,
      OptionT.lift, OptionT.bind, OptionT.pure, StateT.mk, StateT.run, StateT.bind,
      StateT.instMonad, StateT.pure, StateT.map, StateT.run_bind, StateT.run_pure,
      Id.run, Id.run_bind, Id.run_pure, Pure.pure, Bind.bind, Functor.map,
      MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Option.elimM, monadLift, MonadLift.monadLift]

abbrev peanoHeapCtx : Ctx where
  primCtx := heapCtx
  M := StateM Heap
  monad := StateT.instMonad
  opCtx := heapOpCtx
  postShape := .arg Heap .pure
  wpMonad := inferInstance

/-- A heap program consists of the ambient heap operators and a checked list of blocks. -/
abbrev mkCtx (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) : Ctx where
  primCtx := heapCtx
  M := StateM Heap
  monad := StateT.instMonad
  opCtx := heapOpCtx
  blockCtx := { val := blocks, isValid := h }
  postShape := .arg Heap .pure
  wpMonad := inferInstance

abbrev checkedBlocks (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) :
    BlockCtx heapCtx :=
  { val := blocks, isValid := h }

/-- Fuel-independent effectful denotation of a heap term. -/
abbrev eval (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks)
    (env : Env heapCtx) (term : Term heapCtx)
    (P : EvalTriple.Assertion (mkCtx blocks h))
    (Q : EvalTriple.PostCond (mkCtx blocks h) (Val heapCtx)) : Prop :=
  Zag.EvaluatesTo (mkCtx blocks h) env term P Q

/-- Fuel-independent effectful call judgment. The heap remains in its generic WP assertions. -/
abbrev evalCall (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx))
    (P : EvalTriple.Assertion (mkCtx blocks h))
    (Q : EvalTriple.PostCond (mkCtx blocks h) (Val heapCtx)) : Prop :=
  Zag.EvaluatesCall (mkCtx blocks h) name args P Q

/-- The exact-state specialization is definitionally the generic total-correctness judgment. -/
theorem evalCall_relation_triple
    (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx))
    (initial final : Heap) (value : Val heapCtx)
    (hcall : EvalTriple.State.EvaluatesCall heapCtx heapOpCtx (checkedBlocks blocks h)
      name args initial value final) :
    evalCall blocks h name args
      (EvalTriple.Singleton.statePre initial)
      (EvalTriple.Singleton.statePost fun result state =>
        result = value ∧ state = final) := by
  exact hcall

/-- Names are unique and every `call` names a declared block. -/
syntax (name := validBlocksTactic) "valid_blocks"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
| `(tactic| valid_blocks [$blocks,*]) =>
    `(tactic|
      refine ⟨by decide, ?_⟩ <;>
      set_option linter.unusedSimpArgs false in
        simp [$blocks,*, Zag.Block.callNames, Zag.Term.callNames, Zag.Term.nat,
          Zag.Term.bool, Zag.Term.ite, Zag.Lib.PeanoHeap.termPtr,
          Zag.Lib.PeanoHeap.termArray])

instance : Peano.Model peanoHeapCtx where
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

instance (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) :
    Peano.Model (mkCtx blocks h) where
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

attribute [irreducible] heapCtx

end Lib.PeanoHeap

end Zag
