import Lib.Peano.Eval

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

end Heap

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

/-- `State(a)`: what a heap-transforming computation leaves behind -- the heap it produced
  together with the value it returned.

  The effect is declared once, parametrically, as an ordinary arity-1 primitive, and the payload
  is a type *argument*. There is no `StateNat`/`StateBool`/`StatePtr` triplet to keep in step,
  and a program returning a new payload type needs neither a new primitive nor new operators.

  It is deliberately the *result* of a computation rather than `Heap -> Heap x a`: a block
  sequences its effects through its instruction list, so the block itself is the `do` block.
  `pure` and `bind` would need a lambda to write a continuation, and blocks have no lambda --
  see `Test/Monad.lean` for a context whose monad is written that way instead. -/
def statePrim : Primitive where
  name := "State"
  arity := 1
  type := fun
    | [payload] => Heap × payload
    | _ => Empty
  repr := fun _ => none

abbrev heapCtx : PrimitiveCtx := .ofPrims [
  .of "Nat" Nat,
  .of "Bool" Bool,
  .of "Ptr" Ptr,
  .of "Heap" Heap,
  .of "Array" HeapArray,
  statePrim
]

instance : Peano.Types heapCtx where
  natType := by rfl
  boolType := by rfl

abbrev NatTy : Ty := Peano.NatTy
abbrev BoolTy : Ty := Peano.BoolTy
abbrev PtrTy : Ty := .prim "Ptr" []
abbrev HeapTy : Ty := .prim "Heap" []
abbrev ArrayTy : Ty := .prim "Array" []
abbrev StateTy (payload : Ty) : Ty := .prim "State" [payload]

def ofPtr (ptr : Ptr) : Ty.type heapCtx PtrTy :=
  PrimitiveCtx.toPrimitiveValue heapCtx "Ptr" ptr (by rfl)

def toPtr (raw : Ty.type heapCtx PtrTy) : Ptr :=
  cast (Ty.type_ground (primCtx := heapCtx) (name := "Ptr") (type := Ptr) (by rfl)) raw

def ofHeap (heap : Heap) : Ty.type heapCtx HeapTy :=
  PrimitiveCtx.toPrimitiveValue heapCtx "Heap" heap (by rfl)

def toHeap (raw : Ty.type heapCtx HeapTy) : Heap :=
  cast (Ty.type_ground (primCtx := heapCtx) (name := "Heap") (type := Heap) (by rfl)) raw

def ofArray (xs : HeapArray) : Ty.type heapCtx ArrayTy :=
  PrimitiveCtx.toPrimitiveValue heapCtx "Array" xs (by rfl)

def toArray (raw : Ty.type heapCtx ArrayTy) : HeapArray :=
  cast (Ty.type_ground (primCtx := heapCtx) (name := "Array") (type := HeapArray) (by rfl)) raw

theorem type_state (payload : Ty) :
    Ty.type heapCtx (StateTy payload) = (Heap × Ty.type heapCtx payload) := by
  rw [Ty.type_prim_of_find (primitive := statePrim) [payload] rfl, Ty.types_cons, Ty.types_nil]
  rfl

def ofState (payload : Ty) (state : Heap × Ty.type heapCtx payload) :
    Ty.type heapCtx (StateTy payload) :=
  cast (type_state payload).symm state

def toState (payload : Ty) (raw : Ty.type heapCtx (StateTy payload)) :
    Heap × Ty.type heapCtx payload :=
  cast (type_state payload) raw

@[simp] theorem toState_ofState (payload : Ty) (state : Heap × Ty.type heapCtx payload) :
    toState payload (ofState payload state) = state := by
  simp [toState, ofState]

def valPtr (ptr : Ptr) : Val heapCtx :=
  .mk PtrTy (ofPtr ptr)

def valHeap (heap : Heap) : Val heapCtx :=
  .mk HeapTy (ofHeap heap)

def valArray (xs : HeapArray) : Val heapCtx :=
  .mk ArrayTy (ofArray xs)

def valState (payload : Ty) (state : Heap × Ty.type heapCtx payload) : Val heapCtx :=
  .mk (StateTy payload) (ofState payload state)

def asPtr? (value : Val heapCtx) : Option Ptr := do
  let raw ← value.as? PtrTy
  some (toPtr raw)

def asHeap? (value : Val heapCtx) : Option Heap := do
  let raw ← value.as? HeapTy
  some (toHeap raw)

def asArray? (value : Val heapCtx) : Option HeapArray := do
  let raw ← value.as? ArrayTy
  some (toArray raw)

def asState? (payload : Ty) (value : Val heapCtx) :
    Option (Heap × Ty.type heapCtx payload) := do
  let raw ← value.as? (StateTy payload)
  some (toState payload raw)

def termPtr (addr : Nat) : Term heapCtx :=
  .prim PtrTy (ofPtr ⟨addr⟩)

def termHeap (heap : Heap) : Term heapCtx :=
  .prim HeapTy (ofHeap heap)

def termArray (xs : HeapArray) : Term heapCtx :=
  .prim ArrayTy (ofArray xs)

def unaryNatOp (f : Nat → Nat) : Op heapCtx :=
  Op.ofVals [NatTy] NatTy fun
  | [value] => do
      let n ← value.asNat?
      some (Val.nat (f n))
  | _ => none

def binaryNatOp (f : Nat → Nat → Nat) : Op heapCtx :=
  Op.ofVals [NatTy, NatTy] NatTy fun
  | [lhs, rhs] => do
      let a ← lhs.asNat?
      let b ← rhs.asNat?
      some (Val.nat (f a b))
  | _ => none

def binaryNatBoolOp (f : Nat → Nat → Bool) : Op heapCtx :=
  Op.ofVals [NatTy, NatTy] BoolTy fun
  | [lhs, rhs] => do
      let a ← lhs.asNat?
      let b ← rhs.asNat?
      some (Val.bool (f a b))
  | _ => none

def loadOp : Op heapCtx :=
  Op.ofVals [HeapTy, PtrTy] NatTy fun
  | [heapVal, ptrVal] => do
      let heap ← asHeap? heapVal
      let ptr ← asPtr? ptrVal
      some (Val.nat (Heap.read heap ptr))
  | _ => none

def storeOp : Op heapCtx :=
  Op.ofVals [HeapTy, PtrTy, NatTy] HeapTy fun
  | [heapVal, ptrVal, valueVal] => do
      let heap ← asHeap? heapVal
      let ptr ← asPtr? ptrVal
      let value ← valueVal.asNat?
      some (valHeap (Heap.write heap ptr value))
  | _ => none

def allocPtrOp : Op heapCtx :=
  Op.ofVals [HeapTy, NatTy] PtrTy fun
  | [heapVal, _sizeVal] => do
      let heap ← asHeap? heapVal
      some (valPtr (Heap.allocPtr heap))
  | _ => none

def allocHeapOp : Op heapCtx :=
  Op.ofVals [HeapTy, NatTy] HeapTy fun
  | [heapVal, sizeVal] => do
      let heap ← asHeap? heapVal
      let size ← sizeVal.asNat?
      some (valHeap (Heap.allocHeap heap size))
  | _ => none

def freeHeapOp : Op heapCtx :=
  Op.ofVals [HeapTy, PtrTy, NatTy] HeapTy fun
  | [heapVal, ptrVal, sizeVal] => do
      let heap ← asHeap? heapVal
      let ptr ← asPtr? ptrVal
      let size ← sizeVal.asNat?
      some (valHeap (Heap.free heap ptr size))
  | _ => none

def ptrAddOp : Op heapCtx :=
  Op.ofVals [PtrTy, NatTy] PtrTy fun
  | [ptrVal, offsetVal] => do
      let ptr ← asPtr? ptrVal
      let offset ← offsetVal.asNat?
      some (valPtr ⟨ptr.addr + offset⟩)
  | _ => none

def ptrAddrOp : Op heapCtx :=
  Op.ofVals [PtrTy] NatTy fun
  | [ptrVal] => do
      let ptr ← asPtr? ptrVal
      some (Val.nat ptr.addr)
  | _ => none

def ptrOfNatOp : Op heapCtx :=
  Op.ofVals [NatTy] PtrTy fun
  | [addrVal] => do
      let addr ← addrVal.asNat?
      some (valPtr ⟨addr⟩)
  | _ => none

def ptrEqOp : Op heapCtx :=
  Op.ofVals [PtrTy, PtrTy] BoolTy fun
  | [lhsVal, rhsVal] => do
      let lhs ← asPtr? lhsVal
      let rhs ← asPtr? rhsVal
      some (Val.bool (decide (lhs = rhs)))
  | _ => none

def ptrIsNullOp : Op heapCtx :=
  Op.ofVals [PtrTy] BoolTy fun
  | [ptrVal] => do
      let ptr ← asPtr? ptrVal
      some (Val.bool (decide (ptr = null)))
  | _ => none

def arrayGetOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy] NatTy fun
  | [xsVal, idxVal] => do
      let xs ← asArray? xsVal
      let idx ← idxVal.asNat?
      some (Val.nat (HeapArray.get xs idx))
  | _ => none

def arraySetOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, idxVal, valueVal] => do
      let xs ← asArray? xsVal
      let idx ← idxVal.asNat?
      let value ← valueVal.asNat?
      some (valArray (HeapArray.set xs idx value))
  | _ => none

def arraySwapOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, iVal, jVal] => do
      let xs ← asArray? xsVal
      let i ← iVal.asNat?
      let j ← jVal.asNat?
      some (valArray (HeapArray.swap xs i j))
  | _ => none

def arrayLenOp : Op heapCtx :=
  Op.ofVals [ArrayTy] NatTy fun
  | [xsVal] => do
      let xs ← asArray? xsVal
      some (Val.nat xs.length)
  | _ => none

def arrayCopyOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, dstVal, srcVal, lenVal] => do
      let xs ← asArray? xsVal
      let dst ← dstVal.asNat?
      let src ← srcVal.asNat?
      let len ← lenVal.asNat?
      some (valArray (HeapArray.copy xs dst src len))
  | _ => none

def arrayFillOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy, NatTy, NatTy] ArrayTy fun
  | [xsVal, startVal, lenVal, valueVal] => do
      let xs ← asArray? xsVal
      let start ← startVal.asNat?
      let len ← lenVal.asNat?
      let value ← valueVal.asNat?
      some (valArray (HeapArray.fill xs start len value))
  | _ => none

def arraySortOp : Op heapCtx :=
  Op.ofVals [ArrayTy] ArrayTy fun
  | [xsVal] => do
      let xs ← asArray? xsVal
      some (valArray (HeapArray.sort xs))
  | _ => none

def arrayInsertSortedOp : Op heapCtx :=
  Op.ofVals [ArrayTy, NatTy] ArrayTy fun
  | [xsVal, valueVal] => do
      let xs ← asArray? xsVal
      let value ← valueVal.asNat?
      some (valArray (HeapArray.insertSorted value xs))
  | _ => none

/-! ### the state operators

  Three operators, parametric in the payload, replacing one `mk`/`heap`/`value` triple per
  payload type. `Op.ofVals` cannot express them: they have no fixed signature, so their operand
  and result types are *decoded* from the type they are applied to. -/

@[simp] def stateShape? : (ty : Ty) → Option {payload : Ty // ty = StateTy payload}
| .prim "State" [payload] => some ⟨payload, rfl⟩
| _ => none

/-- Read one component out of a `State(a)`, at a result type computed from the payload. -/
def stateProjection (output : Ty → Ty)
    (run : (payload : Ty) → Heap × Ty.type heapCtx payload → Ty.type heapCtx (output payload)) :
    Op.Signature heapCtx 1 where
  Shape := Ty
  inputs payload _ := StateTy payload
  output := output
  decode tys := (stateShape? (tys 0)).map Subtype.val
  decode_inputs := by
    intro tys payload hdecode
    simp only [Option.map_eq_some_iff] at hdecode
    obtain ⟨decoded, _, rfl⟩ := hdecode
    funext idx
    have hidx : idx = 0 := Subsingleton.elim _ _
    subst hidx
    exact decoded.property.symm
  run payload args := run payload (toState payload (args 0))

def mkStateOp : Op heapCtx :=
  (Op.Signature.binary (shape := Ty) (fun _ => HeapTy) (fun payload => payload) StateTy
    (fun heapTy payloadTy =>
      if h : heapTy = HeapTy then some ⟨payloadTy, h.symm, rfl⟩ else none)
    (fun payload heap value => ofState payload (toHeap heap, value))).toOp

def stateHeapOp : Op heapCtx :=
  (stateProjection (fun _ => HeapTy) (fun _ state => ofHeap state.1)).toOp

def stateValueOp : Op heapCtx :=
  (stateProjection id (fun _ state => state.2)).toOp

def heapOpCtx : OpCtx heapCtx :=
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
    ("allocHeap", allocHeapOp),
    ("freeHeap", freeHeapOp),
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
    ("arrayInsertSorted", arrayInsertSortedOp),
    ("mkState", mkStateOp),
    ("stateHeap", stateHeapOp),
    ("stateValue", stateValueOp)
  ]

abbrev peanoHeapCtx : Ctx where
  primCtx := heapCtx
  opCtx := heapOpCtx

/-- A program: the PeanoHeap primitives and operators, plus a checked list of blocks.

  Deliberately an `abbrev`, so that `ctx.primCtx` reduces to `heapCtx`. The concretization rules
  of `Zag/Eval.lean` are indexed on the primitive context of the terms they see, and a program's
  own text is elaborated at `heapCtx`; if the two did not reduce alike, none of the rules would
  fire on a term read out of a block body. -/
abbrev mkCtx (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) : Ctx where
  primCtx := heapCtx
  opCtx := heapOpCtx
  blockCtx := { val := blocks, isValid := h }

/-- Names are unique and every `call` names a declared block. Takes the block lists to unfold:
  the program's own, plus any it is assembled from. -/
syntax (name := validBlocksTactic) "valid_blocks"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
| `(tactic| valid_blocks [$blocks,*]) =>
    `(tactic|
      refine ⟨by decide, ?_⟩ <;>
      set_option linter.unusedSimpArgs false in
        simp [$blocks,*, Zag.Block.callNames, Zag.Term.callNames, Zag.Term.nat,
          Zag.Term.bool, Zag.Term.ite, Zag.Lib.PeanoHeap.termHeap, Zag.Lib.PeanoHeap.termPtr,
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

end Lib.PeanoHeap

end Zag
