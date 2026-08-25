import HeapAlgebra.Peano

namespace Zag.Test.PeanoHeapAlgebra

open Zag.Lib.PeanoHeap
open HeapAlgebra.Peano

#synth _root_.HeapAlgebra Heap OwnedPtr Region (fun _ => Nat)
#synth LawfulHeapAlgebra Heap OwnedPtr Region (fun _ => Nat)
#synth Allocator Heap OwnedPtr Region (fun _ => Nat) Request

private def block : OwnedPtr := ⟨⟨4⟩, 3, by omega⟩
private def requestOne : Request := ⟨1, by omega⟩
private def requestTwo : Request := ⟨2, by omega⟩

example : block.span = ({4, 5, 6} : Set Nat) := by
  ext addr
  change (4 ≤ addr ∧ addr < 4 + 3) ↔ addr = 4 ∨ addr = 5 ∨ addr = 6
  omega

example (h : Heap) :
    (_root_.readPtr (Region := Region) (Value := fun _ : OwnedPtr => Nat) block :
      StateM Heap Nat).run h = (Zag.Lib.PeanoHeap.load block.base).run h := by
  rfl

example (h : Heap) (value : Nat) :
    (_root_.writePtr (Region := Region) (Value := fun _ : OwnedPtr => Nat) block value :
      StateM Heap PUnit).run h = (Zag.Lib.PeanoHeap.store block.base value).run h := by
  rfl

private def duplicateHeap : Heap :=
  { next := 7, cells := [(4, 11), (4, 9), (5, 13)] }

example :
    _root_.HeapAlgebra.load (Region := Region) (Value := fun _ : OwnedPtr => Nat)
      duplicateHeap block = 11 := by
  decide

example :
    _root_.HeapAlgebra.load (Region := Region) (Value := fun _ : OwnedPtr => Nat)
      (_root_.HeapAlgebra.store (Region := Region) (Value := fun _ : OwnedPtr => Nat)
        block 17 duplicateHeap) block = 17 := by
  exact LawfulHeapAlgebra.load_after_store (Region := Region)
    (Value := fun _ : OwnedPtr => Nat) block 17 duplicateHeap

private def firstAllocation : OwnedPtr × Region × Heap :=
  allocate requestTwo ∅ Heap.empty

example : firstAllocation.1.base = Heap.allocPtr Heap.empty := rfl
example : firstAllocation.1.extent = 2 := rfl
example : firstAllocation.2.2 = Heap.allocHeap Heap.empty 2 := rfl

example : firstAllocation.2.1 = Set.Ico 1 3 := by
  simp [firstAllocation, allocate, requestTwo, OwnedPtr.span, Heap.empty, Heap.allocPtr]

private theorem firstAllocation_valid :
    allocatorValid firstAllocation.2.1 firstAllocation.2.2 := by
  apply allocate_valid requestTwo ∅ Heap.empty
  simp [allocatorValid]

private def secondAllocation : OwnedPtr × Region × Heap :=
  allocate requestOne firstAllocation.2.1 firstAllocation.2.2

example : firstAllocation.1.base.addr = 1 := rfl
example : secondAllocation.1.base.addr = 3 := rfl

example : Disjoint firstAllocation.1.span secondAllocation.1.span := by
  simpa [firstAllocation, secondAllocation, allocate] using
    (allocate_fresh requestOne firstAllocation.2.1 firstAllocation.2.2
      firstAllocation_valid).1

example :
    HeapAlgebra.Peano.changed { next := 1, cells := [] } { next := 9, cells := [] } = ∅ := by
  ext addr
  simp [HeapAlgebra.Peano.changed, Heap.read]

example :
    HeapAlgebra.Peano.changed { next := 2, cells := [(1, 7), (1, 9)] }
      { next := 2, cells := [(1, 7)] } = ∅ := by
  ext addr
  by_cases haddr : addr = 1
  · subst addr
    simp [HeapAlgebra.Peano.changed, Heap.read]
  · simp [HeapAlgebra.Peano.changed, Heap.read, Ne.symm haddr]

example : 1 ∉ HeapAlgebra.Peano.changed Heap.empty (Heap.allocHeap Heap.empty 2) := by
  change ¬Heap.read Heap.empty ⟨1⟩ ≠ Heap.read (Heap.allocHeap Heap.empty 2) ⟨1⟩
  decide

private def futureWrite : Heap :=
  Heap.write Heap.empty ⟨1⟩ 7

example : 1 ∈ HeapAlgebra.Peano.changed futureWrite (Heap.allocHeap futureWrite 1) := by
  change Heap.read futureWrite ⟨1⟩ ≠ Heap.read (Heap.allocHeap futureWrite 1) ⟨1⟩
  decide

example : 2 ∉ HeapAlgebra.Peano.changed futureWrite (Heap.allocHeap futureWrite 1) := by
  change ¬Heap.read futureWrite ⟨2⟩ ≠ Heap.read (Heap.allocHeap futureWrite 1) ⟨2⟩
  decide

example :
    _root_.HeapAlgebra.changed (Ptr := OwnedPtr) (Region := Region)
      (Value := fun _ => Nat) futureWrite (Heap.allocHeap futureWrite 1) ≤ Set.Ico 1 2 := by
  simpa [allocate, requestOne, OwnedPtr.span, futureWrite, Heap.empty, Heap.write,
    Heap.allocPtr] using
    (allocate_writes requestOne ∅ futureWrite)

example (h : Heap) : Heap.allocHeap h 0 = h := by
  simp [Heap.allocHeap, Heap.zeroCells]

example (h : Heap) : Heap.allocPtr (Heap.allocHeap h 0) = Heap.allocPtr h := by
  simp [Heap.allocHeap, Heap.allocPtr, Heap.zeroCells]

example : ¬∃ request : Request, request.1 = 0 := by
  intro hexists
  obtain ⟨request, hzero⟩ := hexists
  exact Nat.ne_of_gt request.property hzero

example :
    ¬Disjoint ({Heap.empty.next} : Set Nat)
      (OwnedPtr.span ⟨Heap.allocPtr Heap.empty, 1, by omega⟩) := by
  simp [OwnedPtr.span, Heap.empty, Heap.allocPtr]

end Zag.Test.PeanoHeapAlgebra
