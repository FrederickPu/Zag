import HeapAlgebra.Defs
import Lib.PeanoHeap

namespace HeapAlgebra.Peano

open Zag.Lib.PeanoHeap

abbrev Region := Set Nat

structure OwnedPtr where
  base : Ptr
  extent : Nat
  extent_pos : 0 < extent

abbrev Request := {size : Nat // 0 < size}

def OwnedPtr.span (p : OwnedPtr) : Region :=
  Set.Ico p.base.addr (p.base.addr + p.extent)

def changed (h h' : Heap) : Region :=
  {addr | Heap.read h ⟨addr⟩ ≠ Heap.read h' ⟨addr⟩}

theorem Heap.read_write_same (h : Heap) (p : Ptr) (value : Nat) :
    Heap.read (Heap.write h p value) p = value := by
  simp [Heap.read, Heap.write]

theorem Heap.read_write_of_ne (h : Heap) (p q : Ptr) (value : Nat)
    (hne : q.addr ≠ p.addr) :
    Heap.read (Heap.write h p value) q = Heap.read h q := by
  simp [Heap.read, Heap.write, Ne.symm hne]

theorem Heap.read_allocHeap_of_not_mem (h : Heap) (size addr : Nat)
    (hout : addr ∉ Set.Ico h.next (h.next + size)) :
    Heap.read (Heap.allocHeap h size) ⟨addr⟩ = Heap.read h ⟨addr⟩ := by
  have hz : List.find? (fun cell => cell.1 = addr) (Heap.zeroCells h.next size) = none := by
    rw [List.find?_eq_none]
    intro cell hcell hfound
    rw [Heap.zeroCells, List.mem_map] at hcell
    obtain ⟨offset, hoffset, rfl⟩ := hcell
    have hlt : offset < size := List.mem_range.mp hoffset
    simp only [decide_eq_true_eq] at hfound
    subst addr
    apply hout
    simpa only [Set.mem_Ico] using
      (show h.next ≤ h.next + offset ∧ h.next + offset < h.next + size by omega)
  simp [Heap.read, Heap.allocHeap, List.find?_append, hz]

instance : _root_.HeapAlgebra Heap OwnedPtr Region (fun _ => Nat) where
  span := OwnedPtr.span
  changed := changed
  load h p := Heap.read h p.base
  store p value h := Heap.write h p.base value

instance : LawfulHeapAlgebra Heap OwnedPtr Region (fun _ => Nat) where
  changed_rfl h := by
    ext addr
    change (Heap.read h ⟨addr⟩ ≠ Heap.read h ⟨addr⟩) ↔ addr ∈ (∅ : Set Nat)
    simp
  changed_symm h h' := by
    ext addr
    change (Heap.read h ⟨addr⟩ ≠ Heap.read h' ⟨addr⟩) ↔
      Heap.read h' ⟨addr⟩ ≠ Heap.read h ⟨addr⟩
    exact ne_comm
  changed_triangle h₁ h₂ h₃ := by
    intro addr hne
    change Heap.read h₁ ⟨addr⟩ ≠ Heap.read h₃ ⟨addr⟩ at hne
    change Heap.read h₁ ⟨addr⟩ ≠ Heap.read h₂ ⟨addr⟩ ∨
      Heap.read h₂ ⟨addr⟩ ≠ Heap.read h₃ ⟨addr⟩
    by_contra hcon
    simp only [not_or, not_not] at hcon
    exact hne (hcon.1.trans hcon.2)
  store_writes_only p value h := by
    intro addr hchanged
    change Heap.read h ⟨addr⟩ ≠ Heap.read (Heap.write h p.base value) ⟨addr⟩ at hchanged
    have heq : addr = p.base.addr := by
      by_contra hne
      exact hchanged (Heap.read_write_of_ne h p.base ⟨addr⟩ value hne).symm
    subst addr
    exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right p.extent_pos⟩
  load_after_store p value h := Heap.read_write_same h p.base value
  store_no_alias p q value h hpq := by
    have hp : p.base.addr ∈ p.span := by simp [OwnedPtr.span, p.extent_pos]
    have hq : q.base.addr ∈ q.span := by simp [OwnedPtr.span, q.extent_pos]
    have hne : q.base.addr ≠ p.base.addr := by
      intro heq
      exact Set.disjoint_left.1 hpq hp (heq ▸ hq)
    exact Heap.read_write_of_ne h p.base q.base value hne
  load_unchanged p h h' hd := by
    have hp : p.base.addr ∈ p.span := by simp [OwnedPtr.span, p.extent_pos]
    by_contra hne
    exact Set.disjoint_left.1 hd hne hp

def allocatorValid (owned : Region) (h : Heap) : Prop :=
  owned ⊆ Set.Iio h.next

def allocate (request : Request) (owned : Region) (h : Heap) :
    OwnedPtr × Region × Heap :=
  let p : OwnedPtr := ⟨Heap.allocPtr h, request, request.property⟩
  (p, owned ⊔ p.span, Heap.allocHeap h request)

theorem allocate_fresh (request : Request) (owned : Region) (h : Heap)
    (hvalid : allocatorValid owned h) :
    let (p, owned', _) := allocate request owned h
    noOverlap owned p.span ∧ owned' = owned ⊔ p.span := by
  dsimp [allocate]
  refine ⟨Set.disjoint_left.2 ?_, rfl⟩
  intro addr howned hnew
  have hold : addr < h.next := hvalid howned
  exact (Nat.not_le_of_gt hold) hnew.1

theorem allocate_valid (request : Request) (owned : Region) (h : Heap)
    (hvalid : allocatorValid owned h) :
    let (_, owned', h') := allocate request owned h
    allocatorValid owned' h' := by
  intro addr haddr
  rcases haddr with haddr | haddr
  · have hold : addr < h.next := hvalid haddr
    change addr < h.next + request
    omega
  · exact haddr.2

theorem allocate_writes (request : Request) (owned : Region) (h : Heap) :
    let (p, _, h') := allocate request owned h
    _root_.HeapAlgebra.changed (Ptr := OwnedPtr) (Region := Region)
        (Value := fun _ => Nat) h h' ≤ p.span := by
  intro addr hchanged
  by_contra hout
  apply hchanged
  exact (Heap.read_allocHeap_of_not_mem h request addr hout).symm

instance : Allocator Heap OwnedPtr Region (fun _ => Nat) Request where
  valid := allocatorValid
  alloc := allocate
  alloc_fresh := allocate_fresh
  alloc_valid := allocate_valid
  alloc_writes := allocate_writes

@[simp] theorem readPtr_run (p : OwnedPtr) (h : Heap) :
    (_root_.readPtr (Region := Region) (Value := fun _ : OwnedPtr => Nat) p :
      StateM Heap Nat).run h = (Heap.read h p.base, h) := by
  rfl

@[simp] theorem writePtr_run (p : OwnedPtr) (value : Nat) (h : Heap) :
    (_root_.writePtr (Region := Region) (Value := fun _ : OwnedPtr => Nat) p value :
      StateM Heap PUnit).run h = (PUnit.unit, Heap.write h p.base value) := by
  rfl

end HeapAlgebra.Peano
