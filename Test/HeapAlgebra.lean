import HeapAlgebra
import Test.HeapAlgebra.Peano

open HeapAlgebra HProp Std.Do

universe u

section Abstract
variable {Heap Ptr Region : Type u} {Value : Ptr → Type u}
  [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
  [LawfulHeapAlgebra Heap Ptr Region Value]

example (p q : Ptr) (u : Value p) (v : Value q) : HProp Heap Ptr Region Value :=
  (p ↦ u) ∗ (q ↦ v)

example (P Q : HProp Heap Ptr Region Value) : (P ∗ Q).region = P.region ⊔ Q.region := rfl

example (p : Ptr) (u : Value p) :
    (HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) p u).region =
      span (Heap := Heap) (Region := Region) (Value := Value) p := rfl

example (p q : Ptr) (u : Value p) (v : Value q) (h : Heap)
    (hh : ((HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) p u) ∗
      (HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) q v)).holds h) :
    noOverlap (span (Heap := Heap) (Region := Region) (Value := Value) p)
      (span (Heap := Heap) (Region := Region) (Value := Value) q) :=
  sep_separated hh

example (p q : Ptr) (u : Value p) (v : Value q) (h : Heap)
    (hh : ((HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) p u) ∗
      (HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) q v)).holds h) :
    load (Region := Region) h p = u ∧ load (Region := Region) h q = v :=
  ⟨hh.2.1, hh.2.2⟩

example (P : HProp Heap Ptr Region Value) : (emp ∗ P).region = P.region :=
  emp_sep_region P

example (p : Ptr) (u : Value p) : Assertion (heapShape Heap) :=
  HProp.toAssertion (Region := Region)
    (HProp.pointsTo (Heap := Heap) (Region := Region) (Value := Value) p u)

example {α : Type u} (P : Heap → Prop) (S : Region)
    (hP : Supported (Ptr := Ptr) (Region := Region) (Value := Value) P S)
    {c : Heap → α × Heap} {R : Region}
    (hc : Writes (Ptr := Ptr) (Region := Region) (Value := Value) c R)
    (hd : noOverlap R S)
    {h : Heap} (h0 : P h) : P (c h).2 :=
  Supported.frame hP hc hd h0

end Abstract

section Concrete

#synth HeapAlgebra (Nat → Nat) Nat (Set Nat) (fun _ => Nat)
#synth LawfulHeapAlgebra (Nat → Nat) Nat (Set Nat) (fun _ => Nat)

abbrev HeapM := StateM (Nat → Nat)

#synth MonadHeap (Nat → Nat) HeapM
#synth WP HeapM (heapShape (Nat → Nat))
#synth WPMonad HeapM (heapShape (Nat → Nat))
#synth WPSound HeapM (heapShape (Nat → Nat))

noncomputable example : HProp (Nat → Nat) Nat (Set Nat) (fun _ => Nat) :=
  (1 ↦ (10 : Nat)) ∗ (2 ↦ (20 : Nat))

#check (readPtr (Region := Set Nat) (Value := fun _ : Nat => Nat) (1 : Nat) : HeapM Nat)
#check (writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
  (1 : Nat) (10 : Nat) : HeapM PUnit)

noncomputable def pre : HProp (Nat → Nat) Nat (Set Nat) (fun _ => Nat) :=
  (1 ↦ (10 : Nat)) ∗ (2 ↦ (20 : Nat))

noncomputable def post : PUnit → HProp (Nat → Nat) Nat (Set Nat) (fun _ => Nat) :=
  fun _ => (1 ↦ (99 : Nat)) ∗ (2 ↦ (20 : Nat))

#check (pre.toAssertion : Assertion (heapShape (Nat → Nat)))
#check (HProp.toPost post : PostCond PUnit (heapShape (Nat → Nat)))

#check (HTriple pre (writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
  (1 : Nat) (99 : Nat) : HeapM PUnit) post : Prop)

theorem write_one_frame :
    HTriple pre (writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
      (1 : Nat) (99 : Nat) : HeapM PUnit) post := by
  refine ⟨?correct, ?footprint⟩
  case correct =>
    simp [Std.Do.Triple, Std.Do.wp, pre, post, HProp.toAssertion, HProp.toPost,
      HProp.sep, HProp.pointsTo, writePtr]
    intro h hsep _ htwo
    refine ⟨hsep, ?_, ?_⟩
    · exact LawfulHeapAlgebra.load_after_store (Region := Set Nat)
        (Value := fun _ : Nat => Nat) (1 : Nat) (99 : Nat) h
    · rw [LawfulHeapAlgebra.store_no_alias (Region := Set Nat)
        (Value := fun _ : Nat => Nat) (1 : Nat) (2 : Nat) (99 : Nat) h hsep]
      exact htwo
  case footprint =>
    intro h
    refine (writePtr_writes (Region := Set Nat) (Value := fun _ : Nat => Nat)
      (1 : Nat) (99 : Nat) h).trans ?_
    simp [pre, HProp.sep, HProp.pointsTo]

#check (FramedTriple pre.toAssertion
          (writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
            (1 : Nat) (99 : Nat) : HeapM PUnit)
          (HProp.toPost post) pre.region : Prop)

#check (wp⟦(writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
          (1 : Nat) (99 : Nat) : HeapM PUnit)⟧
          (HProp.toPost post) : Assertion (heapShape (Nat → Nat)))

example :
    (pre.toAssertion : Assertion (heapShape (Nat → Nat)))
      ⊢ₛ wp⟦(writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
            (1 : Nat) (99 : Nat) : HeapM PUnit)⟧
            (HProp.toPost post) := by
  exact write_one_frame.1

example :
    Std.Do.Triple (writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
      (1 : Nat) (99 : Nat) : HeapM PUnit)
      pre.toAssertion (HProp.toPost post)
      = ((pre.toAssertion : Assertion (heapShape (Nat → Nat)))
          ⊢ₛ wp⟦(writePtr (Region := Set Nat) (Value := fun _ : Nat => Nat)
            (1 : Nat) (99 : Nat) : HeapM PUnit)⟧
                (HProp.toPost post)) := rfl

end Concrete
