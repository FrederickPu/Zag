import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Disjoint
import Mathlib.Data.Set.BooleanAlgebra
import Std.Do

universe u v

abbrev noOverlap {Region : Type u} [BooleanAlgebra Region] (a b : Region) : Prop :=
  Disjoint a b

class HeapAlgebra (Heap Ptr Region : Type u) (Value : Ptr → Type u)
    [BooleanAlgebra Region] where
  span    : Ptr → Region
  changed : Heap → Heap → Region
  load  : Heap → (p : Ptr) → Value p
  store : (p : Ptr) → Value p → Heap → Heap

class LawfulHeapAlgebra (Heap Ptr Region : Type u) (Value : Ptr → Type u)
    [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value] : Prop where
  changed_rfl      : ∀ h : Heap,
    HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h h =
      (⊥ : Region)
  changed_symm     : ∀ a b : Heap,
    HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) a b =
      HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) b a
  changed_triangle : ∀ a b c : Heap,
    HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) a c ≤
      HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) a b ⊔
        HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) b c
  store_writes_only : ∀ (p : Ptr) (v : Value p) (h : Heap),
    HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h
      (HeapAlgebra.store (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) p v h) ≤
      HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p
  load_after_store  : ∀ (p : Ptr) (v : Value p) (h : Heap),
    HeapAlgebra.load (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value)
      (HeapAlgebra.store (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) p v h) p = v
  store_no_alias    : ∀ (p q : Ptr) (v : Value p) (h : Heap),
    noOverlap (HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p)
      (HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) q) →
    HeapAlgebra.load (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value)
      (HeapAlgebra.store (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) p v h) q =
      HeapAlgebra.load (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h q
  load_unchanged    : ∀ (p : Ptr) (h h' : Heap),
    noOverlap (HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h h')
      (HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p) →
    HeapAlgebra.load (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h p =
      HeapAlgebra.load (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h' p

namespace HeapAlgebra

variable {Heap Ptr Region : Type u} {Value : Ptr → Type u}
  [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
  [LawfulHeapAlgebra Heap Ptr Region Value]

open LawfulHeapAlgebra

def Separated (p q : Ptr) : Prop :=
  noOverlap (span (Heap := Heap) (Region := Region) (Value := Value) p)
    (span (Heap := Heap) (Region := Region) (Value := Value) q)

def Writes {α : Type v} (c : Heap → α × Heap) (R : Region) : Prop :=
  ∀ h, changed (Ptr := Ptr) (Region := Region) (Value := Value) h (c h).2 ≤ R

theorem frame_load {α : Type v} {c : Heap → α × Heap} {R : Region} {p : Ptr} {h : Heap}
    (hc : Writes (Ptr := Ptr) (Region := Region) (Value := Value) c R)
    (hd : noOverlap R (span (Heap := Heap) (Region := Region) (Value := Value) p)) :
    load (Ptr := Ptr) (Region := Region) (Value := Value) (c h).2 p =
      load (Ptr := Ptr) (Region := Region) (Value := Value) h p :=
  (load_unchanged (Region := Region) (Value := Value) p h (c h).2
    (hd.mono_left (hc h))).symm

theorem Writes.seq {α β : Type v} {c₁ : Heap → α × Heap} {c₂ : Heap → β × Heap}
    {R₁ R₂ : Region}
    (h₁ : Writes (Ptr := Ptr) (Region := Region) (Value := Value) c₁ R₁)
    (h₂ : Writes (Ptr := Ptr) (Region := Region) (Value := Value) c₂ R₂) :
    Writes (Ptr := Ptr) (Region := Region) (Value := Value)
      (fun h => let (_, h') := c₁ h; c₂ h') (R₁ ⊔ R₂) := by
  intro h
  refine (changed_triangle (Ptr := Ptr) (Region := Region) (Value := Value)
    h (c₁ h).2 _).trans ?_
  exact sup_le_sup (h₁ h) (h₂ (c₁ h).2)

theorem store_writes (p : Ptr) (v : Value p) :
    Writes (Ptr := Ptr) (Region := Region) (Value := Value)
      (fun h => ((), store (Heap := Heap) (Ptr := Ptr) (Region := Region)
        (Value := Value) p v h))
      (span (Heap := Heap) (Region := Region) (Value := Value) p) :=
  fun h => store_writes_only (Heap := Heap) (Region := Region) (Value := Value) p v h

def Supported (P : Heap → Prop) (R : Region) : Prop :=
  ∀ h h', noOverlap (changed (Ptr := Ptr) (Region := Region) (Value := Value) h h') R →
    (P h ↔ P h')

omit [LawfulHeapAlgebra Heap Ptr Region Value] in
theorem Supported.frame {α : Type v} {P : Heap → Prop} {S R : Region}
    (hP : Supported (Ptr := Ptr) (Region := Region) (Value := Value) P S)
    {c : Heap → α × Heap}
    (hc : Writes (Ptr := Ptr) (Region := Region) (Value := Value) c R)
    (hd : noOverlap R S) {h : Heap} (h0 : P h) : P (c h).2 :=
  (hP h (c h).2 (hd.mono_left (hc h))).mp h0

end HeapAlgebra

class Allocator (Heap Ptr Region : Type u) (Value : Ptr → Type u) (Request : Type v)
    [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value] where
  valid : Region → Heap → Prop
  alloc : Request → Region → Heap → Ptr × Region × Heap
  alloc_fresh  : ∀ request owned h, valid owned h →
    let (p, owned', _) := alloc request owned h
    noOverlap owned (HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p) ∧
      owned' = owned ⊔
        HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p
  alloc_valid : ∀ request owned h, valid owned h →
    let (_, owned', h') := alloc request owned h
    valid owned' h'
  alloc_writes : ∀ request owned h,
    let (p, _, h') := alloc request owned h
    HeapAlgebra.changed (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) h h' ≤
      HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p

class Deallocator (Heap Ptr Region : Type u) (Value : Ptr → Type u)
    [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value] where
  free : Ptr → Region → Heap → Region × Heap
  free_owned : ∀ p owned h,
    HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p ≤ owned →
    (free p owned h).1 = owned \
      HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p

class MonadHeap (Heap : outParam (Type u)) (m : Type u → Type v) [Monad m]
    extends MonadStateOf Heap m where
  run      : {α : Type u} → m α → Heap → α × Heap
  run_get  : ∀ h, run (get : m Heap) h = (h, h)
  run_set  : ∀ h h', run (set h' : m PUnit) h = (PUnit.unit, h')
  run_bind : ∀ {α β} (c : m α) (f : α → m β) h,
               run (c >>= f) h = run (f (run c h).1) (run c h).2

instance {Heap : Type u} : MonadHeap Heap (StateM Heap) where
  run c h  := c.run h
  run_get  := by intro _; rfl
  run_set  := by intro _ _; rfl
  run_bind := by intro _ _ _ _ _; rfl

def readPtr {Heap Ptr Region : Type u} {Value : Ptr → Type u} {m : Type u → Type v}
    [Monad m] [MonadHeap Heap m] [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
    (p : Ptr) : m (Value p) :=
  (fun h => HeapAlgebra.load (Ptr := Ptr) (Region := Region) (Value := Value) h p) <$> get

def writePtr {Heap Ptr Region : Type u} {Value : Ptr → Type u} {m : Type u → Type v}
    [Monad m] [MonadHeap Heap m] [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
    (p : Ptr) (v : Value p) : m PUnit :=
  modify (HeapAlgebra.store (Heap := Heap) (Ptr := Ptr) (Region := Region) (Value := Value) p v)

open Std.Do

abbrev heapShape (Heap : Type u) : PostShape.{u} := .arg Heap .pure

example {Heap : Type u} : Assertion (heapShape Heap) = (Heap → ULift Prop) := rfl
example {Heap α : Type} :
    PostCond α (heapShape Heap) = ((α → Heap → ULift Prop) × PUnit) := rfl

def ofHeapPred {Heap : Type u} (P : Heap → Prop) : Assertion (heapShape Heap) :=
  fun h => ⌜P h⌝

def FramedTriple {Heap Ptr Region : Type u} {Value : Ptr → Type u}
    {α : Type u} [BooleanAlgebra Region]
    [HeapAlgebra Heap Ptr Region Value]
    (P : Assertion (heapShape Heap)) (c : StateM Heap α)
    (Q : PostCond α (heapShape Heap)) (R : Region) : Prop :=
  Triple c P Q ∧ ∀ h : Heap,
    HeapAlgebra.changed (Ptr := Ptr) (Region := Region) (Value := Value) h (c.run h).2 ≤ R

structure HProp (Heap Ptr Region : Type u) (Value : Ptr → Type u)
    [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value] where
  region    : Region
  holds     : Heap → Prop
  supported : HeapAlgebra.Supported (Ptr := Ptr) (Region := Region) (Value := Value)
    holds region

namespace HProp

variable {Heap Ptr Region : Type u} {Value : Ptr → Type u}
  [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
  [LawfulHeapAlgebra Heap Ptr Region Value]

def emp : HProp Heap Ptr Region Value where
  region    := ⊥
  holds     := fun _ => True
  supported := by intro _ _ _; exact Iff.rfl

def pointsTo (p : Ptr) (v : Value p) : HProp Heap Ptr Region Value where
  region    := HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p
  holds     := fun h =>
    HeapAlgebra.load (Ptr := Ptr) (Region := Region) (Value := Value) h p = v
  supported := by
    intro h h' hd
    change HeapAlgebra.load (Ptr := Ptr) (Region := Region) (Value := Value) h p = v ↔
      HeapAlgebra.load (Ptr := Ptr) (Region := Region) (Value := Value) h' p = v
    rw [LawfulHeapAlgebra.load_unchanged (Region := Region) (Value := Value) p h h' hd]

def sep (P Q : HProp Heap Ptr Region Value) : HProp Heap Ptr Region Value where
  region    := P.region ⊔ Q.region
  holds     := fun h => noOverlap P.region Q.region ∧ P.holds h ∧ Q.holds h
  supported := by
    intro h h' hd
    have hP := hd.mono_right (le_sup_left  : P.region ≤ P.region ⊔ Q.region)
    have hQ := hd.mono_right (le_sup_right : Q.region ≤ P.region ⊔ Q.region)
    exact and_congr Iff.rfl (and_congr (P.supported h h' hP) (Q.supported h h' hQ))

scoped infixr:35 " ∗ " => HProp.sep
scoped infix:55 " ↦ " => HProp.pointsTo

def toAssertion (P : HProp Heap Ptr Region Value) : Assertion (heapShape Heap) :=
  fun h => ⌜P.holds h⌝

omit [LawfulHeapAlgebra Heap Ptr Region Value] in
theorem sep_separated {P Q : HProp Heap Ptr Region Value} {h : Heap}
    (hpq : (P ∗ Q).holds h) : noOverlap P.region Q.region :=
  hpq.1

omit [LawfulHeapAlgebra Heap Ptr Region Value] in
theorem emp_sep_region (P : HProp Heap Ptr Region Value) :
    (emp ∗ P).region = P.region := by simp [sep, emp]

end HProp

def HProp.toPost {Heap Ptr Region : Type u} {Value : Ptr → Type u} {α : Type u}
    [BooleanAlgebra Region] [HeapAlgebra Heap Ptr Region Value]
    (Q : α → HProp Heap Ptr Region Value) : PostCond α (heapShape Heap) :=
  PostCond.noThrow (fun a => HProp.toAssertion (Q a))

def HTriple {Heap Ptr Region : Type u} {Value : Ptr → Type u}
    {α : Type u} [BooleanAlgebra Region]
    [HeapAlgebra Heap Ptr Region Value]
    (P : HProp Heap Ptr Region Value) (c : StateM Heap α)
    (Q : α → HProp Heap Ptr Region Value) : Prop :=
  FramedTriple (Ptr := Ptr) (Region := Region) (Value := Value)
    (HProp.toAssertion P) c (HProp.toPost Q) P.region

theorem writePtr_writes {Heap Ptr Region : Type u} {Value : Ptr → Type u}
    [BooleanAlgebra Region]
    [HeapAlgebra Heap Ptr Region Value] [LawfulHeapAlgebra Heap Ptr Region Value]
    (p : Ptr) (v : Value p) (h : Heap) :
    HeapAlgebra.changed (Ptr := Ptr) (Region := Region) (Value := Value) h
      ((writePtr (Region := Region) p v : StateM Heap PUnit).run h).2
      ≤ HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p := by
  change HeapAlgebra.changed (Ptr := Ptr) (Region := Region) (Value := Value) h
    (HeapAlgebra.store (Region := Region) p v h) ≤
      HeapAlgebra.span (Heap := Heap) (Region := Region) (Value := Value) p
  exact LawfulHeapAlgebra.store_writes_only (Region := Region) p v h

section Model
variable (Addr V : Type) [DecidableEq Addr]

instance : HeapAlgebra (Addr → V) Addr (Set Addr) (fun _ => V) where
  span a       := {a}
  changed h h' := {a | h a ≠ h' a}
  load h a     := h a
  store a v h  := Function.update h a v

instance : LawfulHeapAlgebra (Addr → V) Addr (Set Addr) (fun _ => V) where
  changed_rfl h := by
    change {a | h a ≠ h a} = ∅
    ext a
    simp
  changed_symm a b := by
    change {x | a x ≠ b x} = {x | b x ≠ a x}
    ext x
    simp [ne_comm]
  changed_triangle a b c := by
    change {x | a x ≠ c x} ⊆ {x | a x ≠ b x} ∪ {x | b x ≠ c x}
    intro x hx; by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at *
    exact hx (hcon.1.trans hcon.2)
  store_writes_only p v h := by
    change {a | h a ≠ Function.update h p v a} ⊆ {p}
    intro a ha
    by_contra hne
    simp only [Set.mem_singleton_iff] at hne
    apply ha
    simp [Function.update, hne]
  load_after_store p v h := by
    change Function.update h p v p = v
    simp [Function.update]
  store_no_alias p q v h hpq := by
    have : q ≠ p := fun he => (Set.disjoint_singleton.mp hpq) (he ▸ rfl)
    change Function.update h p v q = h q
    simp [Function.update, this]
  load_unchanged p h h' hd := by
    change Disjoint {x | h x ≠ h' x} {p} at hd
    by_contra hne
    exact (Set.disjoint_singleton_right.mp hd) hne
end Model
