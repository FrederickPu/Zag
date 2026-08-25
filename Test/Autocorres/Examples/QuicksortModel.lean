import Lib.PeanoHeap

/-!
Pure list reasoning, exact ambient-heap model, and universal correctness for pointer-addressed quicksort.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

/-! ## Pure semantics and array facts -/

@[simp] theorem heapArray_length_set (xs : HeapArray) (i value : Nat) :
    (HeapArray.set xs i value).length = xs.length := by
  induction xs generalizing i with
  | nil => simp [HeapArray.set]
  | cons x xs ih =>
      cases i <;> simp [HeapArray.set, ih]

theorem heapArray_get_eq_getElem {xs : HeapArray} {i : Nat} (hi : i < xs.length) :
    HeapArray.get xs i = xs[i] := by
  simp [HeapArray.get, hi]

@[simp] theorem heapArray_get_set_self {xs : HeapArray} {i value : Nat}
    (hi : i < xs.length) :
    HeapArray.get (HeapArray.set xs i value) i = value := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [HeapArray.set, HeapArray.get]
      | succ i =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          simpa [HeapArray.set, HeapArray.get] using ih hi

@[simp] theorem heapArray_get_set_of_ne {xs : HeapArray} {i j value : Nat}
    (hij : j ≠ i) :
    HeapArray.get (HeapArray.set xs i value) j = HeapArray.get xs j := by
  induction xs generalizing i j with
  | nil => simp [HeapArray.set, HeapArray.get]
  | cons x xs ih =>
      cases i <;> cases j <;> simp_all [HeapArray.set, HeapArray.get]

theorem heapArray_get_set {xs : HeapArray} {i k value : Nat} (hi : i < xs.length) :
    HeapArray.get (HeapArray.set xs i value) k =
      if k = i then value else HeapArray.get xs k := by
  by_cases hki : k = i
  · subst k
    simp [hi]
  · simp [hki]

theorem heapArray_get_set_perm_cons (xs : HeapArray) (value : Nat) {i : Nat}
    (hi : i < xs.length) :
    List.Perm (HeapArray.get xs i :: HeapArray.set xs i value) (value :: xs) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simpa [HeapArray.set, HeapArray.get] using (List.Perm.swap x value xs).symm
      | succ i =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          have hmove : List.Perm
              (HeapArray.get xs i :: x :: HeapArray.set xs i value)
              (x :: HeapArray.get xs i :: HeapArray.set xs i value) :=
            List.Perm.swap _ _ _
          exact hmove.trans ((ih hi).cons x) |>.trans (List.Perm.swap x value xs).symm

theorem heapArray_swap_perm (xs : HeapArray) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    List.Perm (HeapArray.swap xs i j) xs := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [HeapArray.swap, HeapArray.set, HeapArray.get]
          | succ j =>
              simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
              simpa [HeapArray.swap, HeapArray.set, HeapArray.get] using
                heapArray_get_set_perm_cons xs x hj
      | succ i =>
          cases j with
          | zero =>
              simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
              simpa [HeapArray.swap, HeapArray.set, HeapArray.get] using
                heapArray_get_set_perm_cons xs x hi
          | succ j =>
              simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hj
              simpa [HeapArray.swap, HeapArray.set, HeapArray.get] using (ih hi hj).cons x

@[simp] theorem heapArray_length_swap (xs : HeapArray) (i j : Nat) :
    (HeapArray.swap xs i j).length = xs.length := by
  simp [HeapArray.swap]

theorem heapArray_get_swap {xs : HeapArray} {i j k : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    HeapArray.get (HeapArray.swap xs i j) k =
      if k = j then HeapArray.get xs i
      else if k = i then HeapArray.get xs j
      else HeapArray.get xs k := by
  by_cases hkj : k = j
  · subst k
    simp [HeapArray.swap, hi, hj]
  · by_cases hki : k = i
    · subst k
      simp [HeapArray.swap, hi, hj, hkj]
    · simp [HeapArray.swap, hkj, hki]

/-- One successful source partition step. The two swaps are extensionally the source's three
assignments: rotate the current value before the pivot, and shift the intervening first value to
the old current position. -/

def partitionSwap (xs : HeapArray) (start pivotIdx i : Nat) : HeapArray :=
  HeapArray.swap
    (HeapArray.swap xs (start + pivotIdx) (start + i))
    (start + pivotIdx + 1) (start + i)

def partitionRotateSets (xs : HeapArray) (start pivotIdx i : Nat) : HeapArray :=
  let pivotPos := start + pivotIdx
  let iPos := start + i
  let pivot := HeapArray.get xs pivotPos
  let current := HeapArray.get xs iPos
  let movedCurrent := HeapArray.set xs pivotPos current
  let nextPivotPos := start + (pivotIdx + 1)
  let shifted := HeapArray.get movedCurrent nextPivotPos
  let movedShifted := HeapArray.set movedCurrent iPos shifted
  HeapArray.set movedShifted nextPivotPos pivot

theorem partitionRotateSets_get (xs : HeapArray) (start pivotIdx i k : Nat)
    (hp : start + pivotIdx < xs.length) (hi : start + i < xs.length)
    (hn : start + (pivotIdx + 1) < xs.length) :
    HeapArray.get (partitionRotateSets xs start pivotIdx i) k =
      if k = start + (pivotIdx + 1) then HeapArray.get xs (start + pivotIdx)
      else if k = start + i then
        (if start + (pivotIdx + 1) = start + pivotIdx then HeapArray.get xs (start + i)
         else HeapArray.get xs (start + (pivotIdx + 1)))
      else if k = start + pivotIdx then HeapArray.get xs (start + i)
      else HeapArray.get xs k := by
  unfold partitionRotateSets
  rw [heapArray_get_set (i := start + (pivotIdx + 1)) (by simp; exact hn)]
  rw [heapArray_get_set (i := start + i) (by simp; exact hi)]
  simp only [heapArray_get_set hp]

theorem partitionRotateSets_eq_swap (xs : HeapArray) (start pivotIdx i : Nat)
    (hpivot : pivotIdx < i) (hi : start + i < xs.length) :
    partitionRotateSets xs start pivotIdx i = partitionSwap xs start pivotIdx i := by
  have hp : start + pivotIdx < xs.length := by omega
  have hn : start + pivotIdx + 1 < xs.length := by omega
  apply List.ext_getElem
  · simp [partitionRotateSets, partitionSwap]
  intro k hkLeft hkRight
  have hk : k < xs.length := by simpa [partitionRotateSets] using hkLeft
  rw [← heapArray_get_eq_getElem hkLeft, ← heapArray_get_eq_getElem hkRight]
  have hn' : start + pivotIdx + 1 <
      (HeapArray.swap xs (start + pivotIdx) (start + i)).length := by simpa using hn
  have hi' : start + i <
      (HeapArray.swap xs (start + pivotIdx) (start + i)).length := by simpa using hi
  rw [show HeapArray.get (partitionSwap xs start pivotIdx i) k = _ by
    exact heapArray_get_swap hn' hi']
  simp only [heapArray_get_swap hp hi]
  rw [partitionRotateSets_get xs start pivotIdx i k hp hi (by omega)]
  simp only [Nat.add_assoc] at *
  have hpi : pivotIdx ≠ i := by omega
  simp only [hpi, ↓reduceIte]
  by_cases hki : k = start + i
  · subst k
    by_cases hadj : pivotIdx + 1 = i
    · simp [partitionRotateSets, partitionSwap, heapArray_get_swap, Nat.add_assoc, hp, hn, hi,
        hadj] <;> omega
    · have hnep : start + i ≠ start + pivotIdx := by omega
      have hnen : start + i ≠ start + pivotIdx + 1 := by omega
      simp [partitionRotateSets, partitionSwap, heapArray_get_swap, Nat.add_assoc, hp, hn, hi,
        hnep, hnen, hadj] <;> omega
  · by_cases hkp : k = start + pivotIdx
    · subst k
      have hnepi : start + pivotIdx ≠ start + i := by omega
      have hnepn : start + pivotIdx ≠ start + pivotIdx + 1 := by omega
      simp [partitionRotateSets, partitionSwap, heapArray_get_swap, Nat.add_assoc, hp, hn, hi,
        hpi, hnepi, hnepn] <;> omega
    · by_cases hkn : k = start + pivotIdx + 1
      · subst k
        by_cases hadj : pivotIdx + 1 = i
        · omega
        · have hne : start + pivotIdx + 1 ≠ start + i := by omega
          simp [partitionRotateSets, partitionSwap, heapArray_get_swap, Nat.add_assoc, hp, hn, hi,
            hadj, hne] <;> omega
      · simp [partitionRotateSets, partitionSwap, heapArray_get_swap, Nat.add_assoc, hp, hn, hi,
          hki, hkp, hkn] <;> omega


def partitionLoopSpec (xs : HeapArray) (start n pivotIdx i : Nat) : HeapArray × Nat :=
  if n ≤ i then (xs, pivotIdx)
  else
    let pivot := HeapArray.get xs (start + pivotIdx)
    let current := HeapArray.get xs (start + i)
    if current < pivot then
      partitionLoopSpec (partitionSwap xs start pivotIdx i) start n (pivotIdx + 1) (i + 1)
    else
      partitionLoopSpec xs start n pivotIdx (i + 1)
termination_by n - i
decreasing_by all_goals omega

def partitionRangeSpec (xs : HeapArray) (start n : Nat) : HeapArray × Nat :=
  partitionLoopSpec xs start n 0 1

@[simp] theorem partitionSwap_length (xs : HeapArray) (start pivotIdx i : Nat) :
    (partitionSwap xs start pivotIdx i).length = xs.length := by
  simp [partitionSwap]

theorem partitionSwap_perm (xs : HeapArray) (start pivotIdx i : Nat)
    (hp : start + pivotIdx < xs.length) (hi : start + i < xs.length)
    (hn : start + pivotIdx + 1 < xs.length) :
    List.Perm (partitionSwap xs start pivotIdx i) xs := by
  apply (heapArray_swap_perm _ (by simpa using hn) (by simpa using hi)).trans
  exact heapArray_swap_perm xs hp hi

theorem partitionSwap_get (xs : HeapArray) (start pivotIdx i k : Nat)
    (hpivot : pivotIdx < i) (hi : start + i < xs.length) :
    HeapArray.get (partitionSwap xs start pivotIdx i) k =
      if k = start + (pivotIdx + 1) then HeapArray.get xs (start + pivotIdx)
      else if k = start + i then HeapArray.get xs (start + (pivotIdx + 1))
      else if k = start + pivotIdx then HeapArray.get xs (start + i)
      else HeapArray.get xs k := by
  rw [← partitionRotateSets_eq_swap xs start pivotIdx i hpivot hi]
  rw [partitionRotateSets_get]
  · by_cases hadj : pivotIdx + 1 = i
    · have heq : start + (pivotIdx + 1) = start + i := by omega
      simp [heq]
    · have hne : start + (pivotIdx + 1) ≠ start + i := by omega
      simp [hne]
  all_goals omega

/-- The loop invariant used by the universal partition proof. It records the original pivot as a
ghost value, not as an implementation shortcut. -/
theorem partitionLoopSpec_invariant (xs : HeapArray) (start n pivotIdx i pivot : Nat)
    (hbound : start + n ≤ xs.length) (hpivotIdx : pivotIdx < i) (hi : i ≤ n)
    (hpivot : HeapArray.get xs (start + pivotIdx) = pivot)
    (hleft : ∀ j, j < pivotIdx → HeapArray.get xs (start + j) < pivot)
    (hright : ∀ j, pivotIdx < j → j < i → pivot ≤ HeapArray.get xs (start + j)) :
    let out := partitionLoopSpec xs start n pivotIdx i
    out.1.length = xs.length ∧ List.Perm out.1 xs ∧
      pivotIdx ≤ out.2 ∧ out.2 < n ∧
      HeapArray.get out.1 (start + out.2) = pivot ∧
      (∀ j, j < out.2 → HeapArray.get out.1 (start + j) < pivot) ∧
      (∀ j, out.2 < j → j < n → pivot ≤ HeapArray.get out.1 (start + j)) ∧
      (∀ k, k < start ∨ start + n ≤ k → HeapArray.get out.1 k = HeapArray.get xs k) := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing xs pivotIdx i with
  | ind measure ih =>
      rw [partitionLoopSpec]
      split <;> rename_i hdone
      · dsimp only
        have hieq : i = n := by omega
        subst i
        refine ⟨rfl, List.Perm.refl _, Nat.le_refl _, by omega, hpivot, hleft, ?_, ?_⟩
        · intro j hpj hjn
          exact hright j hpj hjn
        · intros
          rfl
      · have hin : i < n := by omega
        have hipos : start + i < xs.length := by omega
        by_cases hcurrent : HeapArray.get xs (start + i) < pivot
        · have hp : start + pivotIdx < xs.length := by omega
          have hn : start + (pivotIdx + 1) < xs.length := by omega
          let ys := partitionSwap xs start pivotIdx i
          have hysLen : ys.length = xs.length := by simp [ys]
          have hysBound : start + n ≤ ys.length := by simpa [hysLen]
          have hysPivot : HeapArray.get ys (start + (pivotIdx + 1)) = pivot := by
            simp [ys, partitionSwap_get, hpivotIdx, hipos, hpivot]
          have hysLeft : ∀ j, j < pivotIdx + 1 →
              HeapArray.get ys (start + j) < pivot := by
            intro j hj
            by_cases hjp : j = pivotIdx
            · subst j
              have hpi : pivotIdx ≠ i := by omega
              simpa [ys, partitionSwap_get, hpivotIdx, hipos, hpi] using hcurrent
            · have hji : j ≠ i := by omega
              have hjn : j ≠ pivotIdx + 1 := by omega
              simpa [ys, partitionSwap_get, hpivotIdx, hipos, hjp, hji, hjn] using
                hleft j (by omega)
          have hysRight : ∀ j, pivotIdx + 1 < j → j < i + 1 →
              pivot ≤ HeapArray.get ys (start + j) := by
            intro j hpj hji
            by_cases hjeq : j = i
            · subst j
              have hinext : i ≠ pivotIdx + 1 := by omega
              have hnext : pivot ≤ HeapArray.get xs (start + (pivotIdx + 1)) :=
                hright (pivotIdx + 1) (by omega) (by omega)
              simpa [ys, partitionSwap_get, hpivotIdx, hipos, hinext] using hnext
            · have hjp : j ≠ pivotIdx := by omega
              have hjn : j ≠ pivotIdx + 1 := by omega
              simpa [ys, partitionSwap_get, hpivotIdx, hipos, hjeq, hjp, hjn] using
                hright j (by omega) (by omega)
          have hysOutside : ∀ k, k < start ∨ start + n ≤ k →
              HeapArray.get ys k = HeapArray.get xs k := by
            intro k hk
            have hki : k ≠ start + i := by omega
            have hkp : k ≠ start + pivotIdx := by omega
            have hkn : k ≠ start + (pivotIdx + 1) := by omega
            simp [ys, partitionSwap_get, hpivotIdx, hipos, hki, hkp, hkn]
          have hrec := ih (n - (i + 1)) (by omega) ys (pivotIdx + 1) (i + 1)
            hysBound (by omega) (by omega) hysPivot hysLeft hysRight rfl
          rw [if_pos (by simpa [hpivot] using hcurrent)]
          dsimp only [ys] at hrec
          dsimp only
          rcases hrec with ⟨hlen, hperm, hpmono, hpout, hpiv, hl, hr, hout⟩
          refine ⟨hlen.trans hysLen, hperm.trans ?_, Nat.le_trans (Nat.le_succ _) hpmono,
            hpout, hpiv, hl, hr, ?_⟩
          · exact partitionSwap_perm xs start pivotIdx i hp hipos (by omega)
          · intro k hk
            exact (hout k hk).trans (hysOutside k hk)
        · have hnextRight : ∀ j, pivotIdx < j → j < i + 1 →
              pivot ≤ HeapArray.get xs (start + j) := by
            intro j hpj hj
            by_cases hji : j = i
            · subst j
              omega
            · exact hright j hpj (by omega)
          have hrec := ih (n - (i + 1)) (by omega) xs pivotIdx (i + 1)
            hbound (by omega) (by omega) hpivot hleft hnextRight rfl
          rw [if_neg (by simpa [hpivot] using hcurrent)]
          exact hrec

theorem partitionLoopSpec_index (xs : HeapArray) (start n pivotIdx i : Nat)
    (hpivotIdx : pivotIdx < i) (hi : i ≤ n) :
    pivotIdx ≤ (partitionLoopSpec xs start n pivotIdx i).2 ∧
      (partitionLoopSpec xs start n pivotIdx i).2 < n := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing xs pivotIdx i with
  | ind measure ih =>
      rw [partitionLoopSpec]
      split <;> rename_i hdone
      · simp only [Prod.snd]
        omega
      · by_cases hlt : HeapArray.get xs (start + i) <
            HeapArray.get xs (start + pivotIdx)
        · rw [if_pos hlt]
          have hrec := ih (n - (i + 1)) (by omega)
            (partitionSwap xs start pivotIdx i) (pivotIdx + 1) (i + 1)
            (by omega) (by omega) rfl
          exact ⟨Nat.le_trans (Nat.le_succ _) hrec.1, hrec.2⟩
        · rw [if_neg hlt]
          exact ih (n - (i + 1)) (by omega) xs pivotIdx (i + 1)
            (by omega) (by omega) rfl

theorem partitionRangeSpec_correct (xs : HeapArray) (start n : Nat)
    (hbound : start + n ≤ xs.length) (hn : 0 < n) :
    let out := partitionRangeSpec xs start n
    out.1.length = xs.length ∧ List.Perm out.1 xs ∧ out.2 < n ∧
      HeapArray.get out.1 (start + out.2) = HeapArray.get xs start ∧
      (∀ j, j < out.2 →
        HeapArray.get out.1 (start + j) < HeapArray.get xs start) ∧
      (∀ j, out.2 < j → j < n →
        HeapArray.get xs start ≤ HeapArray.get out.1 (start + j)) ∧
      (∀ k, k < start ∨ start + n ≤ k →
        HeapArray.get out.1 k = HeapArray.get xs k) := by
  have h := partitionLoopSpec_invariant xs start n 0 1 (HeapArray.get xs start)
    hbound (by omega) (by omega) rfl (by omega)
    (by intro j hj; omega)
  simpa [partitionRangeSpec] using
    And.intro h.1 ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

def RangeAll (xs : HeapArray) (start n : Nat) (P : Nat → Prop) : Prop :=
  ∀ j, j < n → P (HeapArray.get xs (start + j))

def RangeSorted (xs : HeapArray) (start n : Nat) : Prop :=
  ∀ i j, i < j → j < n →
    HeapArray.get xs (start + i) ≤ HeapArray.get xs (start + j)

theorem partitionLoopSpec_rangeAll (xs : HeapArray) (start n pivotIdx i : Nat)
    (hbound : start + n ≤ xs.length) (hpivotIdx : pivotIdx < i) (hi : i ≤ n)
    {P : Nat → Prop}
    (hall : RangeAll xs start n P) :
    RangeAll (partitionLoopSpec xs start n pivotIdx i).1 start n P := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing xs pivotIdx i with
  | ind measure ih =>
      rw [partitionLoopSpec]
      split <;> rename_i hdone
      · exact hall
      · by_cases hlt : HeapArray.get xs (start + i) <
            HeapArray.get xs (start + pivotIdx)
        · rw [if_pos hlt]
          refine ih (n - (i + 1)) (by omega) (partitionSwap xs start pivotIdx i)
            (pivotIdx + 1) (i + 1) (by simpa) (by omega) (by omega) ?_ rfl
          intro j hj
          rw [partitionSwap_get xs start pivotIdx i (start + j)]
          · split <;> rename_i heq
            · exact hall pivotIdx (by omega)
            split <;> rename_i heq
            · exact hall (pivotIdx + 1) (by omega)
            split <;> rename_i heq
            · exact hall i (by omega)
            · exact hall j hj
          · exact hpivotIdx
          · omega
        · rw [if_neg hlt]
          exact ih (n - (i + 1)) (by omega) xs pivotIdx (i + 1)
            hbound (by omega) (by omega) hall rfl


def quicksortRangeSpec (xs : HeapArray) (start n : Nat) : HeapArray :=
  if hactive : 1 < n then
    let part := partitionRangeSpec xs start n
    let left := quicksortRangeSpec part.1 start part.2
    quicksortRangeSpec left (start + part.2 + 1) (n - part.2 - 1)
  else xs
termination_by n
decreasing_by
  · have hp := (partitionLoopSpec_index xs start n 0 1 (by omega) (by omega)).2
    simpa [partitionRangeSpec] using hp
  · omega

def quicksortSpec (xs : HeapArray) (n : Nat) : HeapArray :=
  quicksortRangeSpec xs 0 n

def quicksortAllSpec (xs : HeapArray) : HeapArray :=
  quicksortSpec xs xs.length

theorem quicksortRangeSpec_correct (xs : HeapArray) (start n : Nat)
    (hbound : start + n ≤ xs.length) :
    let out := quicksortRangeSpec xs start n
    out.length = xs.length ∧ List.Perm out xs ∧
      (∀ k, k < start ∨ start + n ≤ k →
        HeapArray.get out k = HeapArray.get xs k) ∧
      RangeSorted out start n ∧
      (∀ (P : Nat → Prop), RangeAll xs start n P → RangeAll out start n P) := by
  induction n using Nat.strongRecOn generalizing xs start with
  | ind n ih =>
      rw [quicksortRangeSpec]
      split <;> rename_i hactive
      · dsimp only
        let part := partitionRangeSpec xs start n
        let split := part.1
        let p := part.2
        have hpart := partitionRangeSpec_correct xs start n hbound (by omega)
        change split.length = xs.length ∧ List.Perm split xs ∧ p < n ∧
          HeapArray.get split (start + p) = HeapArray.get xs start ∧
          (∀ j, j < p → HeapArray.get split (start + j) < HeapArray.get xs start) ∧
          (∀ j, p < j → j < n →
            HeapArray.get xs start ≤ HeapArray.get split (start + j)) ∧
          (∀ k, k < start ∨ start + n ≤ k →
            HeapArray.get split k = HeapArray.get xs k) at hpart
        rcases hpart with ⟨hsplitLen, hsplitPerm, hp, hpivot, hpartLeft,
          hpartRight, hpartOutside⟩
        let left := quicksortRangeSpec split start p
        have hleft := ih p hp split start (by omega)
        change left.length = split.length ∧ List.Perm left split ∧
          (∀ k, k < start ∨ start + p ≤ k →
            HeapArray.get left k = HeapArray.get split k) ∧
          RangeSorted left start p ∧
          (∀ (P : Nat → Prop), RangeAll split start p P → RangeAll left start p P) at hleft
        rcases hleft with ⟨hleftLen, hleftPerm, hleftOutside, hleftSorted, hleftAll⟩
        let rightStart := start + p + 1
        let rightLen := n - p - 1
        let out := quicksortRangeSpec left rightStart rightLen
        have hright := ih rightLen (by omega) left rightStart (by
          dsimp [rightStart, rightLen]
          rw [hleftLen, hsplitLen]
          omega)
        change out.length = left.length ∧ List.Perm out left ∧
          (∀ k, k < rightStart ∨ rightStart + rightLen ≤ k →
            HeapArray.get out k = HeapArray.get left k) ∧
          RangeSorted out rightStart rightLen ∧
          (∀ (P : Nat → Prop), RangeAll left rightStart rightLen P →
            RangeAll out rightStart rightLen P) at hright
        rcases hright with ⟨houtLen, houtPerm, houtOutside, hrightSorted, hrightAll⟩
        have hpivotLeft : HeapArray.get left (start + p) = HeapArray.get xs start :=
          (hleftOutside (start + p) (by omega)).trans hpivot
        have hpivotOut : HeapArray.get out (start + p) = HeapArray.get xs start :=
          (houtOutside (start + p) (by simp [rightStart])).trans hpivotLeft
        have hleftBound : ∀ j, j < p →
            HeapArray.get out (start + j) < HeapArray.get xs start := by
          have hallLeft : RangeAll left start p (· < HeapArray.get xs start) :=
            hleftAll _ (fun j hj => hpartLeft j hj)
          intro j hj
          rw [houtOutside (start + j) (by simp [rightStart]; omega)]
          exact hallLeft j hj
        have hrightInput : RangeAll left rightStart rightLen
            (HeapArray.get xs start ≤ ·) := by
          intro j hj
          rw [hleftOutside (rightStart + j) (by simp [rightStart]; omega)]
          have hboundRight : p + 1 + j < n := by
            dsimp [rightLen] at hj
            omega
          simpa [rightStart, Nat.add_assoc] using
            hpartRight (p + 1 + j) (by omega) hboundRight
        have hrightBound : ∀ j, p < j → j < n →
            HeapArray.get xs start ≤ HeapArray.get out (start + j) := by
          have hallRight := hrightAll _ hrightInput
          intro j hpj hj
          have hjlen : j - p - 1 < rightLen := by
            dsimp [rightLen]
            omega
          have := hallRight (j - p - 1) hjlen
          have heq : rightStart + (j - p - 1) = start + j := by
            dsimp [rightStart]
            omega
          simpa only [heq] using this
        have houtSorted : RangeSorted out start n := by
          intro i j hij hjn
          by_cases hjleft : j < p
          · rw [houtOutside (start + i) (by simp [rightStart]; omega),
              houtOutside (start + j) (by simp [rightStart]; omega)]
            exact hleftSorted i j hij hjleft
          by_cases hjpivot : j = p
          · subst j
            rw [hpivotOut]
            exact Nat.le_of_lt (hleftBound i (by omega))
          have hjright : p < j := by omega
          by_cases hipivot : i = p
          · subst i
            rw [hpivotOut]
            exact hrightBound j hjright hjn
          by_cases hileft : i < p
          · exact Nat.le_trans (Nat.le_of_lt (hleftBound i hileft))
              (hrightBound j hjright hjn)
          have hiright : p < i := by omega
          have hioff : i - p - 1 < j - p - 1 := by omega
          have hjoff : j - p - 1 < rightLen := by
            dsimp [rightLen]
            omega
          have hieq : rightStart + (i - p - 1) = start + i := by
            dsimp [rightStart]
            omega
          have hjeq : rightStart + (j - p - 1) = start + j := by
            dsimp [rightStart]
            omega
          simpa only [hieq, hjeq] using
            hrightSorted (i - p - 1) (j - p - 1) hioff hjoff
        have houtAll : ∀ (P : Nat → Prop), RangeAll xs start n P →
            RangeAll out start n P := by
          intro P hall j hj
          have hpartAll := partitionLoopSpec_rangeAll xs start n 0 1 hbound
            (by omega) (by omega) hall
          change RangeAll split start n P at hpartAll
          by_cases hjright : p < j
          · have hinput : RangeAll left rightStart rightLen P := by
              intro r hr
              rw [hleftOutside (rightStart + r) (by simp [rightStart]; omega)]
              have hrn : p + 1 + r < n := by
                dsimp [rightLen] at hr
                omega
              simpa [rightStart, Nat.add_assoc] using hpartAll (p + 1 + r) hrn
            have hfinal := hrightAll P hinput (j - p - 1) (by
              dsimp [rightLen]
              omega)
            have heq : rightStart + (j - p - 1) = start + j := by
              dsimp [rightStart]
              omega
            simpa only [heq] using hfinal
          · rw [houtOutside (start + j) (by simp [rightStart]; omega)]
            by_cases hjleft : j < p
            · exact hleftAll P (fun r hr => hpartAll r (by omega)) j hjleft
            · rw [hleftOutside (start + j) (by omega)]
              exact hpartAll j hj
        change out.length = xs.length ∧ List.Perm out xs ∧ _
        refine ⟨houtLen.trans (hleftLen.trans hsplitLen),
          houtPerm.trans (hleftPerm.trans hsplitPerm), ?_, houtSorted, houtAll⟩
        intro k hk
        exact (houtOutside k (by simp [rightStart, rightLen]; omega)).trans
          ((hleftOutside k (by omega)).trans (hpartOutside k hk))
      · dsimp
        refine ⟨rfl, List.Perm.refl _, ?_, ?_, ?_⟩
        · intros
          rfl
        · intro i j hij hj
          omega
        · intro P hall
          exact hall

theorem rangeSorted_take {xs : HeapArray} {n : Nat} (hn : n ≤ xs.length)
    (h : RangeSorted xs 0 n) :
    (xs.take n).Pairwise (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_take]
  have hi' : i < xs.length := by
    have : i < n := by simpa [List.length_take, Nat.min_eq_left hn] using hi
    omega
  have hj' : j < xs.length := by
    have : j < n := by simpa [List.length_take, Nat.min_eq_left hn] using hj
    omega
  rw [← heapArray_get_eq_getElem hi', ← heapArray_get_eq_getElem hj']
  simpa using h i j hij (by simpa [Nat.min_eq_left hn] using hj)

theorem quicksortRangeSpec_perm (xs : HeapArray) (start n : Nat)
    (hbound : start + n ≤ xs.length) :
    List.Perm (quicksortRangeSpec xs start n) xs :=
  (quicksortRangeSpec_correct xs start n hbound).2.1

theorem quicksortRangeSpec_outside (xs : HeapArray) (start n : Nat)
    (hbound : start + n ≤ xs.length) {k : Nat}
    (hk : k < start ∨ start + n ≤ k) :
    HeapArray.get (quicksortRangeSpec xs start n) k = HeapArray.get xs k :=
  (quicksortRangeSpec_correct xs start n hbound).2.2.1 k hk

theorem quicksortRangeSpec_sorted (xs : HeapArray) (start n : Nat)
    (hbound : start + n ≤ xs.length) :
    RangeSorted (quicksortRangeSpec xs start n) start n :=
  (quicksortRangeSpec_correct xs start n hbound).2.2.2.1

theorem quicksortSpec_perm (xs : HeapArray) (n : Nat) (hn : n ≤ xs.length) :
    List.Perm (quicksortSpec xs n) xs := by
  exact quicksortRangeSpec_perm xs 0 n (by omega)

theorem quicksortSpec_sorted_prefix (xs : HeapArray) (n : Nat) (hn : n ≤ xs.length) :
    ((quicksortSpec xs n).take n).Pairwise (· ≤ ·) := by
  apply rangeSorted_take
  · have hlen := (quicksortRangeSpec_correct xs 0 n (by omega)).1
    simpa [quicksortSpec] using (show n ≤ (quicksortRangeSpec xs 0 n).length by omega)
  exact quicksortRangeSpec_sorted xs 0 n (by omega)

theorem quicksortAllSpec_perm (xs : HeapArray) :
    List.Perm (quicksortAllSpec xs) xs := by
  exact quicksortSpec_perm xs xs.length (Nat.le_refl _)

theorem quicksortAllSpec_sorted (xs : HeapArray) :
    (quicksortAllSpec xs).Pairwise (· ≤ ·) := by
  have hlen := (quicksortRangeSpec_correct xs 0 xs.length (by omega)).1
  have hsorted := quicksortSpec_sorted_prefix xs xs.length (Nat.le_refl _)
  have htake : (quicksortRangeSpec xs 0 xs.length).take xs.length =
      quicksortRangeSpec xs 0 xs.length := List.take_of_length_le (by omega)
  simpa [quicksortAllSpec, quicksortSpec, htake] using hsorted


/-! ## Connection to executable blocks -/

def heapRange (heap : Heap) (base : Ptr) (n : Nat) : HeapArray :=
  (List.range n).map fun offset => Heap.read heap ⟨base.addr + offset⟩

@[simp] theorem heapRange_length (heap : Heap) (base : Ptr) (n : Nat) :
    (heapRange heap base n).length = n := by
  simp [heapRange]

theorem heapRange_get (heap : Heap) (base : Ptr) {n i : Nat} (hi : i < n) :
    HeapArray.get (heapRange heap base n) i = Heap.read heap ⟨base.addr + i⟩ := by
  simp [heapRange, HeapArray.get, hi]

theorem heap_read_write_same (heap : Heap) (ptr : Ptr) (value : Nat) :
    Heap.read (Heap.write heap ptr value) ptr = value := by
  simp [Heap.read, Heap.write]

theorem heap_read_write_other (heap : Heap) (written read : Ptr) (value : Nat)
    (h : read ≠ written) :
    Heap.read (Heap.write heap written value) read = Heap.read heap read := by
  rcases written with ⟨written⟩
  rcases read with ⟨read⟩
  have haddr : read ≠ written := by
    intro heq
    apply h
    cases heq
    rfl
  simp [Heap.read, Heap.write, Ne.symm haddr]

def partitionHeapRotate (heap : Heap) (base : Ptr) (pivotIdx i : Nat) : Heap :=
  let pivotPtr : Ptr := ⟨base.addr + pivotIdx⟩
  let currentPtr : Ptr := ⟨base.addr + i⟩
  let pivot := Heap.read heap pivotPtr
  let current := Heap.read heap currentPtr
  let movedCurrent := Heap.write heap pivotPtr current
  let nextPivotPtr : Ptr := ⟨base.addr + pivotIdx + 1⟩
  let shifted := Heap.read movedCurrent nextPivotPtr
  let movedShifted := Heap.write movedCurrent currentPtr shifted
  Heap.write movedShifted nextPivotPtr pivot

def partitionHeapLoopSpec (heap : Heap) (base : Ptr) (n pivotIdx i : Nat) : Heap × Nat :=
  if n ≤ i then (heap, pivotIdx)
  else if Heap.read heap ⟨base.addr + i⟩ < Heap.read heap ⟨base.addr + pivotIdx⟩ then
    partitionHeapLoopSpec (partitionHeapRotate heap base pivotIdx i)
      base n (pivotIdx + 1) (i + 1)
  else
    partitionHeapLoopSpec heap base n pivotIdx (i + 1)
termination_by n - i
decreasing_by all_goals omega

def partitionHeapSpec (heap : Heap) (base : Ptr) (n : Nat) : Heap × Nat :=
  partitionHeapLoopSpec heap base n 0 1

theorem partitionHeapLoopSpec_index (heap : Heap) (base : Ptr) (n pivotIdx i : Nat)
    (hpivotIdx : pivotIdx < i) (hi : i ≤ n) :
    pivotIdx ≤ (partitionHeapLoopSpec heap base n pivotIdx i).2 ∧
      (partitionHeapLoopSpec heap base n pivotIdx i).2 < n := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing heap pivotIdx i with
  | ind measure ih =>
      rw [partitionHeapLoopSpec]
      split
      · simp only [Prod.snd]
        omega
      · split
        · have hrec := ih (n - (i + 1)) (by omega)
            (partitionHeapRotate heap base pivotIdx i) (pivotIdx + 1) (i + 1)
            (by omega) (by omega) rfl
          exact ⟨Nat.le_trans (Nat.le_succ _) hrec.1, hrec.2⟩
        · exact ih (n - (i + 1)) (by omega) heap pivotIdx (i + 1)
            (by omega) (by omega) rfl

def quicksortHeapSpec (heap : Heap) (base : Ptr) (n : Nat) : Heap :=
  if hactive : 1 < n then
    let part := partitionHeapSpec heap base n
    let left := quicksortHeapSpec part.1 base part.2
    quicksortHeapSpec left ⟨base.addr + part.2 + 1⟩ (n - part.2 - 1)
  else heap
termination_by n
decreasing_by
  · exact (partitionHeapLoopSpec_index heap base n 0 1 (by omega) (by omega)).2
  · have hp := (partitionHeapLoopSpec_index heap base n 0 1 (by omega) (by omega)).2
    omega

def HeapRep (heap : Heap) (origin : Ptr) (xs : HeapArray) : Prop :=
  ∀ k, k < xs.length → Heap.read heap ⟨origin.addr + k⟩ = HeapArray.get xs k

theorem heapRep_write {heap : Heap} {origin : Ptr} {xs : HeapArray} (hrep : HeapRep heap origin xs)
    {index value : Nat} (hindex : index < xs.length) :
    HeapRep (Heap.write heap ⟨origin.addr + index⟩ value) origin
      (HeapArray.set xs index value) := by
  intro k hk
  rw [heapArray_length_set] at hk
  rw [heapArray_get_set hindex]
  by_cases hki : k = index
  · subst k
    simp [heap_read_write_same]
  · have hptr : (⟨origin.addr + k⟩ : Ptr) ≠ ⟨origin.addr + index⟩ := by
      intro h
      have haddr := congrArg Ptr.addr h
      simp only at haddr
      omega
    simp [hki, heap_read_write_other _ _ _ _ hptr, hrep k hk]

theorem partitionHeapRotate_rep {heap : Heap} {origin : Ptr} {xs : HeapArray}
    (hrep : HeapRep heap origin xs) (start pivotIdx i : Nat)
    (hpivotIdx : pivotIdx < i) (hi : start + i < xs.length) :
    HeapRep (partitionHeapRotate heap ⟨origin.addr + start⟩ pivotIdx i) origin
      (partitionSwap xs start pivotIdx i) := by
  rw [← partitionRotateSets_eq_swap xs start pivotIdx i hpivotIdx hi]
  have hp : start + pivotIdx < xs.length := by omega
  have hn : start + (pivotIdx + 1) < xs.length := by omega
  simp only [partitionHeapRotate, partitionRotateSets, Nat.add_assoc]
  have hpivot := hrep (start + pivotIdx) hp
  have hcurrent := hrep (start + i) hi
  have hfirst := heapRep_write hrep (index := start + pivotIdx)
    (value := HeapArray.get xs (start + i)) hp
  have hshifted := hfirst (start + (pivotIdx + 1)) (by simp; exact hn)
  have hsecond := heapRep_write hfirst (index := start + i)
    (value := HeapArray.get (HeapArray.set xs (start + pivotIdx)
      (HeapArray.get xs (start + i))) (start + (pivotIdx + 1))) (by simpa using hi)
  have hthird := heapRep_write hsecond (index := start + (pivotIdx + 1))
    (value := HeapArray.get xs (start + pivotIdx)) (by simpa using hn)
  simpa [hpivot, hcurrent, hshifted, Nat.add_assoc] using hthird

theorem partitionHeapLoopSpec_rep {heap : Heap} {origin : Ptr} {xs : HeapArray}
    (hrep : HeapRep heap origin xs) (start n pivotIdx i : Nat)
    (hbound : start + n ≤ xs.length) (hpivotIdx : pivotIdx < i) (hi : i ≤ n) :
    let heapOut := partitionHeapLoopSpec heap ⟨origin.addr + start⟩ n pivotIdx i
    let arrayOut := partitionLoopSpec xs start n pivotIdx i
    HeapRep heapOut.1 origin arrayOut.1 ∧ heapOut.2 = arrayOut.2 := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing heap xs pivotIdx i with
  | ind measure ih =>
      rw [partitionHeapLoopSpec, partitionLoopSpec]
      split <;> rename_i hdone
      · exact ⟨hrep, rfl⟩
      · have hipos : start + i < xs.length := by omega
        have hppos : start + pivotIdx < xs.length := by omega
        have hcurrent : Heap.read heap ⟨(origin.addr + start) + i⟩ =
            HeapArray.get xs (start + i) := by
          simpa [Nat.add_assoc] using hrep (start + i) hipos
        have hpivot : Heap.read heap ⟨(origin.addr + start) + pivotIdx⟩ =
            HeapArray.get xs (start + pivotIdx) := by
          simpa [Nat.add_assoc] using hrep (start + pivotIdx) hppos
        rw [hcurrent, hpivot]
        split <;> rename_i hlt
        · rw [if_pos hlt]
          have hrotate := partitionHeapRotate_rep hrep start pivotIdx i
            (by omega) hipos
          have hlen : (partitionSwap xs start pivotIdx i).length = xs.length := by simp
          exact ih (n - (i + 1)) (by omega)
            (heap := partitionHeapRotate heap ⟨origin.addr + start⟩ pivotIdx i)
            (xs := partitionSwap xs start pivotIdx i) (pivotIdx := pivotIdx + 1)
            (i := i + 1) hrotate (by simpa [hlen] using hbound)
            (by omega) (by omega) rfl
        · rw [if_neg hlt]
          exact ih (n - (i + 1)) (by omega) (heap := heap) (xs := xs)
            (pivotIdx := pivotIdx) (i := i + 1) hrep hbound (by omega) (by omega) rfl

theorem partitionHeapSpec_rep {heap : Heap} {origin : Ptr} {xs : HeapArray}
    (hrep : HeapRep heap origin xs) (start n : Nat)
    (hbound : start + n ≤ xs.length) (hn : 0 < n) :
    let heapOut := partitionHeapSpec heap ⟨origin.addr + start⟩ n
    let arrayOut := partitionRangeSpec xs start n
    HeapRep heapOut.1 origin arrayOut.1 ∧ heapOut.2 = arrayOut.2 := by
  simpa [partitionHeapSpec, partitionRangeSpec] using
    partitionHeapLoopSpec_rep hrep start n 0 1 hbound (by omega) (by omega)

theorem quicksortHeapSpec_rep {heap : Heap} {origin : Ptr} {xs : HeapArray}
    (hrep : HeapRep heap origin xs) (start n : Nat) (hbound : start + n ≤ xs.length) :
    HeapRep (quicksortHeapSpec heap ⟨origin.addr + start⟩ n) origin
      (quicksortRangeSpec xs start n) := by
  induction n using Nat.strongRecOn generalizing heap xs start with
  | ind n ih =>
      rw [quicksortHeapSpec, quicksortRangeSpec]
      split <;> rename_i hactive
      · let heapPart := partitionHeapSpec heap ⟨origin.addr + start⟩ n
        let arrayPart := partitionRangeSpec xs start n
        have hpart := partitionHeapSpec_rep hrep start n hbound (by omega)
        change HeapRep heapPart.1 origin arrayPart.1 ∧ heapPart.2 = arrayPart.2 at hpart
        have hp : heapPart.2 < n :=
          (partitionHeapLoopSpec_index heap ⟨origin.addr + start⟩ n 0 1
            (by omega) (by omega)).2
        have harrayLen : arrayPart.1.length = xs.length := by
          exact (partitionRangeSpec_correct xs start n hbound (by omega)).1
        let leftHeap := quicksortHeapSpec heapPart.1 ⟨origin.addr + start⟩ heapPart.2
        let leftArray := quicksortRangeSpec arrayPart.1 start heapPart.2
        have hleft := ih heapPart.2 hp (heap := heapPart.1) (xs := arrayPart.1)
          (start := start) hpart.1 (by
          rw [harrayLen]
          omega)
        change HeapRep leftHeap origin leftArray at hleft
        have hleftLen : leftArray.length = arrayPart.1.length :=
          (quicksortRangeSpec_correct arrayPart.1 start heapPart.2 (by
            rw [harrayLen]
            omega)).1
        have hright := ih (n - heapPart.2 - 1) (by omega) (heap := leftHeap)
          (xs := leftArray) (start := start + heapPart.2 + 1) hleft (by
            rw [hleftLen, harrayLen]
            omega)
        simpa [heapPart, arrayPart, leftHeap, leftArray, hpart.2, Nat.add_assoc] using hright
      · exact hrep

theorem quicksortHeapSpec_range (heap : Heap) (base : Ptr) (n : Nat) :
    heapRange (quicksortHeapSpec heap base n) base n =
      quicksortRangeSpec (heapRange heap base n) 0 n := by
  let xs := heapRange heap base n
  have hrep : HeapRep heap base xs := by
    intro k hk
    symm
    exact heapRange_get heap base (by simpa [xs] using hk)
  have hout := quicksortHeapSpec_rep hrep 0 n (by simp [xs])
  apply List.ext_getElem
  · have hlen := (quicksortRangeSpec_correct xs 0 n (by simp [xs])).1
    simpa [xs] using hlen.symm
  intro k hkLeft hkRight
  rw [← heapArray_get_eq_getElem (by simpa using hkLeft),
    ← heapArray_get_eq_getElem (by simpa using hkRight)]
  rw [heapRange_get _ _ (by simpa using hkLeft)]
  exact hout k (by
    have hlen := (quicksortRangeSpec_correct xs 0 n (by simp [xs])).1
    rw [hlen]
    simpa [xs] using hkLeft)

theorem partitionHeapRotate_outside (heap : Heap) (base : Ptr) (n pivotIdx i : Nat)
    (hpivotIdx : pivotIdx < i) (hi : i < n) {ptr : Ptr}
    (hout : ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr) :
    Heap.read (partitionHeapRotate heap base pivotIdx i) ptr = Heap.read heap ptr := by
  unfold partitionHeapRotate
  rw [heap_read_write_other, heap_read_write_other, heap_read_write_other]
  all_goals
    intro heq
    have haddr := congrArg Ptr.addr heq
    simp only at haddr
    omega

theorem partitionHeapLoopSpec_outside (heap : Heap) (base : Ptr) (n pivotIdx i : Nat)
    (hpivotIdx : pivotIdx < i) (hi : i ≤ n) {ptr : Ptr}
    (hout : ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr) :
    Heap.read (partitionHeapLoopSpec heap base n pivotIdx i).1 ptr = Heap.read heap ptr := by
  induction hmeasure : n - i using Nat.strongRecOn generalizing heap pivotIdx i with
  | ind measure ih =>
      rw [partitionHeapLoopSpec]
      split
      · rfl
      · split
        · exact (ih (n - (i + 1)) (by omega)
            (partitionHeapRotate heap base pivotIdx i) (pivotIdx + 1) (i + 1)
            (by omega) (by omega) rfl).trans
              (partitionHeapRotate_outside heap base n pivotIdx i (by omega) (by omega) hout)
        · exact ih (n - (i + 1)) (by omega) heap pivotIdx (i + 1)
            (by omega) (by omega) rfl

theorem partitionHeapSpec_outside (heap : Heap) (base : Ptr) (n : Nat) (hn : 0 < n)
    {ptr : Ptr} (hout : ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr) :
    Heap.read (partitionHeapSpec heap base n).1 ptr = Heap.read heap ptr := by
  exact partitionHeapLoopSpec_outside heap base n 0 1 (by omega) (by omega) hout

theorem quicksortHeapSpec_outside (heap : Heap) (base : Ptr) (n : Nat) {ptr : Ptr}
    (hout : ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr) :
    Heap.read (quicksortHeapSpec heap base n) ptr = Heap.read heap ptr := by
  induction n using Nat.strongRecOn generalizing heap base with
  | ind n ih =>
      rw [quicksortHeapSpec]
      split <;> rename_i hactive
      · let part := partitionHeapSpec heap base n
        have hp : part.2 < n :=
          (partitionHeapLoopSpec_index heap base n 0 1 (by omega) (by omega)).2
        let left := quicksortHeapSpec part.1 base part.2
        calc
          Heap.read
              (quicksortHeapSpec left ⟨base.addr + part.2 + 1⟩ (n - part.2 - 1)) ptr =
              Heap.read left ptr := ih (n - part.2 - 1) (by omega) left
                ⟨base.addr + part.2 + 1⟩ (by dsimp; omega)
          _ = Heap.read part.1 ptr := ih part.2 hp part.1 base (by omega)
          _ = Heap.read heap ptr := partitionHeapSpec_outside heap base n (by omega) hout
      · rfl

/-- Universal correctness of the exact heap model used by the embedded program. -/
theorem quicksortHeapSpec_correct (heap : Heap) (base : Ptr) (n : Nat) :
    let final := quicksortHeapSpec heap base n
    List.Perm (heapRange final base n) (heapRange heap base n) ∧
      (heapRange final base n).Pairwise (· ≤ ·) ∧
      (∀ ptr, ptr.addr < base.addr ∨ base.addr + n ≤ ptr.addr →
        Heap.read final ptr = Heap.read heap ptr) := by
  let xs := heapRange heap base n
  have hrange := quicksortHeapSpec_range heap base n
  have hspec : quicksortRangeSpec xs 0 n = quicksortAllSpec xs := by
    simp [quicksortAllSpec, quicksortSpec, xs]
  dsimp only
  rw [hrange, hspec]
  exact ⟨quicksortAllSpec_perm xs, quicksortAllSpec_sorted xs,
    fun _ hout => quicksortHeapSpec_outside heap base n hout⟩



end Zag.Test.Autocorres.Examples
