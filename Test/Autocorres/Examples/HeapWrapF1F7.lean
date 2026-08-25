import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`HeapWrap.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/HeapWrap.thy).

`thing` occupies four Nat cells (`x`, `p`, `left`, `right`) and `list` occupies two (`x`, `p`).
This covers all eight upstream access/update shapes and short-circuit control flow. C typed-heap
overloading, signed/unsigned 64-bit interpretation, casts, and by-value structure ABI behavior are
not represented by `PeanoHeap`; `heapWrapF5PointerCopy` consequently specifies a pointer-source
copy rather than the C by-value call.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev heapWrapBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    heapWrapF1(thing : Ptr) : Unit {
      pField := op "ptrAdd"[thing, nat(1)];
      targetAddr := op "load"[pField];
      target := op "ptrOfNat"[targetAddr];
      ret op "store"[target, nat(42)]
    },
    heapWrapF2(thing : Ptr) : Unit {
      ret op "store"[thing, nat(42)]
    },
    heapWrapF3(thing : Ptr) : Unit {
      leftField := op "ptrAdd"[thing, nat(2)];
      leftAddr := op "load"[leftField];
      rightAddr := op "add"[leftAddr, nat(4)];
      rightField := op "ptrAdd"[thing, nat(3)];
      ret op "store"[rightField, rightAddr]
    },
    heapWrapF4(thing : Ptr) : Unit {
      leftField := op "ptrAdd"[thing, nat(2)];
      thingAddr := op "ptrAddr"[thing];
      ret op "store"[leftField, thingAddr]
    },
    heapWrapF5PointerCopy(dst : Ptr, src : Ptr) : Unit {
      x := op "load"[src];
      srcP := op "ptrAdd"[src, nat(1)];
      p := op "load"[srcP];
      srcLeft := op "ptrAdd"[src, nat(2)];
      left := op "load"[srcLeft];
      srcRight := op "ptrAdd"[src, nat(3)];
      right := op "load"[srcRight];
      storedX := op "store"[dst, x];
      dstP := op "ptrAdd"[dst, nat(1)];
      storedP := op "store"[dstP, p];
      dstLeft := op "ptrAdd"[dst, nat(2)];
      storedLeft := op "store"[dstLeft, left];
      dstRight := op "ptrAdd"[dst, nat(3)];
      ret op "store"[dstRight, right]
    },
    heapWrapF6(ptr : Ptr) : Unit {
      ret op "store"[ptr, nat(42)]
    },
    heapWrapF7(ptr : Ptr) : Unit {
      ret op "store"[ptr, nat(42)]
    },
    heapWrapF8(list : Ptr, thing : Ptr) : Nat {
      listPField := op "ptrAdd"[list, nat(1)];
      listThingAddr := op "load"[listPField];
      listThing := op "ptrOfNat"[listThingAddr];
      lhs := op "load"[listThing];
      lhsZero := op "eq"[lhs, nat(0)];
      ret if lhsZero { nat(0) } else { call heapWrapF8Rhs [thing] }
    },
    heapWrapF8Rhs(thing : Ptr) : Nat {
      leftField := op "ptrAdd"[thing, nat(2)];
      leftAddr := op "load"[leftField];
      left := op "ptrOfNat"[leftAddr];
      rightField := op "ptrAdd"[left, nat(3)];
      rightAddr := op "load"[rightField];
      right := op "ptrOfNat"[rightAddr];
      value := op "load"[right];
      zero := op "eq"[value, nat(0)];
      ret if zero { nat(0) } else { nat(1) }
    }
  ]

theorem heapWrapBlocksValid : BlockCtx.Valid heapWrapBlocks := by
  valid_blocks [heapWrapBlocks]

abbrev heapWrapCtx : Ctx := mkCtx heapWrapBlocks heapWrapBlocksValid

theorem heapWrapCtx_wellTyped : Ctx.WellTyped heapWrapCtx := by
  typecheck_ctx

private abbrev heapWrapStateCtx : Ctx := heapStateCtx heapWrapBlocks heapWrapBlocksValid

def thingField (thing : Ptr) (offset : Nat) : Ptr :=
  ⟨thing.addr + offset⟩

def ObjectValid (heap : Heap) (ptr : Ptr) (cells : Nat) : Prop :=
  ptr ≠ null ∧ ptr.addr + cells ≤ heap.next

def ThingRep (heap : Heap) (thing : Ptr) (x p left right : Nat) : Prop :=
  ObjectValid heap thing 4 ∧
  Heap.read heap (thingField thing 0) = x ∧
  Heap.read heap (thingField thing 1) = p ∧
  Heap.read heap (thingField thing 2) = left ∧
  Heap.read heap (thingField thing 3) = right

def ListStructRep (heap : Heap) (list : Ptr) (x p : Nat) : Prop :=
  ObjectValid heap list 2 ∧ Heap.read heap list = x ∧
    Heap.read heap (thingField list 1) = p

def HeapWrapF1Pre (heap : Heap) (thing : Ptr) : Prop :=
  ObjectValid heap thing 4 ∧
    ObjectValid heap ⟨Heap.read heap (thingField thing 1)⟩ 1

def HeapWrapF8Pre (heap : Heap) (list thing : Ptr) : Prop :=
  let listTarget := ⟨Heap.read heap (thingField list 1)⟩
  let left := ⟨Heap.read heap (thingField thing 2)⟩
  let right := ⟨Heap.read heap (thingField left 3)⟩
  ObjectValid heap list 2 ∧ ObjectValid heap listTarget 2 ∧
    (Heap.read heap listTarget ≠ 0 →
      ObjectValid heap thing 4 ∧ ObjectValid heap left 4 ∧ ObjectValid heap right 4)

theorem thing_fields_have_distinct_addresses (thing : Ptr) :
    (thingField thing 0).addr ≠ (thingField thing 1).addr ∧
    (thingField thing 1).addr ≠ (thingField thing 2).addr ∧
    (thingField thing 2).addr ≠ (thingField thing 3).addr := by
  simp [thingField]

theorem ThingRep.field_values {heap : Heap} {thing : Ptr} {x p left right : Nat}
    (h : ThingRep heap thing x p left right) :
    Heap.read heap thing = x ∧
    Heap.read heap (thingField thing 1) = p ∧
    Heap.read heap (thingField thing 2) = left ∧
    Heap.read heap (thingField thing 3) = right := by
  simpa [ThingRep, thingField] using h.2

def thingContents (x p left right : Nat) : Nat → Nat
| 0 => x
| 1 => p
| 2 => left
| _ => right

def thingSegment (thing : Ptr) (x p left right : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  segment thing.addr 4 (thingContents x p left right)

theorem thingSegment_holds (heap : Heap) (thing : Ptr) (x p left right : Nat) :
    (thingSegment thing x p left right).holds heap ↔
      Heap.read heap thing = x ∧
      Heap.read heap (thingField thing 1) = p ∧
      Heap.read heap (thingField thing 2) = left ∧
      Heap.read heap (thingField thing 3) = right := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [thingSegment, segment, thingContents, thingField] using h 0 (by omega)
    · simpa [thingSegment, segment, thingContents, thingField] using h 1 (by omega)
    · simpa [thingSegment, segment, thingContents, thingField] using h 2 (by omega)
    · simpa [thingSegment, segment, thingContents, thingField] using h 3 (by omega)
  · rintro ⟨hx, hp, hleft, hright⟩ i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa [thingSegment, segment, thingContents, thingField] using hx
    · simpa [thingSegment, segment, thingContents, thingField] using hp
    · simpa [thingSegment, segment, thingContents, thingField] using hleft
    · simpa [thingSegment, segment, thingContents, thingField] using hright

private theorem pointsTo_sep_write_second (heap : Heap) (p q : Ptr)
    (vp vq new : Nat) :
    ((p ↦ vp) ∗ (q ↦ vq)).holds heap →
      ((p ↦ vp) ∗ (q ↦ new)).holds (Heap.write heap q new) := by
  intro hpq
  rcases hpq with ⟨hdisj, hp, _hq⟩
  refine ⟨hdisj, ?_, ?_⟩
  · rw [cell_pointsTo_holds] at hp ⊢
    have hne : p.addr ≠ q.addr := by
      intro heq
      have hpMem : p.addr ∈ (p ↦ vp).region := by
        simp [pointsToVal, HProp.pointsTo, HeapAlgebra.span, cell,
          HeapAlgebra.Peano.OwnedPtr.span]
      have hqMem : q.addr ∈ (q ↦ vq).region := by
        simp [pointsToVal, HProp.pointsTo, HeapAlgebra.span, cell,
          HeapAlgebra.Peano.OwnedPtr.span]
      exact Set.disjoint_left.mp hdisj hpMem (by simpa [heq] using hqMem)
    exact (HeapAlgebra.Peano.Heap.read_write_of_ne heap q p new hne).trans hp
  · rw [cell_pointsTo_holds]
    exact HeapAlgebra.Peano.Heap.read_write_same heap q new

private theorem thingSegment_addr_ne_of_sep {heap : Heap} {dst src : Ptr}
    {dx dp dl dr sx sp sl sr i j : Nat}
    (hp : ((thingSegment dst dx dp dl dr) ∗
      (thingSegment src sx sp sl sr)).holds heap)
    (hi : i < 4) (hj : j < 4) :
    (thingField src i).addr ≠ (thingField dst j).addr := by
  have hdst : (thingField dst j).addr ∈ (thingSegment dst dx dp dl dr).region := by
    simp [thingSegment, segment, range, thingField]
    omega
  have hsrc : (thingField src i).addr ∈ (thingSegment src sx sp sl sr).region := by
    simp [thingSegment, segment, range, thingField]
    omega
  intro heq
  exact Set.disjoint_left.mp hp.1 hdst (by simpa [heq] using hsrc)

def heapWrapF1Model (heap : Heap) (thing : Ptr) : Heap :=
  Heap.write heap ⟨Heap.read heap (thingField thing 1)⟩ 42

def heapWrapF2Model (heap : Heap) (thing : Ptr) : Heap :=
  Heap.write heap thing 42

def heapWrapF3Model (heap : Heap) (thing : Ptr) : Heap :=
  Heap.write heap (thingField thing 3) (Heap.read heap (thingField thing 2) + 4)

def heapWrapF4Model (heap : Heap) (thing : Ptr) : Heap :=
  Heap.write heap (thingField thing 2) thing.addr

def heapWrapF5Model (heap : Heap) (dst src : Ptr) : Heap :=
  let h0 := Heap.write heap dst (Heap.read heap src)
  let h1 := Heap.write h0 (thingField dst 1) (Heap.read heap (thingField src 1))
  let h2 := Heap.write h1 (thingField dst 2) (Heap.read heap (thingField src 2))
  Heap.write h2 (thingField dst 3) (Heap.read heap (thingField src 3))

private theorem thingSegment_source_read_after_copy {heap : Heap} {dst src : Ptr}
    {dx dp dl dr sx sp sl sr i : Nat}
    (hp : ((thingSegment dst dx dp dl dr) ∗
      (thingSegment src sx sp sl sr)).holds heap)
    (hi : i < 4) :
    Heap.read (heapWrapF5Model heap dst src) (thingField src i) =
      Heap.read heap (thingField src i) := by
  have hne0 : (thingField src i).addr ≠ dst.addr := by
    simpa [thingField] using thingSegment_addr_ne_of_sep (heap := heap)
      (dst := dst) (src := src) (dx := dx) (dp := dp) (dl := dl) (dr := dr)
      (sx := sx) (sp := sp) (sl := sl) (sr := sr) (i := i) (j := 0) hp hi (by omega)
  have hne1 : (thingField src i).addr ≠ (thingField dst 1).addr :=
    thingSegment_addr_ne_of_sep (heap := heap) (dst := dst) (src := src)
      (dx := dx) (dp := dp) (dl := dl) (dr := dr)
      (sx := sx) (sp := sp) (sl := sl) (sr := sr) (i := i) (j := 1) hp hi (by omega)
  have hne2 : (thingField src i).addr ≠ (thingField dst 2).addr :=
    thingSegment_addr_ne_of_sep (heap := heap) (dst := dst) (src := src)
      (dx := dx) (dp := dp) (dl := dl) (dr := dr)
      (sx := sx) (sp := sp) (sl := sl) (sr := sr) (i := i) (j := 2) hp hi (by omega)
  have hne3 : (thingField src i).addr ≠ (thingField dst 3).addr :=
    thingSegment_addr_ne_of_sep (heap := heap) (dst := dst) (src := src)
      (dx := dx) (dp := dp) (dl := dl) (dr := dr)
      (sx := sx) (sp := sp) (sl := sl) (sr := sr) (i := i) (j := 3) hp hi (by omega)
  simp [heapWrapF5Model,
    HeapAlgebra.Peano.Heap.read_write_of_ne _ (thingField dst 3) (thingField src i) _ hne3,
    HeapAlgebra.Peano.Heap.read_write_of_ne _ (thingField dst 2) (thingField src i) _ hne2,
    HeapAlgebra.Peano.Heap.read_write_of_ne _ (thingField dst 1) (thingField src i) _ hne1,
    HeapAlgebra.Peano.Heap.read_write_of_ne _ dst (thingField src i) _ hne0]

def heapWrapF6Model (heap : Heap) (ptr : Ptr) : Heap :=
  Heap.write heap ptr 42

def heapWrapF7Model (heap : Heap) (ptr : Ptr) : Heap :=
  Heap.write heap ptr 42

def heapWrapF8Model (heap : Heap) (list thing : Ptr) : Nat :=
  let listThing := ⟨Heap.read heap (thingField list 1)⟩
  if Heap.read heap listThing = 0 then 0
  else
    let left := ⟨Heap.read heap (thingField thing 2)⟩
    let right := ⟨Heap.read heap (thingField left 3)⟩
    if Heap.read heap right = 0 then 0 else 1

theorem heapWrapF8_short_circuits (heap : Heap) (list thing : Ptr)
    (h : Heap.read heap ⟨Heap.read heap (thingField list 1)⟩ = 0) :
    heapWrapF8Model heap list thing = 0 := by
  simp [heapWrapF8Model, h]

private theorem heapWrapF1_evaluates (heap : Heap) (thing : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF1" [termPtr thing.addr]
      heap valUnit (heapWrapF1Model heap thing) := by
  have hblock : (checkedBlocks heapWrapBlocks heapWrapBlocksValid).get? "heapWrapF1" =
      some heapWrapBlocks[0].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, heapWrapBlocks]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel
    (Machine.stateCtx heapCtx heapOpCtx (checkedBlocks heapWrapBlocks heapWrapBlocksValid)) 50
    (Machine.start [] (.call "heapWrapF1" [termPtr thing.addr]))).run heap) = _
  set_option linter.unusedSimpArgs false in
    repeat
      rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
      first
      | rw [storeOp_step]
        simp [heapWrapF1Model, thingField]
      | rw [loadOp_step]
        simp
      | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
          Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
          Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
          Machine.enterInstrs, Machine.driveOp, Machine.start, hblock, hload,
          hstore, hptrAdd, hptrOfNat, Machine.stateM_pure_run, loadOp, storeOp,
          ptrAddOp, ptrOfNatOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
          Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
          Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
  simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
    OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
    StateT.pure, Id.run]

private theorem heapWrapF2_evaluates (heap : Heap) (thing : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF2" [termPtr thing.addr]
      heap valUnit (heapWrapF2Model heap thing) := by
  rcases thing with ⟨thing⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [heapWrapBlocks, checkedBlocks, storeOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
      termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat, Val.mk_ofNat,
      Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, resume_store_value_operand,
      storeValAction_spec, storeOp_action_spec, storeOp_action_vals]
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]
  all_goals try solve_by_elim
  all_goals try obtain ⟨hleft, hright⟩ := ‹_ ∧ _›
  all_goals subst_vars
  all_goals try simp_all [heapWrapF2Model, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]

private theorem heapWrapF3_evaluates (heap : Heap) (thing : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF3" [termPtr thing.addr]
      heap valUnit (heapWrapF3Model heap thing) := by
  have hblock : (checkedBlocks heapWrapBlocks heapWrapBlocksValid).get? "heapWrapF3" =
      some heapWrapBlocks[2].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, heapWrapBlocks]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hadd : heapOpCtx.get? "add" = some (Op.natBinary Nat.add) := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel
    (Machine.stateCtx heapCtx heapOpCtx (checkedBlocks heapWrapBlocks heapWrapBlocksValid)) 70
    (Machine.start [] (.call "heapWrapF3" [termPtr thing.addr]))).run heap) = _
  set_option linter.unusedSimpArgs false in
    repeat
      rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
      first
      | rw [storeOp_step]
        simp [heapWrapF3Model, thingField]
      | rw [loadOp_step]
        simp
      | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
          Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
          Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
          Machine.enterInstrs, Machine.driveOp, Machine.start, hblock, hload,
          hstore, hptrAdd, hadd, Machine.stateM_pure_run, loadOp, storeOp,
          ptrAddOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
          Op.ofVals, Op.Body.eager, Op.fixed, Op.natBinary, Block.entryEnv,
          Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
  simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
    OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
    StateT.pure, Id.run]

private theorem heapWrapF4_evaluates (heap : Heap) (thing : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF4" [termPtr thing.addr]
      heap valUnit (heapWrapF4Model heap thing) := by
  rcases thing with ⟨thing⟩
  let blocks := checkedBlocks heapWrapBlocks heapWrapBlocksValid
  have hstore := store_apply_evaluates blocks heap ⟨thing + 2⟩ thing
  set_option zvcgen.useLocalApply true in
    set_option zvcgen.resumeReturn true in
      zvcgen [heapWrapBlocks, blocks, Term.nat, termPtr, valPtr]
  all_goals subst_vars
  all_goals simp_all [heapWrapF4Model, thingField, EvalTriple.Singleton.statePre,
    EvalTriple.Singleton.statePost]

private theorem heapWrapF5_evaluates (heap : Heap) (dst src : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF5PointerCopy"
      [termPtr dst.addr, termPtr src.addr] heap valUnit (heapWrapF5Model heap dst src) := by
  have hblock :
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid).get? "heapWrapF5PointerCopy" =
        some heapWrapBlocks[4].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, heapWrapBlocks]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel
    (Machine.stateCtx heapCtx heapOpCtx (checkedBlocks heapWrapBlocks heapWrapBlocksValid)) 130
    (Machine.start [] (.call "heapWrapF5PointerCopy"
      [termPtr dst.addr, termPtr src.addr]))).run heap) = _
  set_option linter.unusedSimpArgs false in
    repeat
      rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
      first
      | rw [storeOp_step]
        simp [heapWrapF5Model, thingField]
      | rw [loadOp_step]
        simp
      | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
          Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
          Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
          Machine.enterInstrs, Machine.driveOp, Machine.start, hblock, hload,
          hstore, hptrAdd, Machine.stateM_pure_run, loadOp, storeOp, ptrAddOp,
          Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
          Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat, termPtr,
          valPtr, valUnit, asPtr?]
  simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
    OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
    StateT.pure, Id.run]

private theorem heapWrapF6_evaluates (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF6" [termPtr ptr.addr]
      heap valUnit (heapWrapF6Model heap ptr) := by
  rcases ptr with ⟨ptr⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [heapWrapBlocks, checkedBlocks, storeOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
      termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat, Val.mk_ofNat,
      Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, resume_store_value_operand,
      storeValAction_spec, storeOp_action_spec, storeOp_action_vals]
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]
  all_goals try solve_by_elim
  all_goals try obtain ⟨hleft, hright⟩ := ‹_ ∧ _›
  all_goals subst_vars
  all_goals try simp_all [heapWrapF6Model, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]

private theorem heapWrapF7_evaluates (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF7" [termPtr ptr.addr]
      heap valUnit (heapWrapF7Model heap ptr) := by
  rcases ptr with ⟨ptr⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [heapWrapBlocks, checkedBlocks, storeOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
      termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat, Val.mk_ofNat,
      Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, resume_store_value_operand,
      storeValAction_spec, storeOp_action_spec, storeOp_action_vals]
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]
  all_goals try solve_by_elim
  all_goals try obtain ⟨hleft, hright⟩ := ‹_ ∧ _›
  all_goals subst_vars
  all_goals try simp_all [heapWrapF7Model, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]

/-
```
{ thing+1 ↦ target.addr ∗ target ↦ old }
  heapWrapF1(thing)
{ thing+1 ↦ target.addr ∗ target ↦ 42 }
```
-/
@[zspec] theorem heapWrapF1_spec (thing target : Ptr) (old : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF1" [termPtr thing.addr]
      (HProp.toAssertion ((thingField thing 1 ↦ target.addr) ∗ (target ↦ old)))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧
          (((thingField thing 1 ↦ target.addr) ∗ (target ↦ 42)).holds final)⌝) :=
  evaluatesCall_of_hprop "heapWrapF1" _
    ((thingField thing 1 ↦ target.addr) ∗ (target ↦ old))
    (fun _ => (thingField thing 1 ↦ target.addr) ∗ (target ↦ 42))
    valUnit
    (fun h => heapWrapF1Model h thing)
    (fun h => heapWrapF1_evaluates h thing)
    (fun h hp => by
      have htarget : Heap.read h (thingField thing 1) = target.addr :=
        (cell_pointsTo_holds (thingField thing 1) target.addr h).1 hp.2.1
      simpa [heapWrapF1Model, htarget] using
        pointsTo_sep_write_second h (thingField thing 1) target target.addr old 42 hp)

/--
```
{ thing ↦ old }
  heapWrapF2(thing)
{ thing ↦ 42 }
```
-/
@[zspec] theorem heapWrapF2_spec (thing : Ptr) (old : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF2" [termPtr thing.addr]
      (HProp.toAssertion (thing ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (thing ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop "heapWrapF2" _
    (thing ↦ old)
    (fun _ => thing ↦ 42)
    valUnit
    (fun h => Heap.write h thing 42)
    (fun h => by simpa [heapWrapF2Model] using heapWrapF2_evaluates h thing)
    (fun h _hp =>
      (cell_pointsTo_holds thing 42 (Heap.write h thing 42)).2
        (by simp [Heap.read, Heap.write]))

/-
```
{ segment thing 4 [x, p, left, oldRight] }
  heapWrapF3(thing)
{ segment thing 4 [x, p, left, left + 4] }
```
-/
@[zspec] theorem heapWrapF3_spec (thing : Ptr) (x p left oldRight : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF3" [termPtr thing.addr]
      (HProp.toAssertion (thingSegment thing x p left oldRight))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (thingSegment thing x p left (left + 4)).holds final⌝) :=
  evaluatesCall_of_hprop "heapWrapF3" _
    (thingSegment thing x p left oldRight)
    (fun _ => thingSegment thing x p left (left + 4))
    valUnit
    (fun h => heapWrapF3Model h thing)
    (fun h => heapWrapF3_evaluates h thing)
    (fun h hp => by
      rcases (thingSegment_holds h thing x p left oldRight).1 hp with
        ⟨hx, hpField, hleft, _hright⟩
      apply (thingSegment_holds _ thing x p left (left + 4)).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (by
          rw [heapWrapF3Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 3)
            thing (Heap.read h (thingField thing 2) + 4) (by simp [thingField])).trans hx)
      · exact (by
          rw [heapWrapF3Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 3)
            (thingField thing 1) (Heap.read h (thingField thing 2) + 4)
            (by simp [thingField])).trans hpField)
      · exact (by
          rw [heapWrapF3Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 3)
            (thingField thing 2) (Heap.read h (thingField thing 2) + 4)
            (by simp [thingField])).trans hleft)
      · rw [heapWrapF3Model]
        simpa [hleft] using HeapAlgebra.Peano.Heap.read_write_same h
          (thingField thing 3) (Heap.read h (thingField thing 2) + 4))

/-
```
{ segment thing 4 [x, p, oldLeft, right] }
  heapWrapF4(thing)
{ segment thing 4 [x, p, thing.addr, right] }
```
-/
@[zspec] theorem heapWrapF4_spec (thing : Ptr) (x p oldLeft right : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF4" [termPtr thing.addr]
      (HProp.toAssertion (thingSegment thing x p oldLeft right))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (thingSegment thing x p thing.addr right).holds final⌝) :=
  evaluatesCall_of_hprop "heapWrapF4" _
    (thingSegment thing x p oldLeft right)
    (fun _ => thingSegment thing x p thing.addr right)
    valUnit
    (fun h => heapWrapF4Model h thing)
    (fun h => heapWrapF4_evaluates h thing)
    (fun h hp => by
      rcases (thingSegment_holds h thing x p oldLeft right).1 hp with
        ⟨hx, hpField, _hleft, hright⟩
      apply (thingSegment_holds _ thing x p thing.addr right).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (by
          rw [heapWrapF4Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 2)
            thing thing.addr (by simp [thingField])).trans hx)
      · exact (by
          rw [heapWrapF4Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 2)
            (thingField thing 1) thing.addr (by simp [thingField])).trans hpField)
      · rw [heapWrapF4Model]
        exact HeapAlgebra.Peano.Heap.read_write_same h (thingField thing 2) thing.addr
      · exact (by
          rw [heapWrapF4Model]
          exact (HeapAlgebra.Peano.Heap.read_write_of_ne h (thingField thing 2)
            (thingField thing 3) thing.addr (by simp [thingField])).trans hright))

@[zspec] theorem heapWrapF5PointerCopy_spec (dst src : Ptr)
    (dx dp dl dr sx sp sl sr : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF5PointerCopy"
      [termPtr dst.addr, termPtr src.addr]
      (HProp.toAssertion ((thingSegment dst dx dp dl dr) ∗
        (thingSegment src sx sp sl sr)))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧
          (((thingSegment dst sx sp sl sr) ∗
            (thingSegment src sx sp sl sr)).holds final)⌝) :=
  evaluatesCall_of_hprop "heapWrapF5PointerCopy" _
    ((thingSegment dst dx dp dl dr) ∗ (thingSegment src sx sp sl sr))
    (fun _ => (thingSegment dst sx sp sl sr) ∗ (thingSegment src sx sp sl sr))
    valUnit
    (fun h => heapWrapF5Model h dst src)
    (fun h => heapWrapF5_evaluates h dst src)
    (fun h hp => by
      rcases hp with ⟨hdisj, hdst, hsrc⟩
      rcases (thingSegment_holds h src sx sp sl sr).1 hsrc with
        ⟨hsx, hsp, hsl, hsr⟩
      have hreadSrc (i : Nat) (hi : i < 4) :
          Heap.read (heapWrapF5Model h dst src) (thingField src i) =
            Heap.read h (thingField src i) := by
        exact thingSegment_source_read_after_copy (heap := h) (dst := dst) (src := src)
          (dx := dx) (dp := dp) (dl := dl) (dr := dr)
          (sx := sx) (sp := sp) (sl := sl) (sr := sr) (i := i)
          ⟨hdisj, hdst, hsrc⟩ hi
      refine ⟨by simpa [thingSegment, segment] using hdisj, ?_, ?_⟩
      · apply (thingSegment_holds _ dst sx sp sl sr).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · calc
            Heap.read (heapWrapF5Model h dst src) dst = Heap.read h src := by
              simp [heapWrapF5Model, thingField,
                HeapAlgebra.Peano.Heap.read_write_same,
                HeapAlgebra.Peano.Heap.read_write_of_ne]
            _ = sx := hsx
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField dst 1) =
                Heap.read h (thingField src 1) := by
              simp [heapWrapF5Model, thingField,
                HeapAlgebra.Peano.Heap.read_write_same,
                HeapAlgebra.Peano.Heap.read_write_of_ne]
            _ = sp := hsp
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField dst 2) =
                Heap.read h (thingField src 2) := by
              simp [heapWrapF5Model, thingField,
                HeapAlgebra.Peano.Heap.read_write_same,
                HeapAlgebra.Peano.Heap.read_write_of_ne]
            _ = sl := hsl
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField dst 3) =
                Heap.read h (thingField src 3) := by
              simp [heapWrapF5Model, thingField,
                HeapAlgebra.Peano.Heap.read_write_same,
                HeapAlgebra.Peano.Heap.read_write_of_ne]
            _ = sr := hsr
      · apply (thingSegment_holds _ src sx sp sl sr).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · calc
            Heap.read (heapWrapF5Model h dst src) src =
                Heap.read (heapWrapF5Model h dst src) (thingField src 0) := by simp [thingField]
            _ = Heap.read h (thingField src 0) := hreadSrc 0 (by omega)
            _ = sx := by simpa [thingField] using hsx
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField src 1) =
                Heap.read h (thingField src 1) := hreadSrc 1 (by omega)
            _ = sp := hsp
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField src 2) =
                Heap.read h (thingField src 2) := hreadSrc 2 (by omega)
            _ = sl := hsl
        · calc
            Heap.read (heapWrapF5Model h dst src) (thingField src 3) =
                Heap.read h (thingField src 3) := hreadSrc 3 (by omega)
            _ = sr := hsr)

/--
```
{ ptr ↦ old }
  heapWrapF6(ptr)
{ ptr ↦ 42 }
```
-/
@[zspec] theorem heapWrapF6_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF6" [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (ptr ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop "heapWrapF6" _
    (ptr ↦ old)
    (fun _ => ptr ↦ 42)
    valUnit
    (fun h => Heap.write h ptr 42)
    (fun h => by simpa [heapWrapF6Model] using heapWrapF6_evaluates h ptr)
    (fun h _hp =>
      (cell_pointsTo_holds ptr 42 (Heap.write h ptr 42)).2
        (by simp [Heap.read, Heap.write]))

/--
```
{ ptr ↦ old }
  heapWrapF7(ptr)
{ ptr ↦ 42 }
```
-/
@[zspec] theorem heapWrapF7_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall heapWrapStateCtx "heapWrapF7" [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (ptr ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop "heapWrapF7" _
    (ptr ↦ old)
    (fun _ => ptr ↦ 42)
    valUnit
    (fun h => Heap.write h ptr 42)
    (fun h => by simpa [heapWrapF7Model] using heapWrapF7_evaluates h ptr)
    (fun h _hp =>
      (cell_pointsTo_holds ptr 42 (Heap.write h ptr 42)).2
        (by simp [Heap.read, Heap.write]))

theorem heapWrapF5_run :
    (match (Machine.evalFuel heapWrapCtx 100 []
        (.call "heapWrapF5PointerCopy" [termPtr 5, termPtr 1])).run
          { next := 9, cells := [(1, 10), (2, 20), (3, 30), (4, 40)] } with
      | (some _, final) => some final
      | (none, _) => none) =
    some (heapWrapF5Model
      { next := 9, cells := [(1, 10), (2, 20), (3, 30), (4, 40)] } ⟨5⟩ ⟨1⟩) := by
  native_decide

end Zag.Test.Autocorres.Examples
