import Test.Autocorres.Examples.HeapWrapF1F7

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

set_option maxHeartbeats 1000000 in
theorem heapWrapF8_evaluates (heap : Heap) (list thing : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF8"
      [termPtr list.addr, termPtr thing.addr] heap
      (Val.nat (heapWrapF8Model heap list thing)) heap := by
  let listThing : Ptr := ⟨Heap.read heap (thingField list 1)⟩
  let left : Ptr := ⟨Heap.read heap (thingField thing 2)⟩
  let right : Ptr := ⟨Heap.read heap (thingField left 3)⟩
  have hblockF8 : (checkedBlocks heapWrapBlocks heapWrapBlocksValid).get? "heapWrapF8" =
      some heapWrapBlocks[7].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, heapWrapBlocks]
  have hblockRhs : (checkedBlocks heapWrapBlocks heapWrapBlocksValid).get? "heapWrapF8Rhs" =
      some heapWrapBlocks[8].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, heapWrapBlocks]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel
    (Machine.stateCtx heapCtx heapOpCtx (checkedBlocks heapWrapBlocks heapWrapBlocksValid)) 120
    (Machine.start [] (.call "heapWrapF8" [termPtr list.addr, termPtr thing.addr]))).run heap) = _
  by_cases hlhs : Heap.read heap listThing = 0
  · have hlhsRaw : Heap.read heap { addr := Heap.read heap { addr := list.addr + 1 } } = 0 := by
      simpa [listThing, thingField] using hlhs
    set_option linter.unusedSimpArgs false in
      repeat
        rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
        first
        | rw [loadOp_step]
          simp [listThing, thingField]
        | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, Machine.start, hblockF8, hblockRhs,
            hload, hptrAdd, hptrOfNat, heq, hite, Machine.stateM_pure_run, loadOp,
            ptrAddOp, ptrOfNatOp, Op.eq, Op.compare, Op.ite, Op.effectful,
            Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
            Op.fixed, Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr,
            valPtr, valUnit, asPtr?, Val.as?_mk, Val.asNat?_nat, Val.primEq?_nat,
            Val.ty_mk, Val.mk_ofNat, Val.ty_nat, Ty.toNat_cast_ofNat,
            Ty.toBool_cast_ofBool, toPtr_ofPtr, List.get, Fin.cast, listThing,
            thingField, hlhs, hlhsRaw]
    simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
      OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
      StateT.pure, Id.run, heapWrapF8Model, listThing, hlhs]
  · have hlhsRaw : ¬ Heap.read heap { addr := Heap.read heap { addr := list.addr + 1 } } = 0 := by
      simpa [listThing, thingField] using hlhs
    by_cases hrhs : Heap.read heap right = 0
    · have hrhsRaw :
          Heap.read heap { addr := Heap.read heap { addr := Heap.read heap { addr := thing.addr + 2 } + 3 } } = 0 := by
        simpa [left, right, thingField] using hrhs
      set_option linter.unusedSimpArgs false in
        repeat
          rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
          first
          | rw [loadOp_step]
            simp [listThing, left, right, thingField]
          | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, Machine.start, hblockF8, hblockRhs,
              hload, hptrAdd, hptrOfNat, heq, hite, Machine.stateM_pure_run, loadOp,
              ptrAddOp, ptrOfNatOp, Op.eq, Op.compare, Op.ite, Op.effectful,
              Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
              Op.fixed, Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr,
              valPtr, valUnit, asPtr?, Val.as?_mk, Val.asNat?_nat, Val.primEq?_nat,
              Val.ty_mk, Val.mk_ofNat, Val.ty_nat, Ty.toNat_cast_ofNat,
              Ty.toBool_cast_ofBool, toPtr_ofPtr, List.get, Fin.cast, listThing,
              left, right, thingField, hlhs, hlhsRaw, hrhs, hrhsRaw]
      simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
        OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
        StateT.pure, Id.run, heapWrapF8Model, listThing, left, right, hlhs, hrhs]
    · have hrhsRaw :
          ¬ Heap.read heap { addr := Heap.read heap { addr := Heap.read heap { addr := thing.addr + 2 } + 3 } } = 0 := by
        simpa [left, right, thingField] using hrhs
      set_option linter.unusedSimpArgs false in
        repeat
          rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
          first
          | rw [loadOp_step]
            simp [listThing, left, right, thingField]
          | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, Machine.start, hblockF8, hblockRhs,
              hload, hptrAdd, hptrOfNat, heq, hite, Machine.stateM_pure_run, loadOp,
              ptrAddOp, ptrOfNatOp, Op.eq, Op.compare, Op.ite, Op.effectful,
              Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
              Op.fixed, Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr,
              valPtr, valUnit, asPtr?, Val.as?_mk, Val.asNat?_nat, Val.primEq?_nat,
              Val.ty_mk, Val.mk_ofNat, Val.ty_nat, Ty.toNat_cast_ofNat,
              Ty.toBool_cast_ofBool, toPtr_ofPtr, List.get, Fin.cast, listThing,
              left, right, thingField, hlhs, hlhsRaw, hrhs, hrhsRaw]
      simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
        OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
        StateT.pure, Id.run, heapWrapF8Model, listThing, left, right, hlhs, hrhs]

theorem heapWrapF8_short_circuit_evaluates (heap : Heap) (list thing : Ptr)
    (hzero : Heap.read heap ⟨Heap.read heap (thingField list 1)⟩ = 0) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks heapWrapBlocks heapWrapBlocksValid) "heapWrapF8"
      [termPtr list.addr, termPtr thing.addr] heap (Val.nat 0) heap := by
  simpa [heapWrapF8Model, hzero] using heapWrapF8_evaluates heap list thing

section MonadicSL
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

private abbrev heapWrapStateCtxF8 : Ctx := heapStateCtx heapWrapBlocks heapWrapBlocksValid

def heapWrapF8Footprint (list thing listThing left right : Ptr) (lhs rhs : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (thingField list 1 ↦ listThing.addr) ∗
    (listThing ↦ lhs) ∗
    (thingField thing 2 ↦ left.addr) ∗
    (thingField left 3 ↦ right.addr) ∗
    (right ↦ rhs)

private theorem heapWrapF8Model_of_footprint (heap : Heap)
    (list thing listThing left right : Ptr) (lhs rhs : Nat)
    (hp : (heapWrapF8Footprint list thing listThing left right lhs rhs).holds heap) :
    heapWrapF8Model heap list thing = if lhs = 0 then 0 else if rhs = 0 then 0 else 1 := by
  rcases hp with ⟨_, hlistField, hp⟩
  rcases hp with ⟨_, hlistThing, hp⟩
  rcases hp with ⟨_, hthingLeft, hp⟩
  rcases hp with ⟨_, hleftRight, hright⟩
  have hlistFieldRead := (cell_pointsTo_holds (thingField list 1) listThing.addr heap).1 hlistField
  have hlistThingRead := (cell_pointsTo_holds listThing lhs heap).1 hlistThing
  have hthingLeftRead := (cell_pointsTo_holds (thingField thing 2) left.addr heap).1 hthingLeft
  have hleftRightRead := (cell_pointsTo_holds (thingField left 3) right.addr heap).1 hleftRight
  have hrightRead := (cell_pointsTo_holds right rhs heap).1 hright
  cases listThing
  cases left
  cases right
  simp [heapWrapF8Model, hlistFieldRead, hlistThingRead, hthingLeftRead,
    hleftRightRead, hrightRead]

def heapWrapF8ShortCircuitFootprint (list listThing : Ptr) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (thingField list 1 ↦ listThing.addr) ∗ (listThing ↦ 0)

/-
```
{ list+1 ↦ listThing.addr ∗ listThing ↦ lhs ∗ thing+2 ↦ left.addr ∗
  left+3 ↦ right.addr ∗ right ↦ rhs }
  heapWrapF8(list, thing)
{ same footprint, r = if lhs = 0 then 0 else if rhs = 0 then 0 else 1 }
```
-/
@[zspec] theorem heapWrapF8_spec (list thing listThing left right : Ptr) (lhs rhs : Nat) :
    Zag.EvaluatesCall heapWrapStateCtxF8 "heapWrapF8"
      [termPtr list.addr, termPtr thing.addr]
      (HProp.toAssertion (heapWrapF8Footprint list thing listThing left right lhs rhs))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat (if lhs = 0 then 0 else if rhs = 0 then 0 else 1) ∧
          (heapWrapF8Footprint list thing listThing left right lhs rhs).holds final⌝) := by
  let PreHeap :=
    { heap : Heap // (heapWrapF8Footprint list thing listThing left right lhs rhs).holds heap }
  change EvalTriple.EvaluatesFrom heapWrapStateCtxF8
    (Machine.start [] (.call "heapWrapF8" [termPtr list.addr, termPtr thing.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hmodel := heapWrapF8Model_of_footprint hh.1 list thing listThing left right lhs rhs hh.2
    have hex := heapWrapF8_evaluates hh.1 list thing
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hmodel, hh.2]

/-
```
{ list+1 ↦ listThing.addr ∗ listThing ↦ 0 }
  heapWrapF8(list, thing)
{ same footprint, r = 0 }
```
-/
@[zspec] theorem heapWrapF8_short_circuit_spec (list thing listThing : Ptr) :
    Zag.EvaluatesCall heapWrapStateCtxF8 "heapWrapF8"
      [termPtr list.addr, termPtr thing.addr]
      (HProp.toAssertion (heapWrapF8ShortCircuitFootprint list listThing))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat 0 ∧
          (heapWrapF8ShortCircuitFootprint list listThing).holds final⌝) := by
  let PreHeap :=
    { heap : Heap // (heapWrapF8ShortCircuitFootprint list listThing).holds heap }
  change EvalTriple.EvaluatesFrom heapWrapStateCtxF8
    (Machine.start [] (.call "heapWrapF8" [termPtr list.addr, termPtr thing.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hpost := hh.2
    rcases hh.2 with ⟨_, hlistField, hlistThing⟩
    have hlistFieldRead :=
      (cell_pointsTo_holds (thingField list 1) listThing.addr hh.1).1 hlistField
    have hlistThingRead := (cell_pointsTo_holds listThing 0 hh.1).1 hlistThing
    cases listThing
    have hzero : Heap.read hh.1 ⟨Heap.read hh.1 (thingField list 1)⟩ = 0 := by
      simpa [hlistFieldRead] using hlistThingRead
    have hex := heapWrapF8_short_circuit_evaluates hh.1 list thing hzero
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hpost]

end MonadicSL

end Zag.Test.Autocorres.Examples
