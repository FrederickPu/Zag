import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Suzuki.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Suzuki.thy).

The current model lays a node out as `[data, next-address]` in a functional `Nat` heap. It has no
C pointer guards, so `SuzukiSeparated` explicitly supplies the no-aliasing fact that source object
validity and distinctness provide. Under that delimiter, this block retains all source stores and
the same two-link return expression.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev suzukiBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    suzuki(w : Ptr, x : Ptr, y : Ptr, z : Ptr) : Nat {
      storedWNext := op "store"[op "ptrAdd"[w, nat(1)], op "ptrAddr"[x]];
      storedXNextY := op "store"[op "ptrAdd"[x, nat(1)], op "ptrAddr"[y]];
      storedYNext := op "store"[op "ptrAdd"[y, nat(1)], op "ptrAddr"[z]];
      storedXNextZ := op "store"[op "ptrAdd"[x, nat(1)], op "ptrAddr"[z]];
      storedWData := op "store"[w, nat(1)];
      storedXData := op "store"[x, nat(2)];
      storedYData := op "store"[y, nat(3)];
      storedZData := op "store"[z, nat(4)];
      next1Addr := op "load"[op "ptrAdd"[w, nat(1)]];
      next1 := op "ptrOfNat"[next1Addr];
      next2Addr := op "load"[op "ptrAdd"[next1, nat(1)]];
      next2 := op "ptrOfNat"[next2Addr];
      ret op "load"[next2]
    }
  ]

theorem suzukiBlocksValid : BlockCtx.Valid suzukiBlocks := by
  valid_blocks [suzukiBlocks]

abbrev suzukiCtx : Ctx := mkCtx suzukiBlocks suzukiBlocksValid

theorem suzukiCtx_wellTyped : Ctx.WellTyped suzukiCtx := by
  typecheck_ctx

private abbrev suzukiStateCtx : Ctx := heapStateCtx suzukiBlocks suzukiBlocksValid

def nextField (ptr : Ptr) : Ptr := ⟨ptr.addr + 1⟩

def suzukiFields (w x y z : Ptr) : List Ptr :=
  [w, nextField w, x, nextField x, y, nextField y, z, nextField z]

def SuzukiSeparated (w x y z : Ptr) : Prop :=
  (suzukiFields w x y z).Nodup

def suzukiHeapSpec (heap : Heap) (w x y z : Ptr) : Heap :=
  let heap := Heap.write heap (nextField w) x.addr
  let heap := Heap.write heap (nextField x) y.addr
  let heap := Heap.write heap (nextField y) z.addr
  let heap := Heap.write heap (nextField x) z.addr
  let heap := Heap.write heap w 1
  let heap := Heap.write heap x 2
  let heap := Heap.write heap y 3
  Heap.write heap z 4

def suzukiReturnSpec (heap : Heap) (w x y z : Ptr) : Nat :=
  let final := suzukiHeapSpec heap w x y z
  let next1 := Ptr.mk (Heap.read final (nextField w))
  let next2 := Ptr.mk (Heap.read final (nextField next1))
  Heap.read final next2

theorem suzuki_read_write_same (heap : Heap) (ptr : Ptr) (value : Nat) :
    Heap.read (Heap.write heap ptr value) ptr = value := by
  simp [Heap.read, Heap.write]

theorem suzuki_read_write_other (heap : Heap) (written read : Ptr) (value : Nat)
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

theorem suzuki_read_write_other_rev (heap : Heap) (written read : Ptr) (value : Nat)
    (h : written ≠ read) :
    Heap.read (Heap.write heap written value) read = Heap.read heap read :=
  suzuki_read_write_other heap written read value (Ne.symm h)

theorem suzukiHeapSpec_return (heap : Heap) (w x y z : Ptr)
    (hsep : SuzukiSeparated w x y z) :
    let final := suzukiHeapSpec heap w x y z
    let next1 := Ptr.mk (Heap.read final (nextField w))
    let next2 := Ptr.mk (Heap.read final (nextField next1))
    Heap.read final next2 = 4 := by
  simp [SuzukiSeparated, suzukiFields] at hsep
  simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
    suzuki_read_write_other_rev, hsep]

theorem suzukiHeapSpec_frame (heap : Heap) (w x y z ptr : Ptr)
    (hout : ptr ∉ suzukiFields w x y z) :
    Heap.read (suzukiHeapSpec heap w x y z) ptr = Heap.read heap ptr := by
  simp [suzukiFields] at hout
  simp [suzukiHeapSpec, suzuki_read_write_other, hout]

def suzukiPre (w x y z : Ptr)
    (wData wNext xData xNext yData yNext zData zNext : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (w ↦ wData) ∗ (nextField w ↦ wNext) ∗
    (x ↦ xData) ∗ (nextField x ↦ xNext) ∗
    (y ↦ yData) ∗ (nextField y ↦ yNext) ∗
    (z ↦ zData) ∗ (nextField z ↦ zNext)

def suzukiPost (w x y z : Ptr) (zNext : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (w ↦ 1) ∗ (nextField w ↦ x.addr) ∗
    (x ↦ 2) ∗ (nextField x ↦ z.addr) ∗
    (y ↦ 3) ∗ (nextField y ↦ z.addr) ∗
    (z ↦ 4) ∗ (nextField z ↦ zNext)

private theorem suzukiPost_holds (heap : Heap) (w x y z : Ptr)
    (wData wNext xData xNext yData yNext zData zNext : Nat)
    (hsep : SuzukiSeparated w x y z)
    (hp : (suzukiPre w x y z wData wNext xData xNext yData yNext zData zNext).holds heap) :
    (suzukiPost w x y z zNext).holds (suzukiHeapSpec heap w x y z) := by
  simp [SuzukiSeparated, suzukiFields] at hsep
  rcases hp with ⟨hdW, _hwData, hp⟩
  rcases hp with ⟨hdWNext, _hwNext, hp⟩
  rcases hp with ⟨hdX, _hxData, hp⟩
  rcases hp with ⟨hdXNext, _hxNext, hp⟩
  rcases hp with ⟨hdY, _hyData, hp⟩
  rcases hp with ⟨hdYNext, _hyNext, hp⟩
  rcases hp with ⟨hdZ, _hzData, hzNextHolds⟩
  have hzNextRead : Heap.read heap (nextField z) = zNext :=
    (cell_pointsTo_holds (nextField z) zNext heap).1 hzNextHolds
  refine ⟨hdW, ?_, ?_⟩
  · apply (cell_pointsTo_holds w 1 _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      hsep]
  refine ⟨hdWNext, ?_, ?_⟩
  · apply (cell_pointsTo_holds (nextField w) x.addr _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      suzuki_read_write_other_rev, hsep]
  refine ⟨hdX, ?_, ?_⟩
  · apply (cell_pointsTo_holds x 2 _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      hsep]
  refine ⟨hdXNext, ?_, ?_⟩
  · apply (cell_pointsTo_holds (nextField x) z.addr _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      suzuki_read_write_other_rev, hsep]
  refine ⟨hdY, ?_, ?_⟩
  · apply (cell_pointsTo_holds y 3 _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      hsep]
  refine ⟨hdYNext, ?_, ?_⟩
  · apply (cell_pointsTo_holds (nextField y) z.addr _).2
    simp [suzukiHeapSpec, suzuki_read_write_same, suzuki_read_write_other,
      suzuki_read_write_other_rev, hsep]
  refine ⟨hdZ, ?_, ?_⟩
  · apply (cell_pointsTo_holds z 4 _).2
    simp [suzukiHeapSpec, suzuki_read_write_same]
  · apply (cell_pointsTo_holds (nextField z) zNext _).2
    calc
      Heap.read (suzukiHeapSpec heap w x y z) (nextField z) = Heap.read heap (nextField z) := by
        simp [suzukiHeapSpec, suzuki_read_write_other_rev, hsep]
      _ = zNext := hzNextRead

private theorem suzuki_evaluates_state (heap : Heap) (w x y z : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks suzukiBlocks suzukiBlocksValid) "suzuki"
      [termPtr w.addr, termPtr x.addr, termPtr y.addr, termPtr z.addr] heap
      (Val.nat (suzukiReturnSpec heap w x y z)) (suzukiHeapSpec heap w x y z) := by
  have hblock : (checkedBlocks suzukiBlocks suzukiBlocksValid).get? "suzuki" =
      some suzukiBlocks[0].2 := by
    simp [BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, suzukiBlocks]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel
    (Machine.stateCtx heapCtx heapOpCtx (checkedBlocks suzukiBlocks suzukiBlocksValid)) 150
    (Machine.start [] (.call "suzuki"
      [termPtr w.addr, termPtr x.addr, termPtr y.addr, termPtr z.addr]))).run heap) = _
  set_option linter.unusedSimpArgs false in
    repeat
      rw [Machine.evalConfigFuel_run_succ_of_none (hresult := rfl)]
      first
      | rw [storeOp_step]
        simp [suzukiHeapSpec, suzukiReturnSpec, nextField]
      | rw [loadOp_step]
        simp
      | simp [Machine.step, Machine.evalTerm, Machine.applyValue,
          Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
          Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
          Machine.enterInstrs, Machine.driveOp, Machine.start, hblock, hload,
          hstore, hptrAdd, hptrAddr, hptrOfNat, Machine.stateM_pure_run, loadOp,
          storeOp, ptrAddOp, ptrAddrOp, ptrOfNatOp, Op.effectful, Op.Body.collect,
          Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
          Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
  simp [Machine.evalConfigFuel, Machine.result?, Machine.stateCtx,
    OptionT.mk, OptionT.pure, OptionT.run, Pure.pure, StateT.instMonad,
    StateT.pure, Id.run]

/-
```
{ w ↦ _ ∗ w.next ↦ _ ∗ x ↦ _ ∗ x.next ↦ _ ∗
  y ↦ _ ∗ y.next ↦ _ ∗ z ↦ _ ∗ z.next ↦ zNext }
  suzuki(w, x, y, z)
{ r = 4 ∧ w ↦ 1 ∗ w.next ↦ x ∗ x ↦ 2 ∗ x.next ↦ z ∗
  y ↦ 3 ∗ y.next ↦ z ∗ z ↦ 4 ∗ z.next ↦ zNext }
```
-/
@[zspec] theorem suzuki_spec (w x y z : Ptr)
    (wData wNext xData xNext yData yNext zData zNext : Nat)
    (hsep : SuzukiSeparated w x y z) :
    Zag.EvaluatesCall suzukiStateCtx "suzuki"
      [termPtr w.addr, termPtr x.addr, termPtr y.addr, termPtr z.addr]
      (HProp.toAssertion (suzukiPre w x y z wData wNext xData xNext yData yNext zData zNext))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat 4 ∧ (suzukiPost w x y z zNext).holds final⌝) :=
  evaluatesCall_of_hprop "suzuki" _
    (suzukiPre w x y z wData wNext xData xNext yData yNext zData zNext)
    (fun _ => suzukiPost w x y z zNext)
    (Val.nat 4)
    (fun h => suzukiHeapSpec h w x y z)
    (fun h => by
      have hreturn : suzukiReturnSpec h w x y z = 4 := by
        simpa [suzukiReturnSpec] using suzukiHeapSpec_return h w x y z hsep
      simpa [hreturn] using suzuki_evaluates_state h w x y z)
    (fun h hp => suzukiPost_holds h w x y z
      wData wNext xData xNext yData yNext zData zNext hsep hp)

theorem suzuki_run :
    (match (Machine.evalFuel suzukiCtx 150 []
        (.call "suzuki" [termPtr 1, termPtr 3, termPtr 5, termPtr 7])).run Heap.empty with
      | (some value, final) => (value.asNat?, final)
      | (none, final) => (none, final)) =
    (some 4, suzukiHeapSpec Heap.empty ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨7⟩) := by
  native_decide

end Zag.Test.Autocorres.Examples
