import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Alloc.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Alloc.thy).

The C allocator maintains a sorted, coalescing free-region list. `PeanoHeap.Heap` is instead a
monotone fresh-cell heap and its shared `Heap.free` operation is intentionally a no-op. The blocks
below therefore specify the executable fresh-allocation behavior, not a translation of the C
allocator. `Allocator` and the operations following the blocks are the current-model
semantic correspondence: addresses and sizes are `Nat`, while splitting, first-fit search,
deallocation insertion, and the allocation counter remain explicit.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

def resetHeapOp : Op heapCtx (StateM Heap) :=
  Op.effectful 0 (fun _ => some UnitTy) fun
  | [] => fun _ => (some valUnit, Heap.empty)
  | _ => fun heap => (none, heap)

@[eval_step] def allocOpCtx : OpCtx heapCtx (StateM Heap) :=
  heapOpCtx ++ [("resetHeap", resetHeapOp)]

abbrev allocBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    freshInitAllocator() : Unit {
      ret op "resetHeap"[]
    },
    freshAlloc(size : Nat) : Ptr {
      ret op "allocPtr"[size]
    },
    eraseFreedStart(ptr : Ptr) : Unit {
      ret op "store"[ptr, nat(0)]
    }
  ]

theorem allocBlocksValid : BlockCtx.Valid allocBlocks := by
  valid_blocks [allocBlocks]

abbrev allocCtx : Ctx where
  primCtx := heapCtx
  M := StateM Heap
  monad := StateT.instMonad
  opCtx := allocOpCtx
  blockCtx := checkedBlocks allocBlocks allocBlocksValid
  postShape := .arg Heap .pure
  wpMonad := inferInstance

instance : Peano.Model allocCtx where
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

theorem allocCtx_wellTyped : Ctx.WellTyped allocCtx := by
  typecheck_ctx

private abbrev allocStateCtx : Ctx :=
  Machine.stateCtx heapCtx allocOpCtx (checkedBlocks allocBlocks allocBlocksValid)

structure FreeRegion where
  start : Nat
  size : Nat
deriving Repr, DecidableEq

structure Allocator where
  free : List FreeRegion
  numAllocs : Nat
deriving Repr, DecidableEq

def FreeRegion.endAddr (region : FreeRegion) : Nat :=
  region.start + region.size

def Allocator.Valid (allocator : Allocator) : Prop :=
  (∀ region ∈ allocator.free, region.start ≠ 0 ∧ 0 < region.size) ∧
  allocator.free.Pairwise fun left right => left.endAddr < right.start

def alignUp (value alignmentBits : Nat) : Nat :=
  let alignment := 2 ^ alignmentBits
  value + ((alignment - value % alignment) % alignment)

def allocChunkBits : Nat := 3

def allocRequestSize (size : Nat) : Nat :=
  alignUp size allocChunkBits

def allocAlignmentBits (alignmentBits : Nat) : Nat :=
  max alignmentBits allocChunkBits

def AllocPre (allocator : Allocator) (size alignmentBits : Nat) : Prop :=
  allocator.Valid ∧ 0 < size ∧ alignmentBits < 32

def FreeRegion.Disjoint (left right : FreeRegion) : Prop :=
  left.endAddr ≤ right.start ∨ right.endAddr ≤ left.start

def DeallocPre (allocator : Allocator) (ptr : Ptr) (size : Nat) : Prop :=
  let region : FreeRegion := { start := ptr.addr, size := allocRequestSize size }
  allocator.Valid ∧ ptr ≠ null ∧ 0 < size ∧ 0 < allocator.numAllocs ∧
    ∀ freeRegion ∈ allocator.free, region.Disjoint freeRegion

def AddMemPoolPre (allocator : Allocator) (ptr : Ptr) (size : Nat) : Prop :=
  let region : FreeRegion := { start := ptr.addr, size := allocRequestSize size }
  allocator.Valid ∧ ptr ≠ null ∧ 0 < size ∧
    ∀ freeRegion ∈ allocator.free, region.Disjoint freeRegion

structure RegionAllocation where
  ptr : Ptr
  before : List FreeRegion
  after : List FreeRegion
deriving Repr, DecidableEq

def allocateRegion? (region : FreeRegion) (size alignmentBits : Nat) : Option RegionAllocation :=
  let desiredStart := alignUp region.start alignmentBits
  if 0 < size ∧ desiredStart + size ≤ region.endAddr then
    let beforeSize := desiredStart - region.start
    let afterStart := desiredStart + size
    let afterSize := region.endAddr - afterStart
    some {
      ptr := ⟨desiredStart⟩
      before := if beforeSize = 0 then [] else [{ start := region.start, size := beforeSize }]
      after := if afterSize = 0 then [] else [{ start := afterStart, size := afterSize }]
    }
  else
    none

def allocateRegions (size alignmentBits : Nat) :
    List FreeRegion → Option (Ptr × List FreeRegion)
| [] => none
| region :: regions =>
    match allocateRegion? region size alignmentBits with
    | some allocation => some (allocation.ptr, allocation.before ++ allocation.after ++ regions)
    | none =>
        match allocateRegions size alignmentBits regions with
        | some (ptr, remaining) => some (ptr, region :: remaining)
        | none => none

def allocatorAlloc (allocator : Allocator) (size alignmentBits : Nat) :
    Option (Ptr × Allocator) := do
  let (ptr, free) ← allocateRegions (allocRequestSize size)
    (allocAlignmentBits alignmentBits) allocator.free
  some (ptr, { free, numAllocs := allocator.numAllocs + 1 })

def insertFreeRegion (region : FreeRegion) : List FreeRegion → List FreeRegion
| [] => [region]
| next :: rest =>
    if region.endAddr < next.start then
      region :: next :: rest
    else if next.endAddr < region.start then
      next :: insertFreeRegion region rest
    else
      let start := min region.start next.start
      let endAddr := max region.endAddr next.endAddr
      insertFreeRegion { start, size := endAddr - start } rest

def allocatorDealloc (allocator : Allocator) (ptr : Ptr) (size : Nat) : Allocator :=
  { free := insertFreeRegion { start := ptr.addr, size := allocRequestSize size } allocator.free
    numAllocs := allocator.numAllocs - 1 }

def allocatorAddMemPool (allocator : Allocator) (ptr : Ptr) (size : Nat) : Allocator :=
  let freed := allocatorDealloc allocator ptr size
  { freed with numAllocs := allocator.numAllocs }

theorem allocateRegion_sound {region : FreeRegion} {size alignmentBits : Nat}
    {allocation : RegionAllocation}
    (h : allocateRegion? region size alignmentBits = some allocation) :
    0 < size ∧ allocation.ptr.addr % (2 ^ alignmentBits) = 0 ∧
      region.start ≤ allocation.ptr.addr ∧
      allocation.ptr.addr + size ≤ region.endAddr := by
  simp only [allocateRegion?] at h
  split at h <;> simp_all
  subst allocation
  simp_all [alignUp]
  let alignment := 2 ^ alignmentBits
  have halignment : 0 < alignment := by
    dsimp [alignment]
    exact Nat.pow_pos (by decide)
  have hremainder : region.start % alignment < alignment := Nat.mod_lt _ halignment
  by_cases hzero : region.start % alignment = 0
  · change (region.start + (alignment - region.start % alignment)) % alignment = 0
    rw [Nat.add_mod, hzero]
    simp
  · change (region.start + (alignment - region.start % alignment)) % alignment = 0
    have hoffset : (alignment - region.start % alignment) % alignment =
        alignment - region.start % alignment := Nat.mod_eq_of_lt (by omega)
    have hsum : region.start % alignment + (alignment - region.start % alignment) = alignment := by
      omega
    calc
      (region.start + (alignment - region.start % alignment)) % alignment =
          (region.start % alignment + (alignment - region.start % alignment)) % alignment := by
            rw [Nat.add_mod, hoffset]
      _ = alignment % alignment := by rw [hsum]
      _ = 0 := Nat.mod_self alignment

theorem allocateRegion_nonnull {region : FreeRegion} {size alignmentBits : Nat}
    {allocation : RegionAllocation} (hstart : region.start ≠ 0)
    (h : allocateRegion? region size alignmentBits = some allocation) :
    allocation.ptr ≠ null := by
  have hsound := allocateRegion_sound h
  intro hnull
  have haddrzero : allocation.ptr.addr = 0 := by
    simpa [null] using congrArg Ptr.addr hnull
  exact hstart (Nat.eq_zero_of_le_zero (haddrzero ▸ hsound.2.2.1))

theorem allocateRegions_nonnull {regions : List FreeRegion} {size alignmentBits : Nat}
    {ptr : Ptr} {remaining : List FreeRegion}
    (hstarts : ∀ region ∈ regions, region.start ≠ 0)
    (h : allocateRegions size alignmentBits regions = some (ptr, remaining)) :
    ptr ≠ null := by
  induction regions generalizing ptr remaining with
  | nil => simp [allocateRegions] at h
  | cons region regions ih =>
      cases hregion : allocateRegion? region size alignmentBits with
      | none =>
          cases htail : allocateRegions size alignmentBits regions with
          | none => simp [allocateRegions, hregion, htail] at h
          | some result =>
              rcases result with ⟨tailPtr, tailRegions⟩
              have htailPtr : tailPtr ≠ null :=
                ih (fun candidate hmem => hstarts candidate (by simp [hmem])) htail
              simp [allocateRegions, hregion, htail] at h
              simpa [h.1] using htailPtr
      | some allocation =>
          have hallocation := allocateRegion_nonnull (hstarts region (by simp)) hregion
          simp [allocateRegions, hregion] at h
          simpa [h.1] using hallocation

theorem allocateRegions_uses_fitting_head {region : FreeRegion} {regions : List FreeRegion}
    {size alignmentBits : Nat} {allocation : RegionAllocation}
    (h : allocateRegion? region size alignmentBits = some allocation) :
    allocateRegions size alignmentBits (region :: regions) =
      some (allocation.ptr, allocation.before ++ allocation.after ++ regions) := by
  simp [allocateRegions, h]

theorem allocatorAlloc_increments_count {allocator next : Allocator} {ptr : Ptr}
    {size alignmentBits : Nat}
    (h : allocatorAlloc allocator size alignmentBits = some (ptr, next)) :
    next.numAllocs = allocator.numAllocs + 1 := by
  unfold allocatorAlloc at h
  cases hregions : allocateRegions (allocRequestSize size)
      (allocAlignmentBits alignmentBits) allocator.free with
  | none => simp [hregions] at h
  | some result =>
      rcases result with ⟨resultPtr, free⟩
      simp [hregions] at h
      rw [← h.2]

theorem allocatorAlloc_returns_nonnull {allocator next : Allocator} {ptr : Ptr}
    {size alignmentBits : Nat} (hpre : AllocPre allocator size alignmentBits)
    (h : allocatorAlloc allocator size alignmentBits = some (ptr, next)) :
    ptr ≠ null := by
  unfold allocatorAlloc at h
  cases hregions : allocateRegions (allocRequestSize size)
      (allocAlignmentBits alignmentBits) allocator.free with
  | none => simp [hregions] at h
  | some result =>
      rcases result with ⟨resultPtr, free⟩
      have hnonnull := allocateRegions_nonnull
        (regions := allocator.free) (ptr := resultPtr) (remaining := free)
        (fun region hmem => hpre.1.1 region hmem |>.1) hregions
      simp [hregions] at h
      simpa [← h.1] using hnonnull

theorem allocatorDealloc_records_region (allocator : Allocator) (ptr : Ptr) (size : Nat) :
    (allocatorDealloc allocator ptr size).free =
      insertFreeRegion { start := ptr.addr, size := allocRequestSize size } allocator.free ∧
    (allocatorDealloc allocator ptr size).numAllocs = allocator.numAllocs - 1 := by
  simp [allocatorDealloc]

theorem allocatorDealloc_decrements_positive_count {allocator : Allocator} {ptr : Ptr} {size : Nat}
    (hpre : DeallocPre allocator ptr size) :
    (allocatorDealloc allocator ptr size).numAllocs + 1 = allocator.numAllocs := by
  simp only [allocatorDealloc]
  unfold DeallocPre at hpre
  omega

theorem allocatorAddMemPool_preserves_count (allocator : Allocator) (ptr : Ptr) (size : Nat) :
    (allocatorAddMemPool allocator ptr size).numAllocs = allocator.numAllocs := by
  simp [allocatorAddMemPool]

@[zspec] theorem resetHeapAction_spec
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateM Heap) (((fun _heap : Heap => (some valUnit, Heap.empty)) :
        StateM Heap (Option (Val heapCtx))))
      (fun _heap => Q.1 (some valUnit) Heap.empty) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem resetHeapOp_action_spec
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple ((resetHeapOp.action "resetHeap" []).get
        (by simp [resetHeapOp, Op.effectful]))
      (fun _heap => Q.1 (some valUnit) Heap.empty) Q := by
  simpa [resetHeapOp, Op.effectful] using resetHeapAction_spec Q

theorem resetHeapOp_action_vals :
    resetHeapOp.action "resetHeap" [] = some (fun _heap : Heap => (some valUnit, Heap.empty)) := by
  rfl

private theorem freshInitAllocator_evaluates_state (heap : Heap) :
    EvalTriple.State.EvaluatesCall heapCtx allocOpCtx
      (checkedBlocks allocBlocks allocBlocksValid) "freshInitAllocator" []
      heap valUnit Heap.empty := by
  let blockCtx := checkedBlocks allocBlocks allocBlocksValid
  let ctx := Machine.stateCtx heapCtx allocOpCtx blockCtx
  let s0 : Machine.Config heapCtx := Machine.start [] (.call "freshInitAllocator" [])
  let s1 : Machine.Config heapCtx :=
    { control := .apply (.blockRef "freshInitAllocator" [] UnitTy) [], env := [], stack := [] }
  let s2 : Machine.Config heapCtx :=
    { control := .eval (.op "resetHeap" []), env := [],
      stack := [.call "freshInitAllocator" []] }
  let resetFrame : Frame heapCtx :=
    .opBody (fun | some value => .done value | none => .fail) [] []
  let s3 : Machine.Config heapCtx :=
    { control := .apply (.opRef "resetHeap" [] [] UnitTy) [], env := [],
      stack := [resetFrame, .call "freshInitAllocator" []] }
  let s4 : Machine.Config heapCtx :=
    { control := .ret valUnit, env := [],
      stack := [resetFrame, .call "freshInitAllocator" []] }
  let s5 : Machine.Config heapCtx :=
    { control := .ret valUnit, env := [], stack := [.call "freshInitAllocator" []] }
  let s6 : Machine.Config heapCtx :=
    { control := .ret valUnit, env := [], stack := [] }
  have hblock : blockCtx.get? "freshInitAllocator" = some allocBlocks[0].2 := by
    simp [blockCtx, BlockCtx.get?, BlockCtx.Raw.get?, Scope.get?, allocBlocks]
  have hreset : allocOpCtx.get? "resetHeap" = some resetHeapOp := by
    simp [allocOpCtx, OpCtx.get?, heapOpCtx, Peano.opCtx]
  have h01 : Id.run ((Machine.step ctx s0).run heap) = (some s1, heap) := by
    simp [ctx, s0, s1, Machine.step, Machine.evalTerm, Machine.ofOption,
      Machine.evalTermImmediate, Machine.start, hblock, Machine.stateM_pure_run]
  have h12 : Id.run ((Machine.step ctx s1).run heap) = (some s2, heap) := by
    simp [ctx, s1, s2, Machine.step, Machine.applyValue, Machine.applyValueImmediate,
      Machine.ofOption, Machine.enterBlock, Machine.enterInstrs, hblock,
      Machine.stateM_pure_run, Block.entryEnv, allocBlocks]
  have h23 : Id.run ((Machine.step ctx s2).run heap) = (some s3, heap) := by
    simp [ctx, s2, s3, resetFrame, Machine.step, Machine.evalTerm,
      Machine.driveSelectedOp, Machine.ofOption, Machine.driveOp, hreset,
      Machine.stateM_pure_run, resetHeapOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, valUnit]
    funext value
    cases value <;> rfl
  have h34 : Id.run ((Machine.step ctx s3).run heap) = (some s4, Heap.empty) := by
    simp [ctx, s3, s4, resetFrame, Machine.step, Machine.applyValue, hreset,
      resetHeapOp_action_vals, OptionT.lift, OptionT.run, OptionT.bind,
      OptionT.pure, OptionT.fail, Id.run, Bind.bind, Pure.pure, monadLift,
      MonadLift.monadLift]
    rfl
  have h45 : Id.run ((Machine.step ctx s4).run Heap.empty) = (some s5, Heap.empty) := by
    simp [ctx, s4, s5, resetFrame, Machine.step, Machine.ofOption,
      Machine.resumeFrame, Machine.driveOp, Machine.stateM_pure_run]
  have h56 : Id.run ((Machine.step ctx s5).run Heap.empty) = (some s6, Heap.empty) := by
    simp [ctx, s5, s6, Machine.step, Machine.ofOption, Machine.resumeFrame,
      Machine.stateM_pure_run]
  apply EvalTriple.State.EvaluatesFrom.of_evalConfigFuel
  change Id.run ((Machine.evalConfigFuel ctx 50 s0).run heap) = _
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 49 s0 s1 heap heap rfl h01]
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 48 s1 s2 heap heap rfl h12]
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 47 s2 s3 heap heap rfl h23]
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 46 s3 s4 heap Heap.empty rfl h34]
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 45 s4 s5 Heap.empty Heap.empty rfl h45]
  rw [Machine.evalConfigFuel_run_succ_of_step heapCtx allocOpCtx blockCtx 44 s5 s6 Heap.empty Heap.empty rfl h56]
  simp [Machine.evalConfigFuel, Machine.result?, ctx, s6, OptionT.pure, StateT.pure,
    Pure.pure, valUnit]
  rfl

private theorem freshAlloc_evaluates_state (heap : Heap) (size : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx allocOpCtx
      (checkedBlocks allocBlocks allocBlocksValid) "freshAlloc" [.nat size]
      heap (valPtr (Heap.allocPtr heap)) (Heap.allocHeap heap size) := by
  set_option zvcgen.resumeReturn true in
    zvcgen [allocBlocks, checkedBlocks, allocOpCtx, allocPtrOp, Op.effectful,
      Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?,
      Term.nat, valPtr, Val.ty_nat, Val.mk_ofNat, Val.asNat?_nat,
      driveOp_apply_done, resume_dependent_apply_done, allocPtrOp_action_val,
      alloc, Heap.allocPtr, Heap.allocHeap]
  all_goals try solve_by_elim
  all_goals subst_vars
  all_goals try simp_all [Val.asNat?_nat]

private theorem eraseFreedStart_evaluates_state (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx allocOpCtx
      (checkedBlocks allocBlocks allocBlocksValid) "eraseFreedStart" [termPtr ptr.addr]
      heap valUnit (Heap.write heap ptr 0) := by
  rcases ptr with ⟨ptr⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [allocBlocks, checkedBlocks, allocOpCtx, storeOp, Op.effectful,
      Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?,
      Term.nat, termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat,
      Val.mk_ofNat, Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, resume_store_value_operand,
      storeValAction_spec, storeOp_action_spec, storeOp_action_vals]
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]
  all_goals try solve_by_elim
  all_goals try obtain ⟨hleft, hright⟩ := ‹_ ∧ _›
  all_goals subst_vars
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]

section MonadicSL
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

/-- Reset yields the empty heap; monadic packaging of the model. -/
@[zspec] theorem freshInitAllocator_spec :
    Zag.EvaluatesCall allocStateCtx "freshInitAllocator" []
      (fun _ => ⌜True⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ final = Heap.empty⌝) := by
  let PreHeap := { heap : Heap // True }
  change EvalTriple.EvaluatesFrom allocStateCtx
    (Machine.start [] (.call "freshInitAllocator" [])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s _
    refine ⟨⟨s, trivial⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := freshInitAllocator_evaluates_state hh.val
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]

/-- Fresh allocation; monadic packaging of the alloc model. -/
@[zspec] theorem freshAlloc_spec (size : Nat) :
    Zag.EvaluatesCall allocStateCtx "freshAlloc" [.nat size]
      (fun _ => ⌜True⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜∃ h0 : Heap, result = valPtr (Heap.allocPtr h0) ∧
          final = Heap.allocHeap h0 size⌝) := by
  let PreHeap := { heap : Heap // True }
  change EvalTriple.EvaluatesFrom allocStateCtx
    (Machine.start [] (.call "freshAlloc" [.nat size])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s _
    refine ⟨⟨s, trivial⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := freshAlloc_evaluates_state hh.val size
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    exact ⟨hh.val, rfl, rfl⟩

/--
```
{ ptr ↦ old }
  eraseFreedStart(ptr)
{ ptr ↦ 0 }
```
-/
@[zspec] theorem eraseFreedStart_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall allocStateCtx "eraseFreedStart" [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (ptr ↦ 0).holds final⌝) := by
  let PreHeap := { heap : Heap // (ptr ↦ old).holds heap }
  change EvalTriple.EvaluatesFrom allocStateCtx
    (Machine.start [] (.call "eraseFreedStart" [termPtr ptr.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := eraseFreedStart_evaluates_state hh.1 ptr
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    exact (cell_pointsTo_holds ptr 0 (Heap.write hh.1 ptr 0)).2
      (by simp [Heap.read, Heap.write])

end MonadicSL

theorem freshAlloc_run :
    (match (Machine.evalFuel allocCtx 50 []
        (.call "freshAlloc" [.nat 3])).run Heap.empty with
      | (some value, final) => (asPtr? value, final)
      | (none, final) => (none, final)) =
    (some (Heap.allocPtr Heap.empty), Heap.allocHeap Heap.empty 3) := by
  native_decide

theorem freshInitAllocator_run :
    (match (Machine.evalFuel allocCtx 50 []
        (.call "freshInitAllocator" [])).run
          { next := 4, cells := [(2, 7)] } with
      | (some _, final) => some final
      | (none, _) => none) = some Heap.empty := by
  native_decide

theorem eraseFreedStart_run :
    (match (Machine.evalFuel allocCtx 50 []
        (.call "eraseFreedStart" [termPtr 2])).run
          { next := 4, cells := [(2, 7)] } with
      | (some _, final) => some final
      | (none, _) => none) =
    some (Heap.write { next := 4, cells := [(2, 7)] } ⟨2⟩ 0) := by
  native_decide

end Zag.Test.Autocorres.Examples
