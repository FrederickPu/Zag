import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Kmalloc.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Kmalloc.thy).

The upstream theory is primarily a C-parser/AUXUPD test. Zag has no typed heap descriptor,
`ptr_retyp`, parser body, or fixed-width overflow, so none of those checks are replaced by ordinary
block typing. The pure model below
follows the 1024-byte successor chain, uses the source bit-mask alignment test over `Nat`, requires
the non-null successor retained by the C allocation loop, updates chain links, zeroes allocated
words, and reinserts freed chunks.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev kmallocBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    kmallocFresh(size : Nat) : Ptr {
      ret op "allocPtr"[size]
    },
    kfreeErase(ptr : Ptr) : Unit {
      ret op "store"[ptr, nat(0)]
    }
  ]

theorem kmallocBlocksValid : BlockCtx.Valid kmallocBlocks := by
  valid_blocks [kmallocBlocks]

abbrev kmallocCtx : Ctx := mkCtx kmallocBlocks kmallocBlocksValid

theorem kmallocCtx_wellTyped : Ctx.WellTyped kmallocCtx := by
  typecheck_ctx

private abbrev kmallocStateCtx : Ctx := heapStateCtx kmallocBlocks kmallocBlocksValid

abbrev KMemory := Nat → Nat

def kmallocChunkSize : Nat := 1024

def kmallocRoundedSize (size : Nat) : Nat :=
  max size kmallocChunkSize

def kmallocChunkCount (size : Nat) : Nat :=
  kmallocRoundedSize size / kmallocChunkSize

def kfreeChunkCount (size : Nat) : Nat :=
  (kmallocRoundedSize size + kmallocChunkSize - 1) / kmallocChunkSize

def kmallocAligned (address size : Nat) : Bool :=
  decide (bitAnd address (kmallocRoundedSize size - 1) = 0)

def contiguousChunkPrefix : List Nat → Nat → Nat → Bool
| _, _, 0 => true
| [], _, _ + 1 => false
| address :: rest, expected, count + 1 =>
    decide (address = expected) &&
      contiguousChunkPrefix rest (expected + kmallocChunkSize) count

def selectKmallocRun (size : Nat) : List Nat → Option (Nat × List Nat)
| [] => none
| free@(_ :: rest) =>
    let start := free.head!
    let count := kmallocChunkCount size
    if decide (kmallocAligned start size = true ∧ contiguousChunkPrefix free start count = true ∧
        count < free.length) then
      some (start, free.drop count)
    else
      match selectKmallocRun size rest with
      | some (selected, remaining) => some (selected, start :: remaining)
      | none => none

def findKmallocRun (free : List Nat) (size : Nat) : Option Nat :=
  (selectKmallocRun size free).map Prod.fst

theorem selectKmallocRun_uses_matching_head {start : Nat} {rest : List Nat} {size : Nat}
    (haligned : kmallocAligned start size = true)
    (hprefix : contiguousChunkPrefix (start :: rest) start (kmallocChunkCount size) = true)
    (hsuccessor : kmallocChunkCount size < (start :: rest).length) :
    selectKmallocRun size (start :: rest) =
      some (start, (start :: rest).drop (kmallocChunkCount size)) := by
  have hsuccessor' : kmallocChunkCount size < rest.length + 1 := by
    simpa using hsuccessor
  simp only [selectKmallocRun]
  rw [show (start :: rest).head! = start by rfl]
  simp [haligned, hprefix, hsuccessor']

theorem kmalloc_two_chunk_tail_is_not_allocatable :
    selectKmallocRun 2048 [2048, 3072] = none := by
  native_decide

theorem kmalloc_non_power_two_uses_source_mask :
    kmallocAligned 3072 3072 = false := by
  native_decide

def zeroWords (memory : KMemory) (start count : Nat) : KMemory :=
  fun address => if start ≤ address ∧ address < start + count then 0 else memory address

def writeKMemory (memory : KMemory) (address value : Nat) : KMemory :=
  fun candidate => if candidate = address then value else memory candidate

def writeFreeLinks : KMemory → List Nat → KMemory
| memory, [] => memory
| memory, address :: rest =>
    let successor := rest.head?.getD 0
    writeFreeLinks (writeKMemory memory (address / 4) successor) rest

structure KmallocState where
  freeChunks : List Nat
  memory : KMemory

structure KmallocResult where
  state : KmallocState
  ptr : Ptr

def kmallocModel (state : KmallocState) (size : Nat) : Option KmallocResult :=
  match selectKmallocRun size state.freeChunks with
  | none => none
  | some (start, freeChunks) =>
      some {
        ptr := ⟨start⟩
        state := {
          freeChunks
          memory := zeroWords (writeFreeLinks state.memory freeChunks)
            (start / 4) (kmallocRoundedSize size / 4)
        }
      }

def insertChunk (address : Nat) : List Nat → List Nat
| [] => [address]
| current :: rest =>
    if address ≤ current then address :: current :: rest else current :: insertChunk address rest

def kfreeModel (state : KmallocState) (ptr : Ptr) (size : Nat) : KmallocState :=
  let chunks := (List.range (kfreeChunkCount size)).map fun i =>
    ptr.addr + kmallocChunkSize * i
  let freeChunks := chunks.foldl (fun free address => insertChunk address free) state.freeChunks
  { freeChunks, memory := writeFreeLinks state.memory freeChunks }

def FreeChainRep (state : KmallocState) : Prop :=
  writeFreeLinks state.memory state.freeChunks = state.memory

def KmallocPre (state : KmallocState) (_size : Nat) : Prop :=
  state.freeChunks.Nodup ∧ state.freeChunks.Pairwise (· < ·) ∧
  (∀ address ∈ state.freeChunks, address ≠ 0) ∧ FreeChainRep state

def KfreePre (state : KmallocState) (ptr : Ptr) (size : Nat) : Prop :=
  KmallocPre state size ∧ ptr ≠ null ∧
  ∀ i, i < kfreeChunkCount size →
    ptr.addr + kmallocChunkSize * i ∉ state.freeChunks

theorem zeroWords_inside (memory : KMemory) {start count offset : Nat} (h : offset < count) :
    zeroWords memory start count (start + offset) = 0 := by
  simp [zeroWords]
  omega

theorem zeroWords_frame (memory : KMemory) {start count address : Nat}
    (h : address < start ∨ start + count ≤ address) :
    zeroWords memory start count address = memory address := by
  simp [zeroWords]
  omega

theorem kmallocModel_success {state : KmallocState} {size start : Nat}
    {remaining : List Nat}
    (h : selectKmallocRun size state.freeChunks = some (start, remaining)) :
    kmallocModel state size = some {
      ptr := ⟨start⟩
      state := {
        freeChunks := remaining
        memory := zeroWords (writeFreeLinks state.memory remaining)
          (start / 4) (kmallocRoundedSize size / 4)
      }
    } := by
  simp [kmallocModel, h]

theorem kmallocModel_zeroes_words {state next : KmallocState} {size : Nat} {ptr : Ptr}
    (h : kmallocModel state size = some { state := next, ptr })
    {offset : Nat} (hoffset : offset < kmallocRoundedSize size / 4) :
    next.memory (ptr.addr / 4 + offset) = 0 := by
  simp [kmallocModel] at h
  split at h <;> simp_all
  rw [← h.1, ← h.2]
  exact zeroWords_inside _ hoffset

theorem kfreeModel_reinserts_single_chunk (state : KmallocState) (ptr : Ptr) :
    (kfreeModel state ptr kmallocChunkSize).freeChunks = insertChunk ptr.addr state.freeChunks := by
  simp [kfreeModel, kmallocChunkSize, kfreeChunkCount, kmallocRoundedSize]

theorem kmalloc_1025_uses_one_chunk_and_retains_successor :
    kmallocChunkCount 1025 = 1 ∧
    selectKmallocRun 1025 [2048, 3072] = some (2048, [3072]) := by
  native_decide

theorem kfreeModel_1025_reinserts_partial_chunk (state : KmallocState) (ptr : Ptr) :
    (kfreeModel state ptr 1025).freeChunks =
      insertChunk (ptr.addr + kmallocChunkSize) (insertChunk ptr.addr state.freeChunks) := by
  simp [kfreeModel, kfreeChunkCount, kmallocRoundedSize, kmallocChunkSize, List.range_succ]

private theorem kmallocFresh_evaluates_state (heap : Heap) (size : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks kmallocBlocks kmallocBlocksValid) "kmallocFresh"
      [.nat size] heap (valPtr (Heap.allocPtr heap)) (Heap.allocHeap heap size) := by
  zvcgen [kmallocBlocks, checkedBlocks, allocPtrOp, Op.effectful,
    Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?,
    Term.nat, valPtr, Val.ty_nat, Val.mk_ofNat, Val.asNat?_nat,
    driveOp_apply_done, resume_dependent_apply_done, allocPtrOp_action_val,
    alloc, Heap.allocPtr, Heap.allocHeap]

private theorem kfreeErase_evaluates_state (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks kmallocBlocks kmallocBlocksValid) "kfreeErase"
      [termPtr ptr.addr] heap valUnit (Heap.write heap ptr 0) := by
  rcases ptr with ⟨ptr⟩
  zvcgen [kmallocBlocks, checkedBlocks, storeOp, Op.effectful, Op.Body.collect,
    Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
    termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat, Val.mk_ofNat,
    Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
    resume_dependent_apply_done, resume_store_value_operand,
    storeValAction_spec, storeOp_action_spec, storeOp_action_vals]

/-- Fresh allocation from an unconstrained heap; post packages the alloc model. -/
@[zspec] theorem kmallocFresh_spec (size : Nat) :
    Zag.EvaluatesCall kmallocStateCtx "kmallocFresh" [.nat size]
      (fun _ => ⌜True⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜∃ h0 : Heap, True ∧ result = valPtr (Heap.allocPtr h0) ∧
          final = Heap.allocHeap h0 size⌝) :=
  evaluatesCall_of_prop "kmallocFresh" _
    (fun _ => True)
    (fun h => valPtr (Heap.allocPtr h))
    (fun h => Heap.allocHeap h size)
    (fun h _ => kmallocFresh_evaluates_state h size)

/--
```
{ ptr ↦ old }
  kfreeErase(ptr)
{ ptr ↦ 0 }
```
-/
@[zspec] theorem kfreeErase_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall kmallocStateCtx "kfreeErase" [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (ptr ↦ 0).holds final⌝) :=
  evaluatesCall_of_hprop "kfreeErase" _
    (ptr ↦ old)
    (fun _ => ptr ↦ 0)
    valUnit
    (fun h => Heap.write h ptr 0)
    (fun h => kfreeErase_evaluates_state h ptr)
    (fun h _hp =>
      (cell_pointsTo_holds ptr 0 (Heap.write h ptr 0)).2
        (by simp [Heap.read, Heap.write]))

theorem kmallocFresh_run :
    (match (Machine.evalFuel kmallocCtx 50 []
        (.call "kmallocFresh" [.nat 3])).run Heap.empty with
      | (some value, final) => (asPtr? value, final)
      | (none, final) => (none, final)) =
    (some (Heap.allocPtr Heap.empty), Heap.allocHeap Heap.empty 3) := by
  native_decide

theorem kfreeErase_run :
    (match (Machine.evalFuel kmallocCtx 50 []
        (.call "kfreeErase" [termPtr 2])).run
          { next := 4, cells := [(2, 7)] } with
      | (some _, final) => some final
      | (none, _) => none) =
    some (Heap.write { next := 4, cells := [(2, 7)] } ⟨2⟩ 0) := by
  native_decide

end Zag.Test.Autocorres.Examples
