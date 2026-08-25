import Test.Autocorres.Examples.Common

/-!
The upstream
[`Incremental.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Incremental.thy)
re-runs AutoCorres over selected functions from `type_strengthen.c`.

This file does not model AutoCorres incremental translation. Zag has no translation cache, scope
selection, generated SIMPL wrapper, per-function translation options, or complete translation of
the upstream final scope; those facilities are unsupported. Instead, the manually authored blocks
give PeanoHeap semantics to the selected source functions `opt_j`, `st_i`, `st_g`, `st_h`, and
`pure_f`. Ordinary `BlockCtx` extensions exercise that existing definitions remain callable after
new blocks are appended, without claiming that any translation phase was resumed.

A `struct ure` occupies two cells: `x` at offset 0 and the address of `n` at offset 1. C words and
casts are represented by `Nat` addresses, and invalid non-null pointer provenance remains outside
PeanoHeap.
The source `void pure_f(void)` is represented by the canonical unit stand-in `Nat` value `0`.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev incrementalOptJBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    optJ(p : Ptr, l : Ptr) : Nat {
      pNull := op "ptrIsNull"[p];
      ret if pNull { call optJ [p, l] } else {
        if op "ptrIsNull"[l] { call optJ [p, l] } else {
          if op "le"[op "load"[p], op "load"[l]] { nat(1) } else { nat(0) }
        }
      }
    }
  ]

abbrev incrementalStIBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    stI(p : Ptr, l : Ptr) : Ptr {
      ordered := call optJ [p, l];
      orderedFalse := primEq ordered nat(0);
      ret if orderedFalse {
        call stIRecurse [p, l]
      } else {
        call stIBase [p, l]
      }
    },
    stIBase(p : Ptr, l : Ptr) : Ptr {
      pNextField := op "ptrAdd"[p, nat(1)];
      lNextField := op "ptrAdd"[l, nat(1)];
      lNextAddr := op "load"[lNextField];
      updated := op "store"[pNextField, lNextAddr];
      ret p
    },
    stIRecurse(p : Ptr, l : Ptr) : Ptr {
      lNextField := op "ptrAdd"[l, nat(1)];
      lNextAddr := op "load"[lNextField];
      recursivePtr := call stI [p, op "ptrOfNat"[lNextAddr]];
      updated := op "store"[lNextField, op "ptrAddr"[recursivePtr]];
      ret l
    }
  ]

abbrev incrementalStGHBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    stG(ptr : Ptr) : Nat {
      updated := op "store"[ptr, nat(42)];
      ret op "load"[ptr]
    },
    stH(address : Nat) : Nat {
      ret call stG [op "ptrOfNat"[address]]
    }
  ]

abbrev incrementalPureFBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    pureF() : Nat {
      ret nat(0)
    }
  ]

abbrev incrementalWithStIBlocks := incrementalOptJBlocks ++ incrementalStIBlocks
abbrev incrementalWithStGHBlocks := incrementalWithStIBlocks ++ incrementalStGHBlocks
abbrev incrementalBlocks := incrementalWithStGHBlocks ++ incrementalPureFBlocks
abbrev incrementalProgramBlocks := incrementalBlocks

theorem incrementalOptJValid : BlockCtx.Valid incrementalOptJBlocks := by
  valid_blocks [incrementalOptJBlocks]

theorem incrementalWithStIValid : BlockCtx.Valid incrementalWithStIBlocks := by
  valid_blocks [incrementalWithStIBlocks, incrementalOptJBlocks, incrementalStIBlocks]

theorem incrementalWithStGHValid : BlockCtx.Valid incrementalWithStGHBlocks := by
  valid_blocks [incrementalWithStGHBlocks, incrementalWithStIBlocks,
    incrementalOptJBlocks, incrementalStIBlocks, incrementalStGHBlocks]

theorem incrementalBlocksValid : BlockCtx.Valid incrementalBlocks := by
  valid_blocks [incrementalBlocks, incrementalWithStGHBlocks, incrementalWithStIBlocks,
    incrementalOptJBlocks, incrementalStIBlocks, incrementalStGHBlocks,
    incrementalPureFBlocks]

abbrev incrementalOptJCtx : Ctx :=
  mkCtx incrementalOptJBlocks incrementalOptJValid
abbrev incrementalWithStICtx : Ctx :=
  mkCtx incrementalWithStIBlocks incrementalWithStIValid
abbrev incrementalWithStGHCtx : Ctx :=
  mkCtx incrementalWithStGHBlocks incrementalWithStGHValid
abbrev incrementalCtx : Ctx := mkCtx incrementalBlocks incrementalBlocksValid

private abbrev incrementalOptJStateCtx : Ctx :=
  heapStateCtx incrementalOptJBlocks incrementalOptJValid
private abbrev incrementalWithStIStateCtx : Ctx :=
  heapStateCtx incrementalWithStIBlocks incrementalWithStIValid
private abbrev incrementalWithStGHStateCtx : Ctx :=
  heapStateCtx incrementalWithStGHBlocks incrementalWithStGHValid

theorem incrementalExtensions_wellTyped :
    Ctx.WellTyped incrementalOptJCtx ∧ Ctx.WellTyped incrementalWithStICtx ∧
    Ctx.WellTyped incrementalWithStGHCtx ∧ Ctx.WellTyped incrementalCtx := by
  constructor
  · typecheck_ctx
  constructor
  · typecheck_ctx
  constructor <;> typecheck_ctx

/-- Ordinary context extension retains the exact installed definitions. -/
theorem incremental_definitions_retained_across_extensions :
    incrementalOptJCtx.blockCtx.get? "optJ" = some incrementalOptJBlocks[0].2 ∧
    incrementalWithStICtx.blockCtx.get? "optJ" = some incrementalOptJBlocks[0].2 ∧
    incrementalWithStGHCtx.blockCtx.get? "optJ" = some incrementalOptJBlocks[0].2 ∧
    incrementalCtx.blockCtx.get? "optJ" = some incrementalOptJBlocks[0].2 ∧
    incrementalWithStICtx.blockCtx.get? "stI" = some incrementalStIBlocks[0].2 ∧
    incrementalWithStGHCtx.blockCtx.get? "stI" = some incrementalStIBlocks[0].2 ∧
    incrementalCtx.blockCtx.get? "stI" = some incrementalStIBlocks[0].2 ∧
    incrementalWithStGHCtx.blockCtx.get? "stG" = some incrementalStGHBlocks[0].2 ∧
    incrementalCtx.blockCtx.get? "stG" = some incrementalStGHBlocks[0].2 ∧
    incrementalWithStGHCtx.blockCtx.get? "stH" = some incrementalStGHBlocks[1].2 ∧
    incrementalCtx.blockCtx.get? "stH" = some incrementalStGHBlocks[1].2 ∧
    incrementalCtx.blockCtx.get? "pureF" = some incrementalPureFBlocks[0].2 := by
  repeat' apply And.intro
  all_goals rfl

def incrementalHeap : Heap :=
  { next := 7, cells := [(1, 1), (2, 0), (3, 2), (4, 0), (5, 9), (6, 0)] }

def incrementalP : Ptr := ⟨1⟩
def incrementalL : Ptr := ⟨3⟩
def incrementalCell : Ptr := ⟨5⟩

def incrementalNextField (ptr : Ptr) : Ptr :=
  ⟨ptr.addr + 1⟩

def incrementalPure (P : Prop) : HProp Heap OwnedPtr Region (fun _ => Nat) where
  region := ⊥
  holds := fun _ => P
  supported := by intro _ _ _; exact Iff.rfl

theorem incrementalPtrEqOfAddrEq {p q : Ptr} (h : p.addr = q.addr) : p = q := by
  rcases p with ⟨p⟩
  rcases q with ⟨q⟩
  simp at h ⊢
  exact h

def aliasCells (p q : Ptr) (pv qv : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  if _h : p = q then incrementalPure (pv = qv) ∗ (p ↦ pv)
  else (p ↦ pv) ∗ (q ↦ qv)

def incrementalOptJFootprint (p l : Ptr) (pv lv : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  incrementalPure (p ≠ null ∧ l ≠ null) ∗ aliasCells p l pv lv

def incrementalStIBaseFootprint (p l : Ptr) (pNextOld lNextAddr : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  aliasCells (incrementalNextField p) (incrementalNextField l) pNextOld lNextAddr

def incrementalStIBasePost (p l : Ptr) (lNextAddr : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  aliasCells (incrementalNextField p) (incrementalNextField l) lNextAddr lNextAddr

def incrementalStructFootprint (ptr : Ptr) (data nextAddr : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (ptr ↦ data) ∗ (incrementalNextField ptr ↦ nextAddr)

def incrementalNodesFootprint : List Ptr → List Nat → List Nat →
    HProp Heap OwnedPtr Region (fun _ => Nat)
| [], [], [] => incrementalPure True
| node :: nodes, value :: values, nextAddr :: nextAddrs =>
    incrementalStructFootprint node value nextAddr ∗
      incrementalNodesFootprint nodes values nextAddrs
| _, _, _ => incrementalPure False

def IncrementalStIPathValues (p : Ptr) (pValue : Nat) :
    List Ptr → List Nat → List Nat → Prop
| [l], [lValue], [_lNextAddr] =>
    p ≠ null ∧ l ≠ null ∧ pValue ≤ lValue
| l :: next :: nodes, lValue :: nextValue :: values, lNextAddr :: nextAddrs =>
    p ≠ null ∧ l ≠ null ∧ lValue < pValue ∧ lNextAddr = next.addr ∧
      IncrementalStIPathValues p pValue (next :: nodes) (nextValue :: values) nextAddrs
| _, _, _ => False

def incrementalStIFootprint (p current : Ptr) (nodes : List Ptr)
    (pValue pNextOld : Nat) (nodeValues nextAddrs : List Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  incrementalPure (IncrementalStIPathValues p pValue (current :: nodes) nodeValues nextAddrs) ∗
    incrementalStructFootprint p pValue pNextOld ∗
      incrementalNodesFootprint (current :: nodes) nodeValues nextAddrs

def heapSnapshot (region : Region) (snapshot : Heap) :
    HProp Heap OwnedPtr Region (fun _ => Nat) where
  region := region
  holds h := ∀ addr, addr ∈ region → Heap.read h ⟨addr⟩ = Heap.read snapshot ⟨addr⟩
  supported := by
    intro h h' hd
    constructor
    · intro hs addr hmem
      have hsame : Heap.read h ⟨addr⟩ = Heap.read h' ⟨addr⟩ := by
        by_contra hneq
        exact Set.disjoint_right.mp hd hmem hneq
      exact hsame.symm.trans (hs addr hmem)
    · intro hs addr hmem
      have hsame : Heap.read h ⟨addr⟩ = Heap.read h' ⟨addr⟩ := by
        by_contra hneq
        exact Set.disjoint_right.mp hd hmem hneq
      exact hsame.trans (hs addr hmem)

theorem heapSnapshot_self (region : Region) (snapshot : Heap) :
    (heapSnapshot region snapshot).holds snapshot := by
  intro _ _
  rfl

theorem aliasCells_reads {heap : Heap} {p q : Ptr} {pv qv : Nat}
    (hp : (aliasCells p q pv qv).holds heap) :
    Heap.read heap p = pv ∧ Heap.read heap q = qv := by
  by_cases hsame : p = q
  · subst q
    rw [aliasCells, dif_pos rfl] at hp
    rcases hp with ⟨_hsep, hpv, hpoint⟩
    have hread := (cell_pointsTo_holds p pv heap).1 hpoint
    exact ⟨hread, hread.trans hpv⟩
  · rw [aliasCells, dif_neg hsame] at hp
    rcases hp with ⟨_hsep, hpPoint, hqPoint⟩
    exact ⟨(cell_pointsTo_holds p pv heap).1 hpPoint,
      (cell_pointsTo_holds q qv heap).1 hqPoint⟩

theorem aliasCells_write_left {heap : Heap} {p q : Ptr} {old qv : Nat}
    (hp : (aliasCells p q old qv).holds heap) :
    (aliasCells p q qv qv).holds (Heap.write heap p qv) := by
  by_cases hsame : p = q
  · subst q
    rw [aliasCells, dif_pos rfl] at hp ⊢
    refine ⟨by simp [incrementalPure], rfl, ?_⟩
    exact (cell_pointsTo_holds p qv (Heap.write heap p qv)).2
      (HeapAlgebra.Peano.Heap.read_write_same heap p qv)
  · rw [aliasCells, dif_neg hsame] at hp ⊢
    rcases hp with ⟨hsep, _hpOld, hqPoint⟩
    refine ⟨by simpa [pointsToVal, HProp.pointsTo] using hsep, ?_, ?_⟩
    · exact (cell_pointsTo_holds p qv (Heap.write heap p qv)).2
        (HeapAlgebra.Peano.Heap.read_write_same heap p qv)
    · have hread := (cell_pointsTo_holds q qv heap).1 hqPoint
      have haddr : q.addr ≠ p.addr := by
        intro heq
        exact hsame (incrementalPtrEqOfAddrEq heq.symm)
      exact (cell_pointsTo_holds q qv (Heap.write heap p qv)).2
        ((HeapAlgebra.Peano.Heap.read_write_of_ne heap p q qv haddr).trans hread)

theorem incrementalOptJFootprint_parts {heap : Heap} {p l : Ptr} {pv lv : Nat}
    (hp : (incrementalOptJFootprint p l pv lv).holds heap) :
    p ≠ null ∧ l ≠ null ∧ Heap.read heap p = pv ∧ Heap.read heap l = lv := by
  change (incrementalPure (p ≠ null ∧ l ≠ null) ∗ aliasCells p l pv lv).holds heap at hp
  rcases hp with ⟨_hsep, hnonnull, hcells⟩
  exact ⟨hnonnull.1, hnonnull.2, aliasCells_reads hcells⟩

theorem incrementalStIBaseFootprint_write (heap : Heap) (p l : Ptr)
    (pNextOld lNextAddr : Nat)
    (hp : (incrementalStIBaseFootprint p l pNextOld lNextAddr).holds heap) :
    (incrementalStIBasePost p l lNextAddr).holds
      (Heap.write heap (incrementalNextField p)
        (Heap.read heap (incrementalNextField l))) := by
  have hreads := aliasCells_reads hp
  have hsource : Heap.read heap (incrementalNextField l) = lNextAddr := hreads.2
  simpa [incrementalStIBaseFootprint, incrementalStIBasePost, hsource] using
    aliasCells_write_left (p := incrementalNextField p) (q := incrementalNextField l)
      (old := pNextOld) (qv := lNextAddr) hp

def IncrementalStIPath (heap : Heap) (p : Ptr) : List Ptr → Prop
| [] => False
| [l] => p ≠ null ∧ l ≠ null ∧ Heap.read heap p ≤ Heap.read heap l
| l :: next :: nodes =>
    p ≠ null ∧ l ≠ null ∧ Heap.read heap l < Heap.read heap p ∧
      Heap.read heap (incrementalNextField l) = next.addr ∧
      IncrementalStIPath heap p (next :: nodes)

theorem incrementalStructFootprint_reads {heap : Heap} {ptr : Ptr} {data nextAddr : Nat}
    (hp : (incrementalStructFootprint ptr data nextAddr).holds heap) :
    Heap.read heap ptr = data ∧ Heap.read heap (incrementalNextField ptr) = nextAddr := by
  change ((ptr ↦ data) ∗ (incrementalNextField ptr ↦ nextAddr)).holds heap at hp
  rcases hp with ⟨_hsep, hdata, hnext⟩
  exact ⟨(cell_pointsTo_holds ptr data heap).1 hdata,
    (cell_pointsTo_holds (incrementalNextField ptr) nextAddr heap).1 hnext⟩

theorem incrementalStIPathValues_sound {heap : Heap} {p : Ptr} {pValue : Nat}
    {path : List Ptr} {nodeValues nextAddrs : List Nat}
    (hvalues : IncrementalStIPathValues p pValue path nodeValues nextAddrs)
    (hpRead : Heap.read heap p = pValue)
    (hnodes : (incrementalNodesFootprint path nodeValues nextAddrs).holds heap) :
    IncrementalStIPath heap p path := by
  induction path generalizing nodeValues nextAddrs with
  | nil =>
      simp [IncrementalStIPathValues] at hvalues
  | cons node rest ih =>
      cases rest with
      | nil =>
          cases nodeValues with
          | nil => simp [IncrementalStIPathValues] at hvalues
          | cons nodeValue valueTail =>
              cases valueTail with
              | nil =>
                  cases nextAddrs with
                  | nil => simp [IncrementalStIPathValues] at hvalues
                  | cons nextAddr nextTail =>
                      cases nextTail with
                      | nil =>
                          change (incrementalStructFootprint node nodeValue nextAddr ∗
                            incrementalNodesFootprint [] [] []).holds heap at hnodes
                          rcases hnodes with ⟨_hsep, hnodeStruct, _htail⟩
                          have hnodeRead := (incrementalStructFootprint_reads hnodeStruct).1
                          change p ≠ null ∧ node ≠ null ∧ Heap.read heap p ≤ Heap.read heap node
                          exact ⟨hvalues.1, hvalues.2.1, by
                            calc
                              Heap.read heap p = pValue := hpRead
                              _ ≤ nodeValue := hvalues.2.2
                              _ = Heap.read heap node := hnodeRead.symm⟩
                      | cons _ _ => simp [IncrementalStIPathValues] at hvalues
              | cons _ _ => simp [IncrementalStIPathValues] at hvalues
      | cons next nodes =>
          cases nodeValues with
          | nil => simp [IncrementalStIPathValues] at hvalues
          | cons nodeValue valueTail =>
              cases valueTail with
              | nil => simp [IncrementalStIPathValues] at hvalues
              | cons nextValue valuesTail =>
                  cases nextAddrs with
                  | nil => simp [IncrementalStIPathValues] at hvalues
                  | cons nodeNextAddr nextAddrsTail =>
                      change (incrementalStructFootprint node nodeValue nodeNextAddr ∗
                        incrementalNodesFootprint (next :: nodes) (nextValue :: valuesTail)
                          nextAddrsTail).holds heap at hnodes
                      rcases hnodes with ⟨_hsep, hnodeStruct, htailNodes⟩
                      have hnodeReads := incrementalStructFootprint_reads hnodeStruct
                      have htail := ih hvalues.2.2.2.2 htailNodes
                      change p ≠ null ∧ node ≠ null ∧ Heap.read heap node < Heap.read heap p ∧
                        Heap.read heap (incrementalNextField node) = next.addr ∧
                        IncrementalStIPath heap p (next :: nodes)
                      exact ⟨hvalues.1, hvalues.2.1, by
                        calc
                          Heap.read heap node = nodeValue := hnodeReads.1
                          _ < pValue := hvalues.2.2.1
                          _ = Heap.read heap p := hpRead.symm,
                        hnodeReads.2.trans hvalues.2.2.2.1, htail⟩

theorem incrementalStIFootprint_path {heap : Heap} {p current : Ptr} {nodes : List Ptr}
    {pValue pNextOld : Nat} {nodeValues nextAddrs : List Nat}
    (hp : (incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs).holds heap) :
    IncrementalStIPath heap p (current :: nodes) := by
  change (incrementalPure
    (IncrementalStIPathValues p pValue (current :: nodes) nodeValues nextAddrs) ∗
      incrementalStructFootprint p pValue pNextOld ∗
        incrementalNodesFootprint (current :: nodes) nodeValues nextAddrs).holds heap at hp
  rcases hp with ⟨_hsepPure, hvalues, hrest⟩
  rcases hrest with ⟨_hsepCells, hpStruct, hnodes⟩
  exact incrementalStIPathValues_sound hvalues
    (incrementalStructFootprint_reads hpStruct).1 hnodes

def incrementalStIModel : Heap → Ptr → List Ptr → Heap × Ptr
| heap, p, [] => (heap, p)
| heap, p, [l] =>
    (Heap.write heap (incrementalNextField p)
      (Heap.read heap (incrementalNextField l)), p)
| heap, p, l :: next :: nodes =>
    let recursive := incrementalStIModel heap p (next :: nodes)
    (Heap.write recursive.1 (incrementalNextField l) recursive.2.addr, l)

def incrementalStIResult (p : Ptr) : List Ptr → Ptr
| [] => p
| [_] => p
| l :: _ :: _ => l

theorem incrementalStIModel_result (heap : Heap) (p : Ptr) (path : List Ptr) :
    (incrementalStIModel heap p path).2 = incrementalStIResult p path := by
  cases path with
  | nil => rfl
  | cons current rest =>
      cases rest with
      | nil => rfl
      | cons next nodes => rfl

def incrementalStIModelPost (initial : Heap) (p current : Ptr) (nodes : List Ptr)
    (pValue pNextOld : Nat) (nodeValues nextAddrs : List Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  heapSnapshot
    (incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs).region
    (incrementalStIModel initial p (current :: nodes)).1

private theorem incrementalOptJ_evaluates_values
    (blockCtx : BlockCtx heapCtx)
    (hblock : blockCtx.get? "optJ" = some incrementalOptJBlocks[0].2)
    (heap : Heap) (p l : Ptr) (hp : p ≠ null) (hl : l ≠ null) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx blockCtx
      "optJ" [valPtr p, valPtr l] heap
      (Val.nat (if Heap.read heap p ≤ Heap.read heap l then 1 else 0)) heap := by
  have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hite : heapOpCtx.get? "ite" = some Op.ite := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hle : heapOpCtx.get? "le" =
      some (binaryNatBoolOp fun a b => decide (a ≤ b)) := by
    rfl
  by_cases hordered : Heap.read heap p ≤ Heap.read heap l
  all_goals
    intro env base
    refine ⟨_, _, hblock, by rfl, ?_⟩
    repeat
      first
      | simpa [hordered] using
          (EvalTriple.State.EvaluatesFrom.done (primCtx := heapCtx) (opCtx := heapOpCtx)
            (blockCtx := blockCtx) (state := heap)
            (value := Val.nat (if Heap.read heap p ≤ Heap.read heap l then 1 else 0)))
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · first
          | change Id.run ((Machine.step
              (Machine.stateCtx heapCtx heapOpCtx blockCtx) _).run heap) = _
            simpa using loadOp_step blockCtx _ _ heap p
          | change Id.run ((Machine.step
              (Machine.stateCtx heapCtx heapOpCtx blockCtx) _).run heap) = _
            simpa using loadOp_step blockCtx _ _ heap l
          | set_option linter.unusedSimpArgs false in
              simp [incrementalOptJBlocks, Machine.step, Machine.evalTerm,
                Machine.applyValue, Machine.driveSelectedOp, Machine.ofOption,
                Machine.evalTermImmediate, Machine.applyValueImmediate, Machine.resumeFrame,
                Machine.enterBlock, Machine.enterInstrs, Machine.driveOp,
                hptrIsNull, hite, hload, hle, hp, hl, hordered, ptrIsNullOp, loadOp,
                binaryNatBoolOp, Op.ite, Op.effectful, Op.Body.collect,
                Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
                Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr, valPtr,
                valUnit, asPtr?]
            rfl

theorem incrementalOptJ_evaluates (heap : Heap) (p l : Ptr)
    (hp : p ≠ null) (hl : l ≠ null) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx incrementalOptJCtx.blockCtx
      "optJ" [termPtr p.addr, termPtr l.addr] heap
      (Val.nat (if Heap.read heap p ≤ Heap.read heap l then 1 else 0)) heap := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hcall := incrementalOptJ_evaluates_values incrementalOptJCtx.blockCtx
    (by rfl) heap p l hp hl
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [incrementalOptJCtx, mkCtx, incrementalOptJBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.driveSelectedOp,
            Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

@[zspec] theorem incrementalOptJ_spec (p l : Ptr) (pv lv : Nat) :
    Zag.EvaluatesCall incrementalOptJStateCtx
      "optJ" [termPtr p.addr, termPtr l.addr]
      (HProp.toAssertion (incrementalOptJFootprint p l pv lv))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat (if pv ≤ lv then 1 else 0) ∧
          (incrementalOptJFootprint p l pv lv).holds final⌝) :=
  evaluatesCall_of_hprop_pre (blocks := incrementalOptJBlocks)
    (hvalid := incrementalOptJValid) "optJ" _
    (incrementalOptJFootprint p l pv lv)
    (fun _ => incrementalOptJFootprint p l pv lv)
    (Val.nat (if pv ≤ lv then 1 else 0))
    (fun h => h)
    (fun h hp => by
      rcases incrementalOptJFootprint_parts hp with ⟨hpNonNull, hlNonNull, hpRead, hlRead⟩
      simpa [hpRead, hlRead] using incrementalOptJ_evaluates h p l hpNonNull hlNonNull)
    (fun _ hp => hp)

private theorem incrementalStIBase_evaluates_values (heap : Heap) (p l : Ptr) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx incrementalWithStICtx.blockCtx
      "stIBase" [valPtr p, valPtr l] heap (valPtr p)
      (Heap.write heap (incrementalNextField p)
        (Heap.read heap (incrementalNextField l))) := by
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  intro env base
  refine ⟨_, _, by rfl, by rfl, ?_⟩
  repeat
    apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
    · first
      | change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx incrementalWithStICtx.blockCtx) _).run heap) = _
        simpa using loadOp_step incrementalWithStICtx.blockCtx _ _ heap
          (incrementalNextField l)
      | set_option linter.unusedSimpArgs false in
          simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
            incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
            incrementalNextField, Machine.step, Machine.evalTerm,
            Machine.applyValue, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate, Machine.resumeFrame,
            Machine.enterBlock, Machine.enterInstrs, Machine.driveOp,
            hload, hstore, hptrAdd, loadOp, storeOp, ptrAddOp, Op.effectful,
            Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
            Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
            termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle :=
    Heap.write heap (incrementalNextField p) (Heap.read heap (incrementalNextField l)))
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx incrementalWithStICtx.blockCtx) _).run heap) = _
    simpa [incrementalNextField] using storeOp_step incrementalWithStICtx.blockCtx _ _ heap
      (incrementalNextField p) (Heap.read heap (incrementalNextField l))
  repeat
    first
    | exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle :=
        Heap.write heap (incrementalNextField p) (Heap.read heap (incrementalNextField l)))
      · set_option linter.unusedSimpArgs false in
          simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
            incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
            incrementalNextField, Machine.step, Machine.evalTerm,
            Machine.applyValue, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate, Machine.resumeFrame,
            Machine.enterBlock, Machine.enterInstrs, Machine.driveOp,
            hload, hstore, hptrAdd, loadOp, storeOp, ptrAddOp, Op.effectful,
            Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
            Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
            termPtr, valPtr, valUnit, asPtr?]
        rfl

theorem incrementalStIBase_evaluates (heap : Heap) (p l : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx incrementalWithStICtx.blockCtx
      "stIBase" [termPtr p.addr, termPtr l.addr] heap (valPtr p)
      (Heap.write heap (incrementalNextField p)
        (Heap.read heap (incrementalNextField l))) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hcall := incrementalStIBase_evaluates_values heap p l
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
            incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.driveSelectedOp,
            Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

@[zspec] theorem incrementalStIBase_spec (p l : Ptr) (pNextOld lNextAddr : Nat) :
    Zag.EvaluatesCall incrementalWithStIStateCtx
      "stIBase" [termPtr p.addr, termPtr l.addr]
      (HProp.toAssertion (incrementalStIBaseFootprint p l pNextOld lNextAddr))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr p ∧
          (incrementalStIBasePost p l lNextAddr).holds final⌝) :=
  evaluatesCall_of_hprop (blocks := incrementalWithStIBlocks)
    (hvalid := incrementalWithStIValid) "stIBase" _
    (incrementalStIBaseFootprint p l pNextOld lNextAddr)
    (fun _ => incrementalStIBasePost p l lNextAddr)
    (valPtr p)
    (fun h => Heap.write h (incrementalNextField p)
      (Heap.read h (incrementalNextField l)))
    (fun h => incrementalStIBase_evaluates h p l)
    (fun h hp => incrementalStIBaseFootprint_write h p l pNextOld lNextAddr hp)

theorem incrementalStI_evaluates_values {heap : Heap} {p current : Ptr} {nodes : List Ptr}
    (hpath : IncrementalStIPath heap p (current :: nodes)) :
    let model := incrementalStIModel heap p (current :: nodes)
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx incrementalWithStICtx.blockCtx
      "stI" [valPtr p, valPtr current] heap (valPtr model.2) model.1 := by
  dsimp only
  induction nodes generalizing heap current with
  | nil =>
      simp only [IncrementalStIPath] at hpath
      have hp := hpath.1
      have hcurrent := hpath.2.1
      have hordered := hpath.2.2
      have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by
        rfl
      have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by
        rfl
      have hopt := incrementalOptJ_evaluates_values incrementalWithStICtx.blockCtx
        (by rfl) heap p current hp hcurrent
      have hbase := incrementalStIBase_evaluates_values heap p current
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx incrementalWithStICtx.blockCtx
        _ heap (valPtr p)
        (Heap.write heap (incrementalNextField p)
          (Heap.read heap (incrementalNextField current))) base
      repeat
        first
        | apply EvalTriple.State.EvaluatesFrom.call_then hopt
          intro scope
          repeat
            first
            | exact EvalTriple.State.EvaluatesFrom.return_through_done_call
            | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
              · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                  Machine.driveOp, Op.Body.resume?, hordered]
                rfl
        | apply EvalTriple.State.EvaluatesFrom.call_then hbase
          intro scope
          exact EvalTriple.State.EvaluatesFrom.return_through_done_call
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                Machine.step, Machine.evalTerm, Machine.applyValue,
                Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
                Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
                Machine.enterInstrs, Machine.driveOp, hordered, heq, hite,
                Op.eq, Op.compare, Op.ite, Op.effectful,
                Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                Term.ite, termPtr, valPtr, valUnit, asPtr?]
            rfl
  | cons next nodes ih =>
      simp only [IncrementalStIPath] at hpath
      have hp := hpath.1
      have hcurrent := hpath.2.1
      have hless := hpath.2.2.1
      have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by
        rfl
      have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by
        rfl
      have hnextAddr := hpath.2.2.2.1
      have hnext : Ptr.mk (Heap.read heap (incrementalNextField current)) = next := by
        cases next
        simp_all
      have hnextLiteral : Ptr.mk (Heap.read heap ⟨current.addr + 1⟩) = next := by
        simpa [incrementalNextField] using hnext
      have hrec := ih (heap := heap) hpath.2.2.2.2
      let recursive := incrementalStIModel heap p (next :: nodes)
      have hrecRecursive :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx incrementalWithStICtx.blockCtx
            "stI" [valPtr p,
              valPtr ⟨Heap.read heap ⟨current.addr + 1⟩⟩] heap
              (valPtr recursive.2) recursive.1 := by
        simpa only [hnextLiteral, recursive] using hrec
      have hopt := incrementalOptJ_evaluates_values incrementalWithStICtx.blockCtx
        (by rfl) heap p current hp hcurrent
      let final := Heap.write recursive.1 (incrementalNextField current) recursive.2.addr
      have hrecurse :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx incrementalWithStICtx.blockCtx
            "stIRecurse" [valPtr p, valPtr current] heap (valPtr current) final := by
        have hload : heapOpCtx.get? "load" = some loadOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        have hstore : heapOpCtx.get? "store" = some storeOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        intro env base
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                incrementalNextField, Machine.step, Machine.evalTerm,
                Machine.applyValue, Machine.driveSelectedOp,
                Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock,
                Machine.enterInstrs, Machine.driveOp, hload, hstore,
                hptrAdd, hptrOfNat, hptrAddr, storeOp, ptrAddOp,
                ptrOfNatOp, ptrAddrOp, Op.effectful, Op.Body.collect,
                Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                Op.fixed, Block.entryEnv, Scope.get?, Term.nat, termPtr,
                valPtr, valUnit, asPtr?]
            rfl
        iterate 3
          apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [Machine.step, Machine.evalTerm,
                Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
                Machine.applyValueImmediate, Machine.resumeFrame, Machine.driveOp,
                hload, loadOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
                Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Scope.get?,
                valPtr, asPtr?]
            rfl
        apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx incrementalWithStICtx.blockCtx) _).run heap) = _
          simpa [incrementalNextField] using loadOp_step incrementalWithStICtx.blockCtx _ _ heap
            (incrementalNextField current)
        repeat
          first
          | apply EvalTriple.State.EvaluatesFrom.call_then hrecRecursive
            intro scope
            repeat
              first
              | apply EvalTriple.State.EvaluatesFrom.step (middle := final)
                · change Id.run ((Machine.step
                    (Machine.stateCtx heapCtx heapOpCtx incrementalWithStICtx.blockCtx) _).run
                      recursive.1) = _
                  simpa [final] using storeOp_step incrementalWithStICtx.blockCtx _ _
                    recursive.1 (incrementalNextField current) recursive.2.addr
              | exact EvalTriple.State.EvaluatesFrom.return_to_call
              | exact EvalTriple.State.EvaluatesFrom.done
              | apply EvalTriple.State.EvaluatesFrom.step (middle := recursive.1)
                · set_option linter.unusedSimpArgs false in
                    simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                      incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                      incrementalNextField, Machine.step, Machine.evalTerm,
                      Machine.applyValue, Machine.driveSelectedOp,
                      Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                      Machine.resumeFrame, Machine.enterBlock,
                      Machine.enterInstrs, Machine.driveOp, hload, hstore,
                      hptrAdd, hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp,
                      ptrOfNatOp, ptrAddrOp, Op.effectful, Op.Body.collect,
                      Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                      Op.fixed, Block.entryEnv, Scope.get?, Term.nat, termPtr,
                      valPtr, valUnit, asPtr?, hnext]
                  rfl
              | apply EvalTriple.State.EvaluatesFrom.step (middle := final)
                · set_option linter.unusedSimpArgs false in
                    simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                      incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                      incrementalNextField, Machine.step, Machine.evalTerm,
                      Machine.applyValue, Machine.driveSelectedOp,
                      Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                      Machine.resumeFrame, Machine.enterBlock,
                      Machine.enterInstrs, Machine.driveOp, hload, hstore,
                      hptrAdd, hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp,
                      ptrOfNatOp, ptrAddrOp, Op.effectful, Op.Body.collect,
                      Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                      Op.fixed, Block.entryEnv, Scope.get?, Term.nat, termPtr,
                      valPtr, valUnit, asPtr?]
                  rfl
          | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
            · set_option linter.unusedSimpArgs false in
                simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                  incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                  incrementalNextField, Machine.step, Machine.evalTerm,
                  Machine.applyValue, Machine.driveSelectedOp,
                  Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, hload, hstore,
                  hptrAdd, hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp,
                  ptrOfNatOp, ptrAddrOp, Op.effectful, Op.Body.collect,
                  Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                  Op.fixed, Block.entryEnv, Scope.get?, Term.nat, termPtr,
                  valPtr, valUnit, asPtr?, hnext]
              rfl
      let stICallerEnv : Env heapCtx :=
        [("p", valPtr p), ("l", valPtr current),
          ("ordered", Val.nat (if Heap.read heap p ≤ Heap.read heap current then 1 else 0)),
          ("orderedFalse", Val.bool true)]
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx incrementalWithStICtx.blockCtx
        _ heap (valPtr current) final base
      repeat
        first
        | apply EvalTriple.State.EvaluatesFrom.call_then hopt
          intro scope
          repeat
            first
            | exact EvalTriple.State.EvaluatesFrom.return_through_done_call
            | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
              · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                  Machine.driveOp, Op.Body.resume?, hless]
                rfl
        | apply EvalTriple.State.EvaluatesFrom.call_then hrecurse
          intro scope
          refine EvalTriple.State.EvaluatesFrom.step (middle := final) ?_
            (EvalTriple.State.EvaluatesFrom.return_to_call (name := "stI")
              (callerEnv := env) (scope := stICallerEnv) (stack := base)
              (state := final) (value := valPtr current))
          simp [stICallerEnv, Machine.step, Machine.ofOption,
            Machine.resumeFrame, Machine.driveOp]
          rfl
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
                incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
                Machine.step, Machine.evalTerm, Machine.applyValue,
                Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
                Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
                Machine.enterInstrs, Machine.driveOp, hless, heq, hite,
                Op.eq, Op.compare, Op.ite, Op.effectful,
                Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                Term.ite, termPtr, valPtr, valUnit, asPtr?]
            rfl

theorem incrementalStI_evaluates {heap : Heap} {p current : Ptr} {nodes : List Ptr}
    (hpath : IncrementalStIPath heap p (current :: nodes)) :
    let model := incrementalStIModel heap p (current :: nodes)
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx incrementalWithStICtx.blockCtx
      "stI" [termPtr p.addr, termPtr current.addr] heap (valPtr model.2) model.1 := by
  dsimp only
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hcall := incrementalStI_evaluates_values hpath
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [incrementalWithStICtx, mkCtx, incrementalWithStIBlocks,
            incrementalOptJBlocks, incrementalStIBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.driveSelectedOp,
            Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

@[zspec] theorem incrementalStI_spec (p current : Ptr) (nodes : List Ptr)
    (pValue pNextOld : Nat) (nodeValues nextAddrs : List Nat) :
    Zag.EvaluatesCall incrementalWithStIStateCtx
      "stI" [termPtr p.addr, termPtr current.addr]
      (HProp.toAssertion
        (incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr (incrementalStIResult p (current :: nodes)) ∧
          ∃ h0 : Heap,
            (incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs).holds h0 ∧
            (incrementalStIModelPost h0 p current nodes pValue pNextOld nodeValues nextAddrs).holds final⌝) := by
  let P := incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs
  let PreHeap := { heap : Heap // P.holds heap }
  change EvalTriple.EvaluatesFrom incrementalWithStIStateCtx
    (Machine.start [] (.call "stI" [termPtr p.addr, termPtr current.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion, P] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hpath : IncrementalStIPath hh.1 p (current :: nodes) := by
      exact incrementalStIFootprint_path (pValue := pValue) (pNextOld := pNextOld)
        (nodeValues := nodeValues) (nextAddrs := nextAddrs) (by simpa [P] using hh.2)
    have hex := incrementalStI_evaluates (heap := hh.1) (p := p) (current := current)
      (nodes := nodes) hpath
    have hresult := incrementalStIModel_result hh.1 p (current :: nodes)
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    refine ⟨by simp [hresult], hh.1, by simpa [P] using hh.2, ?_⟩
    exact heapSnapshot_self
      (incrementalStIFootprint p current nodes pValue pNextOld nodeValues nextAddrs).region
      (incrementalStIModel hh.1 p (current :: nodes)).1

private theorem incrementalStG_evaluates_values (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx incrementalWithStGHCtx.blockCtx
      "stG" [valPtr ptr] heap (Val.nat 42) (Heap.write heap ptr 42) := by
  have hload : heapOpCtx.get? "load" = some loadOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  intro env base
  refine ⟨_, _, by rfl, by rfl, ?_⟩
  repeat
    apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
    · set_option linter.unusedSimpArgs false in
        simp [incrementalWithStGHCtx, mkCtx, incrementalWithStGHBlocks,
          incrementalWithStIBlocks, incrementalOptJBlocks, incrementalStIBlocks,
          incrementalStGHBlocks, checkedBlocks, Machine.step,
          Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
          Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
          Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
          Machine.driveOp, hload, hstore, loadOp, storeOp, Op.effectful,
          Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
          Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
          termPtr, valPtr, valUnit, asPtr?]
      rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := Heap.write heap ptr 42)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx incrementalWithStGHCtx.blockCtx) _).run heap) = _
    simpa using storeOp_step incrementalWithStGHCtx.blockCtx _ _ heap ptr 42
  repeat
    first
    | exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := Heap.write heap ptr 42)
      · first
        | change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx incrementalWithStGHCtx.blockCtx) _).run
              (Heap.write heap ptr 42)) = _
          simpa [Heap.read, Heap.write] using loadOp_step incrementalWithStGHCtx.blockCtx
            _ _ (Heap.write heap ptr 42) ptr
        | set_option linter.unusedSimpArgs false in
            simp [incrementalWithStGHCtx, mkCtx, incrementalWithStGHBlocks,
              incrementalWithStIBlocks, incrementalOptJBlocks, incrementalStIBlocks,
              incrementalStGHBlocks, checkedBlocks, Machine.step,
              Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hload, hstore, loadOp,
              storeOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
              Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
              Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?, Heap.read,
              Heap.write]
          rfl

theorem incrementalStG_evaluates (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx incrementalWithStGHCtx.blockCtx
      "stG" [termPtr ptr.addr] heap (Val.nat 42) (Heap.write heap ptr 42) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hcall := incrementalStG_evaluates_values heap ptr
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [incrementalWithStGHCtx, mkCtx, incrementalWithStGHBlocks,
            incrementalWithStIBlocks, incrementalOptJBlocks, incrementalStIBlocks,
            incrementalStGHBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate, Machine.resumeFrame,
            Machine.enterBlock, Machine.enterInstrs, Machine.driveOp,
            Machine.start, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

theorem incrementalStH_evaluates (heap : Heap) (address : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx incrementalWithStGHCtx.blockCtx
      "stH" [Term.nat address] heap (Val.nat 42) (Heap.write heap ⟨address⟩ 42) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hg := incrementalStG_evaluates_values heap ⟨address⟩
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hg
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [incrementalWithStGHCtx, mkCtx, incrementalWithStGHBlocks,
            incrementalWithStIBlocks, incrementalOptJBlocks, incrementalStIBlocks,
            incrementalStGHBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, Machine.start,
            hptrOfNat, ptrOfNatOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

/--
```
{ ptr ↦ old }
  stG(ptr)
{ r = 42 ∧ ptr ↦ 42 }
```
-/
@[zspec] theorem incrementalStG_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall incrementalWithStGHStateCtx
      "stG" [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat 42 ∧ (ptr ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop (blocks := incrementalWithStGHBlocks)
    (hvalid := incrementalWithStGHValid) "stG" _
    (ptr ↦ old)
    (fun _ => ptr ↦ 42)
    (Val.nat 42)
    (fun h => Heap.write h ptr 42)
    (fun h => incrementalStG_evaluates h ptr)
    (fun h _hp =>
      (cell_pointsTo_holds ptr 42 (Heap.write h ptr 42)).2
        (by simp [Heap.read, Heap.write]))

/--
```
{ ⟨address⟩ ↦ old }
  stH(address)
{ r = 42 ∧ ⟨address⟩ ↦ 42 }
```
-/
@[zspec] theorem incrementalStH_spec (address : Nat) (old : Nat) :
    Zag.EvaluatesCall incrementalWithStGHStateCtx
      "stH" [Term.nat address]
      (HProp.toAssertion ((⟨address⟩ : Ptr) ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat 42 ∧ ((⟨address⟩ : Ptr) ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop (blocks := incrementalWithStGHBlocks)
    (hvalid := incrementalWithStGHValid) "stH" _
    ((⟨address⟩ : Ptr) ↦ old)
    (fun _ => (⟨address⟩ : Ptr) ↦ 42)
    (Val.nat 42)
    (fun h => Heap.write h ⟨address⟩ 42)
    (fun h => incrementalStH_evaluates h address)
    (fun h _hp =>
      (cell_pointsTo_holds ⟨address⟩ 42 (Heap.write h ⟨address⟩ 42)).2
        (by simp [Heap.read, Heap.write]))

def runIncrementalValue (blocks : BlockCtx.Raw heapCtx) (valid : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx)) (heap : Heap) (fuel : Nat := 4000) :
    Option (Val heapCtx) × Heap :=
  (Machine.evalFuel (mkCtx blocks valid) fuel [] (.call name args)).run heap

def runIncrementalNat (blocks : BlockCtx.Raw heapCtx) (valid : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx)) (heap : Heap) : Option Nat :=
  (runIncrementalValue blocks valid name args heap).1.bind Val.asNat?

def runIncrementalPtrState (blocks : BlockCtx.Raw heapCtx) (valid : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx)) (heap : Heap) : Option (Heap × Ptr) := do
  let (some value, final) := runIncrementalValue blocks valid name args heap | none
  let ptr ← asPtr? value
  pure (final, ptr)

def runIncrementalNatState (blocks : BlockCtx.Raw heapCtx) (valid : BlockCtx.Valid blocks)
    (name : String) (args : List (Term heapCtx)) (heap : Heap) : Option (Heap × Nat) := do
  let (some value, final) := runIncrementalValue blocks valid name args heap | none
  let result ← value.asNat?
  pure (final, result)

def incrementalOptJArgs : List (Term heapCtx) :=
  [termPtr incrementalP.addr, termPtr incrementalL.addr]

/- The selected `opt_j` semantics remain executable through ordinary context extensions. -/
theorem incremental_optJ_callable_through_extensions :
    runIncrementalNat incrementalOptJBlocks incrementalOptJValid "optJ"
        incrementalOptJArgs incrementalHeap = some 1 ∧
    runIncrementalNat incrementalWithStIBlocks incrementalWithStIValid "optJ"
        incrementalOptJArgs incrementalHeap = some 1 ∧
    runIncrementalNat incrementalWithStGHBlocks incrementalWithStGHValid "optJ"
        incrementalOptJArgs incrementalHeap = some 1 ∧
    runIncrementalNat incrementalBlocks incrementalBlocksValid "optJ"
        incrementalOptJArgs incrementalHeap = some 1 := by
  native_decide

#guard runIncrementalNat incrementalOptJBlocks incrementalOptJValid "optJ"
  [termPtr 0, termPtr incrementalL.addr] incrementalHeap = none

def incrementalStIArgs : List (Term heapCtx) := incrementalOptJArgs
def incrementalExpectedStI : Heap × Ptr :=
  (Heap.write incrementalHeap ⟨2⟩ 0, incrementalP)

/- `stI` remains callable after later extensions and performs the selected source update. -/
theorem incremental_stI_callable_through_extensions :
    runIncrementalPtrState incrementalWithStIBlocks incrementalWithStIValid "stI"
        incrementalStIArgs incrementalHeap = some incrementalExpectedStI ∧
    runIncrementalPtrState incrementalWithStGHBlocks incrementalWithStGHValid "stI"
        incrementalStIArgs incrementalHeap = some incrementalExpectedStI ∧
    runIncrementalPtrState incrementalBlocks incrementalBlocksValid "stI"
        incrementalStIArgs incrementalHeap = some incrementalExpectedStI := by
  native_decide

def incrementalRecursiveHeap : Heap :=
  { next := 7, cells := [(1, 5), (2, 0), (3, 2), (4, 5), (5, 9), (6, 0)] }

def incrementalRecursiveExpected : Heap × Ptr :=
  (Heap.write (Heap.write incrementalRecursiveHeap ⟨2⟩ 0) ⟨4⟩ 1, ⟨3⟩)

/- The combined selected-function context executes `stI`'s recursive link reconstruction. -/
#guard runIncrementalPtrState incrementalBlocks incrementalBlocksValid "stI"
  [termPtr 1, termPtr 3] incrementalRecursiveHeap =
    some incrementalRecursiveExpected

def incrementalStGArgs : List (Term heapCtx) :=
  [termPtr incrementalCell.addr]
def incrementalStHArgs : List (Term heapCtx) :=
  [Term.nat incrementalCell.addr]
def incrementalExpectedStG : Heap × Nat :=
  (Heap.write incrementalHeap incrementalCell 42, 42)

/- `stG` and its address-taking caller remain callable after extension. -/
theorem incremental_stG_stH_callable_through_extensions :
    runIncrementalNatState incrementalWithStGHBlocks incrementalWithStGHValid "stG"
        incrementalStGArgs incrementalHeap = some incrementalExpectedStG ∧
    runIncrementalNatState incrementalBlocks incrementalBlocksValid "stG"
        incrementalStGArgs incrementalHeap = some incrementalExpectedStG ∧
    runIncrementalNatState incrementalWithStGHBlocks incrementalWithStGHValid "stH"
        incrementalStHArgs incrementalHeap = some incrementalExpectedStG ∧
    runIncrementalNatState incrementalBlocks incrementalBlocksValid "stH"
        incrementalStHArgs incrementalHeap = some incrementalExpectedStG := by
  native_decide

theorem incremental_pureF_callable :
    runIncrementalNat incrementalBlocks incrementalBlocksValid "pureF" [] incrementalHeap = some 0 := by
  native_decide

end Zag.Test.Autocorres.Examples
