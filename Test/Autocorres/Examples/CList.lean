import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`CList.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/CList.thy).

The `list.c` node layout is `data` at cell offset 0 and `next` at offset 1. This differs from
`ListRev.lean`'s upstream C layout and is intentionally not shared with that executable model.
The source `sorted_insert` has a non-advancing branch and is partial; this total block IR does not
pretend that the unrelated array insertion operation models it.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev listBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    cListInsert(node : Ptr, head : Ptr) : Ptr {
      nextField := op "ptrAdd"[node, nat(1)];
      headAddr := op "ptrAddr"[head];
      stored := op "store"[nextField, headAddr];
      ret node
    },
    cListReverse(head : Ptr) : Ptr {
      ret call cListRevappend [head, raw(termPtr 0)]
    },
    cListRevappend(current : Ptr, acc : Ptr) : Ptr {
      done := op "ptrIsNull"[current];
      ret if done { acc }
        else { call cListRevappendStep [current, acc] }
    },
    cListRevappendStep(current : Ptr, acc : Ptr) : Ptr {
      nextField := op "ptrAdd"[current, nat(1)];
      nextAddr := op "load"[nextField];
      nextPtr := op "ptrOfNat"[nextAddr];
      accAddr := op "ptrAddr"[acc];
      stored := op "store"[nextField, accAddr];
      ret call cListRevappend [nextPtr, current]
    }
  ]

theorem listBlocksValid : BlockCtx.Valid listBlocks := by
  valid_blocks [listBlocks]

abbrev listCtx : Ctx := mkCtx listBlocks listBlocksValid

theorem listCtx_wellTyped : Ctx.WellTyped listCtx := by
  typecheck_ctx

private abbrev listStateCtx : Ctx := heapStateCtx listBlocks listBlocksValid

/-- The generic walker evaluates the real pure `ptrAdd` operator in the heap StateM context. -/
theorem ptrAdd_zvcgen_smoke (heap : Heap) (ptr : Ptr) (offset : Nat) :
    EvalTriple.State.EvaluatesTo heapCtx heapOpCtx listCtx.blockCtx []
      (.op "ptrAdd" [termPtr ptr.addr, Term.nat offset])
      heap (valPtr ⟨ptr.addr + offset⟩) heap := by
  have hop : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  zvcgen [hop, ptrAddOp, Op.ofVals, Op.fixed, Op.Body.eager,
    Op.Arg.ofTerms, Op.Arg.ofVals, Term.nat, termPtr, valPtr, asPtr?,
    Val.ty_mk, Val.mk_ofNat, Val.as?_mk, Val.asNat?_nat, Val.ty_nat, toPtr_ofPtr]

abbrev NextHeap := Ptr → Ptr

def updateNext (next : NextHeap) (node value : Ptr) : NextHeap :=
  fun candidate => if candidate = node then value else next candidate

def ListRep (next : NextHeap) : Ptr → List Ptr → Prop
| head, [] => head = null
| head, node :: nodes => head = node ∧ node ≠ null ∧ ListRep next (next node) nodes

def ValidList (next : NextHeap) (head : Ptr) (nodes : List Ptr) : Prop :=
  ListRep next head nodes ∧ nodes.Nodup

def ListsDisjoint (xs ys : List Ptr) : Prop :=
  ∀ node, node ∈ xs → node ∉ ys

def NodeAllocated (heap : Heap) (node : Ptr) : Prop :=
  node ≠ null ∧ node.addr + 2 ≤ heap.next

def NodeRangesDisjoint (left right : Ptr) : Prop :=
  left.addr + 2 ≤ right.addr ∨ right.addr + 2 ≤ left.addr

def ValidNodeLayout (heap : Heap) (nodes : List Ptr) : Prop :=
  (∀ node ∈ nodes, NodeAllocated heap node) ∧
    ∀ left ∈ nodes, ∀ right ∈ nodes, left ≠ right → NodeRangesDisjoint left right

def reverseLinks : NextHeap → List Ptr → Ptr → NextHeap × Ptr
| next, [], acc => (next, acc)
| next, node :: nodes, acc => reverseLinks (updateNext next node acc) nodes node

def cListNextField (node : Ptr) : Ptr :=
  ⟨node.addr + 1⟩

def cListNext (heap : Heap) (node : Ptr) : Ptr :=
  ⟨Heap.read heap (cListNextField node)⟩

def heapPure (P : Prop) : HProp Heap OwnedPtr Region (fun _ => Nat) where
  region := ⊥
  holds := fun _ => P
  supported := by intro _ _ _; exact Iff.rfl

def listHead : List Ptr → Ptr
| [] => null
| node :: _ => node

def revappendHead : List Ptr → Ptr → Ptr
| [], acc => acc
| node :: nodes, _ => revappendHead nodes node

def reverseHead (nodes : List Ptr) : Ptr :=
  revappendHead nodes null

def nextFieldListFootprint (nextField : Ptr → Ptr) :
    Ptr → List Ptr → HProp Heap OwnedPtr Region (fun _ => Nat)
| head, [] => heapPure (head = null)
| head, node :: nodes =>
    heapPure (head = node ∧ node ≠ null ∧ node ∉ nodes) ∗
      (nextField node ↦ (listHead nodes).addr) ∗
        nextFieldListFootprint nextField (listHead nodes) nodes

def cListFootprint (head : Ptr) (nodes : List Ptr) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  nextFieldListFootprint cListNextField head nodes

theorem ptr_eq_of_addr_eq {p q : Ptr} (h : p.addr = q.addr) : p = q := by
  rcases p with ⟨p⟩
  rcases q with ⟨q⟩
  simp at h ⊢
  exact h

theorem cListNextField_injective : Function.Injective cListNextField := by
  intro left right h
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  simp [cListNextField] at h ⊢
  omega

theorem listRep_head {next : NextHeap} {head : Ptr} {nodes : List Ptr}
    (h : ListRep next head nodes) : head = listHead nodes := by
  cases nodes with
  | nil => simpa [ListRep, listHead] using h
  | cons node nodes => simpa [ListRep, listHead] using h.1

theorem nextFieldListFootprint_region_mem
    {nextField : Ptr → Ptr} {head : Ptr} {nodes : List Ptr} {addr : Nat}
    (haddr : addr ∈ (nextFieldListFootprint nextField head nodes).region) :
    ∃ node, node ∈ nodes ∧ addr = (nextField node).addr := by
  induction nodes generalizing head with
  | nil =>
      simp [nextFieldListFootprint, heapPure] at haddr
  | cons node nodes ih =>
      simp [nextFieldListFootprint, heapPure, HProp.sep, pointsToVal,
        HProp.pointsTo, cell, HeapAlgebra.span,
        HeapAlgebra.Peano.OwnedPtr.span] at haddr
      rcases haddr with hcell | htail
      · refine ⟨node, by simp, ?_⟩
        omega
      · rcases ih htail with ⟨tailNode, hmem, heq⟩
        exact ⟨tailNode, by simp [hmem], heq⟩

theorem nextFieldListFootprint_disjoint_tail
    {nextField : Ptr → Ptr} (hinj : Function.Injective nextField)
    {node head : Ptr} {nodes : List Ptr} (hnot : node ∉ nodes) :
    noOverlap (nextField node ↦ (listHead nodes).addr).region
      (nextFieldListFootprint nextField head nodes).region := by
  refine Set.disjoint_left.2 ?_
  intro addr hcell htail
  have haddrCell : addr = (nextField node).addr := by
    simp [pointsToVal, HProp.pointsTo, cell, HeapAlgebra.span,
      HeapAlgebra.Peano.OwnedPtr.span] at hcell
    omega
  rcases nextFieldListFootprint_region_mem htail with ⟨tailNode, hmem, haddrTail⟩
  have hfield : nextField tailNode = nextField node := by
    apply ptr_eq_of_addr_eq
    omega
  exact hnot (by simpa [hinj hfield] using hmem)

theorem nextFieldListFootprint_valid
    {nextField : Ptr → Ptr} {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hp : (nextFieldListFootprint nextField head nodes).holds heap) :
    ValidList (fun node => ⟨Heap.read heap (nextField node)⟩) head nodes := by
  induction nodes generalizing head with
  | nil =>
      constructor
      · simpa [nextFieldListFootprint, heapPure, ListRep] using hp
      · simp
  | cons node nodes ih =>
      rcases hp with ⟨_hpureSep, hpure, hrest⟩
      rcases hrest with ⟨_hsepTail, hpoint, htail⟩
      have htailValid := ih htail
      have hread :=
        (cell_pointsTo_holds (nextField node) (listHead nodes).addr heap).1 hpoint
      have hnext : (⟨Heap.read heap (nextField node)⟩ : Ptr) = listHead nodes :=
        ptr_eq_of_addr_eq hread
      constructor
      · change head = node ∧ node ≠ null ∧
          ListRep (fun node => ⟨Heap.read heap (nextField node)⟩)
            (⟨Heap.read heap (nextField node)⟩) nodes
        exact ⟨hpure.1, hpure.2.1, by simpa [hnext] using htailValid.1⟩
      · exact List.nodup_cons.mpr ⟨hpure.2.2, htailValid.2⟩

theorem nextFieldListFootprint_of_valid
    {nextField : Ptr → Ptr} (hinj : Function.Injective nextField)
    {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hvalid : ValidList (fun node => ⟨Heap.read heap (nextField node)⟩) head nodes) :
    (nextFieldListFootprint nextField head nodes).holds heap := by
  induction nodes generalizing head with
  | nil =>
      have hhead : head = null := by
        simpa [ValidList, ListRep] using hvalid.1
      simp [nextFieldListFootprint, heapPure, hhead]
  | cons node nodes ih =>
      rcases hvalid with ⟨hrep, hnodup⟩
      change head = node ∧ node ≠ null ∧
        ListRep (fun node => ⟨Heap.read heap (nextField node)⟩)
          (⟨Heap.read heap (nextField node)⟩) nodes at hrep
      rcases hrep with ⟨hhead, hnodeNonNull, htailRep⟩
      have hnodeNodes : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have htailNodup : nodes.Nodup := (List.nodup_cons.mp hnodup).2
      have hnext : (⟨Heap.read heap (nextField node)⟩ : Ptr) = listHead nodes :=
        listRep_head htailRep
      have hread : Heap.read heap (nextField node) = (listHead nodes).addr :=
        congrArg Ptr.addr hnext
      have htailValid :
          ValidList (fun node => ⟨Heap.read heap (nextField node)⟩)
            (listHead nodes) nodes := by
        exact ⟨by simpa [hnext] using htailRep, htailNodup⟩
      refine ⟨by simp [heapPure], ⟨hhead, hnodeNonNull, hnodeNodes⟩, ?_⟩
      refine ⟨nextFieldListFootprint_disjoint_tail (nextField := nextField)
        hinj (head := listHead nodes) hnodeNodes, ?_, ih htailValid⟩
      exact (cell_pointsTo_holds (nextField node) (listHead nodes).addr heap).2 hread

theorem cListFootprint_valid {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hp : (cListFootprint head nodes).holds heap) :
    ValidList (cListNext heap) head nodes := by
  change ValidList (fun node => ⟨Heap.read heap (cListNextField node)⟩) head nodes
  exact nextFieldListFootprint_valid (nextField := cListNextField) hp

theorem cListFootprint_of_valid {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hvalid : ValidList (cListNext heap) head nodes) :
    (cListFootprint head nodes).holds heap := by
  change (nextFieldListFootprint cListNextField head nodes).holds heap
  apply nextFieldListFootprint_of_valid (nextField := cListNextField)
    cListNextField_injective
  exact hvalid

def CListRep (heap : Heap) (head : Ptr) (nodes : List Ptr) : Prop :=
  ValidList (cListNext heap) head nodes ∧ ValidNodeLayout heap nodes

def cListInsertModel (heap : Heap) (node head : Ptr) : Heap × Ptr :=
  (Heap.write heap (cListNextField node) head.addr, node)

def cListRevappendModel : Heap → List Ptr → Ptr → Heap × Ptr
| heap, [], acc => (heap, acc)
| heap, node :: nodes, acc =>
    cListRevappendModel (Heap.write heap (cListNextField node) acc.addr) nodes node

theorem cListRevappendModel_result (heap : Heap) (nodes : List Ptr) (acc : Ptr) :
    (cListRevappendModel heap nodes acc).2 = revappendHead nodes acc := by
  induction nodes generalizing heap acc with
  | nil => rfl
  | cons node nodes ih =>
      simpa [cListRevappendModel, revappendHead] using
        ih (Heap.write heap (cListNextField node) acc.addr) node

theorem cListRevappendModel_preserves_next (heap : Heap) (nodes : List Ptr) (acc : Ptr) :
    (cListRevappendModel heap nodes acc).1.next = heap.next := by
  induction nodes generalizing heap acc with
  | nil => rfl
  | cons node nodes ih =>
      simpa [cListRevappendModel, Heap.write] using
        (ih (Heap.write heap (cListNextField node) acc.addr) node)

theorem cListNext_write_self (heap : Heap) (node value : Ptr) :
    cListNext (Heap.write heap (cListNextField node) value.addr) node = value := by
  simp [cListNext, cListNextField, Heap.read, Heap.write]

theorem cListNext_write_other (heap : Heap) (written read value : Ptr)
    (h : read ≠ written) :
    cListNext (Heap.write heap (cListNextField written) value.addr) read = cListNext heap read := by
  rcases written with ⟨written⟩
  rcases read with ⟨read⟩
  have haddr : read + 1 ≠ written + 1 := by
    intro heq
    apply h
    cases Nat.add_right_cancel heq
    rfl
  have haddr' : written + 1 ≠ read + 1 := Ne.symm haddr
  have hbase : written ≠ read := by
    intro heq
    apply h
    cases heq
    rfl
  simp [cListNext, cListNextField, Heap.read, Heap.write, hbase]

theorem cListNext_write (heap : Heap) (node value : Ptr) :
    cListNext (Heap.write heap (cListNextField node) value.addr) =
      updateNext (cListNext heap) node value := by
  funext candidate
  by_cases h : candidate = node
  · subst candidate
    simp [cListNext_write_self, updateNext]
  · simp [updateNext, h, cListNext_write_other heap node candidate value h]

theorem listRep_updateNext_of_not_mem {next : NextHeap} {node value head : Ptr} {nodes : List Ptr}
    (h : node ∉ nodes) :
    ListRep (updateNext next node value) head nodes ↔ ListRep next head nodes := by
  induction nodes generalizing head with
  | nil => simp [ListRep]
  | cons current nodes ih =>
      simp only [List.mem_cons, not_or] at h
      simp [ListRep, updateNext, Ne.symm h.1, ih h.2]

theorem reverseLinks_correct {next : NextHeap} {current acc : Ptr} {xs ys : List Ptr}
    (hcurrent : ValidList next current xs) (hacc : ValidList next acc ys)
    (hdisjoint : ListsDisjoint xs ys) :
    let result := reverseLinks next xs acc
    ValidList result.1 result.2 (xs.reverse ++ ys) := by
  induction xs generalizing next current acc ys with
  | nil => simpa [reverseLinks] using hacc
  | cons node nodes ih =>
      rcases hcurrent with ⟨hrep, hnodup⟩
      change current = node ∧ node ≠ null ∧ ListRep next (next node) nodes at hrep
      have hnodeNodes : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodeYs : node ∉ ys := by
        intro hmem
        exact hdisjoint node (by simp) hmem
      have htail : ValidList (updateNext next node acc) (next node) nodes := by
        refine ⟨(listRep_updateNext_of_not_mem hnodeNodes).2 hrep.2.2, hnodup.tail⟩
      have hnewAcc : ValidList (updateNext next node acc) node (node :: ys) := by
        constructor
        · simp [ListRep, updateNext, hrep.2.1,
            (listRep_updateNext_of_not_mem hnodeYs).2 hacc.1]
        · exact List.nodup_cons.mpr ⟨hnodeYs, hacc.2⟩
      have hnewDisjoint : ListsDisjoint nodes (node :: ys) := by
        intro candidate hnodes hnew
        simp only [List.mem_cons] at hnew
        rcases hnew with hnew | hnew
        · exact hnodeNodes (hnew ▸ hnodes)
        · exact hdisjoint candidate (by simp [hnodes]) hnew
      simpa [reverseLinks, List.reverse_cons, List.append_assoc] using
        ih htail hnewAcc hnewDisjoint

theorem cList_reverse_correct {next : NextHeap} {head : Ptr} {nodes : List Ptr}
    (h : ValidList next head nodes) :
    let result := reverseLinks next nodes null
    ValidList result.1 result.2 nodes.reverse := by
  have hempty : ValidList next null [] := by simp [ValidList, ListRep]
  simpa using reverseLinks_correct h hempty (by simp [ListsDisjoint])

theorem cListRevappendModel_nextHeap {heap : Heap} {current acc : Ptr} {xs ys : List Ptr}
    (hcurrent : ValidList (cListNext heap) current xs)
    (hacc : ValidList (cListNext heap) acc ys)
    (hdisjoint : ListsDisjoint xs ys) :
    let result := cListRevappendModel heap xs acc
    ValidList (cListNext result.1) result.2 (xs.reverse ++ ys) := by
  induction xs generalizing heap current acc ys with
  | nil => simpa [cListRevappendModel] using hacc
  | cons node nodes ih =>
      rcases hcurrent with ⟨hrep, hnodup⟩
      change current = node ∧ node ≠ null ∧ ListRep (cListNext heap) (cListNext heap node) nodes at hrep
      rcases hrep with ⟨rfl, hnodeNonNull, htailRep⟩
      have hnodeNodes : current ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodeYs : current ∉ ys := by
        intro hmem
        exact hdisjoint current (by simp) hmem
      let nextHeap := Heap.write heap (cListNextField current) acc.addr
      have htail : ValidList (cListNext nextHeap) (cListNext heap current) nodes := by
        rw [cListNext_write]
        exact ⟨(listRep_updateNext_of_not_mem hnodeNodes).2 htailRep, hnodup.tail⟩
      have hnewAcc : ValidList (cListNext nextHeap) current (current :: ys) := by
        rw [cListNext_write]
        constructor
        · simp [ListRep, updateNext, hnodeNonNull,
            (listRep_updateNext_of_not_mem hnodeYs).2 hacc.1]
        · exact List.nodup_cons.mpr ⟨hnodeYs, hacc.2⟩
      have hnewDisjoint : ListsDisjoint nodes (current :: ys) := by
        intro candidate hnodes hnew
        simp only [List.mem_cons] at hnew
        rcases hnew with hnew | hnew
        · exact hnodeNodes (hnew ▸ hnodes)
        · exact hdisjoint candidate (by simp [hnodes]) hnew
      simpa [cListRevappendModel, nextHeap, List.reverse_cons, List.append_assoc] using
        ih htail hnewAcc hnewDisjoint

theorem cListReverse_model_correct {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (h : CListRep heap head nodes) :
    let result := cListRevappendModel heap nodes null
    CListRep result.1 result.2 nodes.reverse := by
  let result := cListRevappendModel heap nodes null
  have hempty : ValidList (cListNext heap) null [] := by simp [ValidList, ListRep]
  have hvalid : ValidList (cListNext result.1) result.2 nodes.reverse := by
    simpa [result] using cListRevappendModel_nextHeap h.1 hempty (by simp [ListsDisjoint])
  refine ⟨hvalid, ?_⟩
  rcases h.2 with ⟨hallocated, hseparated⟩
  constructor
  · intro node hmem
    have horiginal : node ∈ nodes := by simpa using hmem
    have hnode := hallocated node horiginal
    unfold NodeAllocated at hnode ⊢
    simpa [result, cListRevappendModel_preserves_next] using hnode
  · intro left hleft right hright hne
    exact hseparated left (by simpa using hleft) right (by simpa using hright) hne

theorem cListInsert_evaluates (heap : Heap) (node head : Ptr) :
    let model := cListInsertModel heap node head
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx listCtx.blockCtx
      "cListInsert" [termPtr node.addr, termPtr head.addr]
      heap (valPtr model.2) model.1 := by
  dsimp only
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hstore : heapOpCtx.get? "store" = some storeOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by
    simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
  repeat
    apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
    · set_option linter.unusedSimpArgs false in
        simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
          Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
          Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
          Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
          Machine.driveOp, Machine.start, hstore, hptrAdd, hptrAddr,
          storeOp, ptrAddOp, ptrAddrOp, Op.effectful, Op.Body.collect,
          Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
          Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
      rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle :=
    (cListInsertModel heap node head).1)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx listCtx.blockCtx) _).run heap) = _
    simpa [cListInsertModel, cListNextField] using
      storeOp_step listCtx.blockCtx _ _ heap (cListNextField node) head.addr
  repeat
    first
    | exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle :=
        (cListInsertModel heap node head).1)
      · set_option linter.unusedSimpArgs false in
          simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
            Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, hstore, hptrAdd, hptrAddr,
            storeOp, ptrAddOp, ptrAddrOp, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

theorem cListRevappend_evaluates {heap : Heap} {current acc : Ptr} {nodes : List Ptr}
    (hlist : ValidList (cListNext heap) current nodes) :
    let model := cListRevappendModel heap nodes acc
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listCtx.blockCtx
      "cListRevappend" [valPtr current, valPtr acc] heap (valPtr model.2) model.1 := by
  dsimp only
  induction nodes generalizing heap current acc with
  | nil =>
      have hnull : current = null := by
        simpa [ValidList, ListRep] using hlist
      subst current
      simpa [cListRevappendModel] using (show
        EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listCtx.blockCtx
          "cListRevappend" [valPtr null, valPtr acc] heap (valPtr acc) heap by
        have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        have hite : heapOpCtx.get? "ite" = some Op.ite := by
          simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
        intro env base
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          first
          | exact EvalTriple.State.EvaluatesFrom.done
          | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
            · set_option linter.unusedSimpArgs false in
                simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
                  Machine.evalTerm, Machine.driveSelectedOp,
                  Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, Machine.start,
                  hptrIsNull, hite, ptrIsNullOp, Op.ite, Op.effectful,
                  Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                  Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                  Term.ite, termPtr, valPtr, valUnit, asPtr?]
              rfl)
  | cons node nodes ih =>
      rcases hlist with ⟨hrep, hnodup⟩
      change current = node ∧ node ≠ null ∧
        ListRep (cListNext heap) (cListNext heap node) nodes at hrep
      rcases hrep with ⟨hcurrent, hnodeNonNull, htailRep⟩
      subst current
      have hnodeNodes : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      let nextHeap := Heap.write heap (cListNextField node) acc.addr
      have htail : ValidList (cListNext nextHeap) (cListNext heap node) nodes := by
        rw [cListNext_write]
        exact ⟨(listRep_updateNext_of_not_mem hnodeNodes).2 htailRep, hnodup.tail⟩
      have hrec := ih (heap := nextHeap) (current := cListNext heap node)
        (acc := node) htail
      have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hite : heapOpCtx.get? "ite" = some Op.ite := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
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
      have hstepCall :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listCtx.blockCtx
            "cListRevappendStep" [valPtr node, valPtr acc] heap
              (valPtr (cListRevappendModel nextHeap nodes node).2)
              (cListRevappendModel nextHeap nodes node).1 := by
        intro env base
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · first
            | change Id.run ((Machine.step
                (Machine.stateCtx heapCtx heapOpCtx listCtx.blockCtx) _).run heap) = _
              simpa [cListNextField] using loadOp_step listCtx.blockCtx _ _ heap
                (cListNextField node)
            | set_option linter.unusedSimpArgs false in
                simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
                  Machine.evalTerm, Machine.applyValue,
                  Machine.driveSelectedOp, Machine.ofOption,
                  Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, Machine.start,
                  hload, hstore, hptrAdd, hptrOfNat, hptrAddr, loadOp, storeOp,
                  ptrAddOp, ptrOfNatOp, ptrAddrOp, Op.ite, Op.effectful,
                  Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                  Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                  Term.ite, termPtr, valPtr, valUnit, asPtr?]
              rfl
        apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx listCtx.blockCtx) _).run heap) = _
          simpa [nextHeap, cListNextField] using storeOp_step listCtx.blockCtx _ _ heap
            (cListNextField node) acc.addr
        repeat
          first
          | apply EvalTriple.State.EvaluatesFrom.call_then hrec
            intro scope
            repeat
              first
              | exact EvalTriple.State.EvaluatesFrom.return_to_call
              | exact EvalTriple.State.EvaluatesFrom.done
              | apply EvalTriple.State.EvaluatesFrom.step (middle :=
                  (cListRevappendModel nextHeap nodes node).1)
                · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                    Machine.driveOp, Op.Body.resume?]
                  rfl
          | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
            · set_option linter.unusedSimpArgs false in
                simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
                  Machine.evalTerm, Machine.applyValue,
                  Machine.driveSelectedOp, Machine.ofOption,
                  Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, Machine.start,
                  hload, hstore, hptrAdd, hptrOfNat, hptrAddr, loadOp, storeOp,
                  ptrAddOp, ptrOfNatOp, ptrAddrOp, Op.ite, Op.effectful,
                  Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                  Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                  Term.ite, termPtr, valPtr, valUnit, asPtr?]
              rfl
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx listCtx.blockCtx _ heap
        (valPtr (cListRevappendModel nextHeap nodes node).2)
        (cListRevappendModel nextHeap nodes node).1 base
      repeat
        first
        | apply EvalTriple.State.EvaluatesFrom.call_then hstepCall
          intro scope
          exact EvalTriple.State.EvaluatesFrom.return_through_done_call
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
                Machine.evalTerm, Machine.applyValue,
                Machine.driveSelectedOp, Machine.ofOption,
                Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock,
                Machine.enterInstrs, Machine.driveOp, Machine.start,
                hptrIsNull, hite, hnodeNonNull, ptrIsNullOp, Op.ite,
                Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
                Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
                Term.nat, Term.ite, termPtr, valPtr, valUnit, asPtr?]
            rfl

theorem cListReverse_evaluates {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hlist : ValidList (cListNext heap) head nodes) :
    let model := cListRevappendModel heap nodes null
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx listCtx.blockCtx
      "cListReverse" [termPtr head.addr] heap (valPtr model.2) model.1 := by
  dsimp only
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hloop := cListRevappend_evaluates (acc := null) hlist
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [listCtx, mkCtx, listBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate, Machine.resumeFrame,
            Machine.enterBlock, Machine.enterInstrs, Machine.driveOp,
            Machine.start, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

/--
```
{ node+1 ↦ old }
  cListInsert(node, head)
{ r = node ∧ node+1 ↦ head.addr }
```
-/
@[zspec] theorem cListInsert_spec (node head : Ptr) (old : Nat) :
    Zag.EvaluatesCall listStateCtx "cListInsert"
      [termPtr node.addr, termPtr head.addr]
      (HProp.toAssertion (cListNextField node ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr node ∧ (cListNextField node ↦ head.addr).holds final⌝) :=
  evaluatesCall_of_hprop "cListInsert" _
    (cListNextField node ↦ old)
    (fun _ => cListNextField node ↦ head.addr)
    (valPtr node)
    (fun h => Heap.write h (cListNextField node) head.addr)
    (fun h => by simpa [cListInsertModel] using cListInsert_evaluates h node head)
    (fun h _hp =>
      (cell_pointsTo_holds (cListNextField node) head.addr
        (Heap.write h (cListNextField node) head.addr)).2
        (by simp [Heap.read, Heap.write]))

/-- Monadic packaging: SL list-shape pre/post, with the executable model hidden in the proof. -/
@[zspec] theorem cListReverse_spec (head : Ptr) (nodes : List Ptr) :
    Zag.EvaluatesCall listStateCtx "cListReverse" [termPtr head.addr]
      (HProp.toAssertion (cListFootprint head nodes))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr (reverseHead nodes) ∧
          (cListFootprint (reverseHead nodes) nodes.reverse).holds final⌝) :=
  evaluatesCall_of_hprop_pre "cListReverse" _
    (cListFootprint head nodes)
    (fun _ => cListFootprint (reverseHead nodes) nodes.reverse)
    (valPtr (reverseHead nodes))
    (fun h => (cListRevappendModel h nodes null).1)
    (fun h hp => by
      have hvalid := cListFootprint_valid hp
      simpa [reverseHead, cListRevappendModel_result] using
        cListReverse_evaluates (heap := h) (head := head) (nodes := nodes) hvalid)
    (fun h hp => by
      have hvalid := cListFootprint_valid hp
      have hempty : ValidList (cListNext h) null [] := by simp [ValidList, ListRep]
      let model := cListRevappendModel h nodes null
      have hpost : ValidList (cListNext model.1) (reverseHead nodes) nodes.reverse := by
        simpa [model, reverseHead, cListRevappendModel_result] using
          cListRevappendModel_nextHeap hvalid hempty (by simp [ListsDisjoint])
      simpa [model] using cListFootprint_of_valid hpost)

theorem cListReverse_run :
    (match (Machine.evalFuel listCtx 500 []
        (.call "cListReverse" [termPtr 1])).run
          { next := 7, cells := [(2, 3), (4, 5), (6, 0)] } with
      | (some value, final) => (asPtr? value, final)
      | (none, final) => (none, final)) =
    let model := cListRevappendModel
      { next := 7, cells := [(2, 3), (4, 5), (6, 0)] } [⟨1⟩, ⟨3⟩, ⟨5⟩] null
    (some model.2, model.1) := by
  native_decide

end Zag.Test.Autocorres.Examples
