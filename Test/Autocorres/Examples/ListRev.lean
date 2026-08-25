import Test.Autocorres.Examples.CList

/-!
Upstream Isabelle theory:
[`ListRev.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/ListRev.thy).

Unlike `list.c`, this C node stores `next` at offset 0 and `data` at offset 1. The block below uses
that layout directly rather than calling `CList.lean`'s offset-1 executable reversal. The generic
`ValidList` relation and reversal theorem are reused only at the semantic `NextHeap` level.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev listRevBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    listRevReverse(head : Ptr) : Ptr {
      ret call listRevLoop [head, raw(termPtr 0)]
    },
    listRevLoop(current : Ptr, acc : Ptr) : Ptr {
      done := op "ptrIsNull"[current];
      ret if done { acc }
        else { call listRevStep [current, acc] }
    },
    listRevStep(current : Ptr, acc : Ptr) : Ptr {
      nextAddr := op "load"[current];
      nextPtr := op "ptrOfNat"[nextAddr];
      accAddr := op "ptrAddr"[acc];
      stored := op "store"[current, accAddr];
      ret call listRevLoop [nextPtr, current]
    }
  ]

abbrev listRevProgramBlocks : BlockCtx.Raw heapCtx :=
  listBlocks ++ listRevBlocks

theorem listRevProgramBlocksValid : BlockCtx.Valid listRevProgramBlocks := by
  valid_blocks [listRevProgramBlocks, listBlocks, listRevBlocks]

abbrev listRevCtx : Ctx := mkCtx listRevProgramBlocks listRevProgramBlocksValid

theorem listRevCtx_wellTyped : Ctx.WellTyped listRevCtx := by
  typecheck_ctx

private abbrev listRevStateCtx : Ctx :=
  heapStateCtx listRevProgramBlocks listRevProgramBlocksValid

def listRevNextField (node : Ptr) : Ptr := node

def listRevNext (heap : Heap) (node : Ptr) : Ptr :=
  ⟨Heap.read heap (listRevNextField node)⟩

def listRevFootprint (head : Ptr) (nodes : List Ptr) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  nextFieldListFootprint listRevNextField head nodes

theorem listRevNextField_injective : Function.Injective listRevNextField := by
  intro left right h
  simpa [listRevNextField] using h

theorem listRevFootprint_valid {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hp : (listRevFootprint head nodes).holds heap) :
    ValidList (listRevNext heap) head nodes := by
  change ValidList (fun node => ⟨Heap.read heap (listRevNextField node)⟩) head nodes
  exact nextFieldListFootprint_valid (nextField := listRevNextField) hp

theorem listRevFootprint_of_valid {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hvalid : ValidList (listRevNext heap) head nodes) :
    (listRevFootprint head nodes).holds heap := by
  change (nextFieldListFootprint listRevNextField head nodes).holds heap
  apply nextFieldListFootprint_of_valid (nextField := listRevNextField)
    listRevNextField_injective
  exact hvalid

def ListRevRep (heap : Heap) (head : Ptr) (nodes : List Ptr) : Prop :=
  ValidList (listRevNext heap) head nodes ∧ ValidNodeLayout heap nodes

def listRevLoopModel : Heap → List Ptr → Ptr → Heap × Ptr
| heap, [], acc => (heap, acc)
| heap, node :: nodes, acc =>
    listRevLoopModel (Heap.write heap node acc.addr) nodes node

theorem listRevLoopModel_result (heap : Heap) (nodes : List Ptr) (acc : Ptr) :
    (listRevLoopModel heap nodes acc).2 = revappendHead nodes acc := by
  induction nodes generalizing heap acc with
  | nil => rfl
  | cons node nodes ih =>
      simpa [listRevLoopModel, revappendHead] using
        ih (Heap.write heap node acc.addr) node

theorem listRevLoopModel_preserves_next (heap : Heap) (nodes : List Ptr) (acc : Ptr) :
    (listRevLoopModel heap nodes acc).1.next = heap.next := by
  induction nodes generalizing heap acc with
  | nil => rfl
  | cons node nodes ih =>
      simpa [listRevLoopModel, Heap.write] using
        (ih (Heap.write heap node acc.addr) node)

theorem listRevNext_write_self (heap : Heap) (node value : Ptr) :
    listRevNext (Heap.write heap (listRevNextField node) value.addr) node = value := by
  simp [listRevNext, listRevNextField, Heap.read, Heap.write]

theorem listRevNext_write_other (heap : Heap) (written read value : Ptr)
    (h : read ≠ written) :
    listRevNext (Heap.write heap written value.addr) read = listRevNext heap read := by
  rcases written with ⟨written⟩
  rcases read with ⟨read⟩
  have hbase : written ≠ read := by
    intro heq
    apply h
    cases heq
    rfl
  simp [listRevNext, listRevNextField, Heap.read, Heap.write, hbase]

theorem listRevNext_write (heap : Heap) (node value : Ptr) :
    listRevNext (Heap.write heap node value.addr) =
      updateNext (listRevNext heap) node value := by
  funext candidate
  by_cases h : candidate = node
  · subst candidate
    simpa [updateNext, listRevNextField] using listRevNext_write_self heap node value
  · simp [updateNext, h, listRevNext_write_other heap node candidate value h]

theorem listRev_reverse_correct {next : NextHeap} {head : Ptr} {nodes : List Ptr}
    (h : ValidList next head nodes) :
    let result := reverseLinks next nodes null
    ValidList result.1 result.2 nodes.reverse :=
  cList_reverse_correct h

theorem list_layouts_are_distinct (node : Ptr) :
    listRevNextField node = node ∧ cListNextField node = ⟨node.addr + 1⟩ := by
  simp [listRevNextField, cListNextField]

theorem listRevLoopModel_nextHeap {heap : Heap} {current acc : Ptr} {xs ys : List Ptr}
    (hcurrent : ValidList (listRevNext heap) current xs)
    (hacc : ValidList (listRevNext heap) acc ys)
    (hdisjoint : ListsDisjoint xs ys) :
    let result := listRevLoopModel heap xs acc
    ValidList (listRevNext result.1) result.2 (xs.reverse ++ ys) := by
  induction xs generalizing heap current acc ys with
  | nil => simpa [listRevLoopModel] using hacc
  | cons node nodes ih =>
      rcases hcurrent with ⟨hrep, hnodup⟩
      change current = node ∧ node ≠ null ∧
        ListRep (listRevNext heap) (listRevNext heap node) nodes at hrep
      rcases hrep with ⟨hcurrent, hnodeNonNull, htailRep⟩
      cases hcurrent
      have hnodeNodes : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      have hnodeYs : node ∉ ys := by
        intro hmem
        exact hdisjoint node (by simp) hmem
      let nextHeap := Heap.write heap node acc.addr
      have htail : ValidList (listRevNext nextHeap) (listRevNext heap node) nodes := by
        rw [listRevNext_write]
        exact ⟨(listRep_updateNext_of_not_mem hnodeNodes).2 htailRep, hnodup.tail⟩
      have hnewAcc : ValidList (listRevNext nextHeap) node (node :: ys) := by
        rw [listRevNext_write]
        constructor
        · simp [ListRep, updateNext, hnodeNonNull,
            (listRep_updateNext_of_not_mem hnodeYs).2 hacc.1]
        · exact List.nodup_cons.mpr ⟨hnodeYs, hacc.2⟩
      have hnewDisjoint : ListsDisjoint nodes (node :: ys) := by
        intro candidate hnodes hnew
        simp only [List.mem_cons] at hnew
        rcases hnew with hnew | hnew
        · exact hnodeNodes (hnew ▸ hnodes)
        · exact hdisjoint candidate (by simp [hnodes]) hnew
      simpa [listRevLoopModel, nextHeap, List.reverse_cons, List.append_assoc] using
        ih htail hnewAcc hnewDisjoint

theorem listRevReverse_model_correct {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (h : ListRevRep heap head nodes) :
    let result := listRevLoopModel heap nodes null
    ListRevRep result.1 result.2 nodes.reverse := by
  let result := listRevLoopModel heap nodes null
  have hempty : ValidList (listRevNext heap) null [] := by simp [ValidList, ListRep]
  have hvalid : ValidList (listRevNext result.1) result.2 nodes.reverse := by
    simpa [result] using listRevLoopModel_nextHeap h.1 hempty (by simp [ListsDisjoint])
  refine ⟨hvalid, ?_⟩
  rcases h.2 with ⟨hallocated, hseparated⟩
  constructor
  · intro node hmem
    have horiginal : node ∈ nodes := by simpa using hmem
    have hnode := hallocated node horiginal
    unfold NodeAllocated at hnode ⊢
    simpa [result, listRevLoopModel_preserves_next] using hnode
  · intro left hleft right hright hne
    exact hseparated left (by simpa using hleft) right (by simpa using hright) hne

theorem listRevLoop_evaluates {heap : Heap} {current acc : Ptr} {nodes : List Ptr}
    (hlist : ValidList (listRevNext heap) current nodes) :
    let model := listRevLoopModel heap nodes acc
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listRevCtx.blockCtx
      "listRevLoop" [valPtr current, valPtr acc] heap (valPtr model.2) model.1 := by
  dsimp only
  induction nodes generalizing heap current acc with
  | nil =>
      have hnull : current = null := by
        simpa [ValidList, ListRep] using hlist
      subst current
      simpa [listRevLoopModel] using (show
        EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listRevCtx.blockCtx
          "listRevLoop" [valPtr null, valPtr acc] heap (valPtr acc) heap by
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
                simp [listRevCtx, mkCtx, listRevProgramBlocks, listBlocks, listRevBlocks,
                  checkedBlocks, Machine.step, Machine.evalTerm,
                  Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
                  Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, Machine.start,
                  hptrIsNull, hite, ptrIsNullOp, Op.ite, Op.effectful,
                  Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
                  Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
                  Term.ite, termPtr, valPtr, valUnit, asPtr?]
              rfl)
  | cons node nodes ih =>
      rcases hlist with ⟨hrep, hnodup⟩
      change current = node ∧ node ≠ null ∧
        ListRep (listRevNext heap) (listRevNext heap node) nodes at hrep
      rcases hrep with ⟨hcurrent, hnodeNonNull, htailRep⟩
      subst current
      have hnodeNodes : node ∉ nodes := (List.nodup_cons.mp hnodup).1
      let nextHeap := Heap.write heap node acc.addr
      have htail : ValidList (listRevNext nextHeap) (listRevNext heap node) nodes := by
        rw [listRevNext_write]
        exact ⟨(listRep_updateNext_of_not_mem hnodeNodes).2 htailRep, hnodup.tail⟩
      have hrec := ih (heap := nextHeap) (current := listRevNext heap node)
        (acc := node) htail
      have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hite : heapOpCtx.get? "ite" = some Op.ite := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hload : heapOpCtx.get? "load" = some loadOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hstore : heapOpCtx.get? "store" = some storeOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by
        simp [OpCtx.get?, heapOpCtx, Peano.opCtx]
      have hstepCall :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx listRevCtx.blockCtx
            "listRevStep" [valPtr node, valPtr acc] heap
              (valPtr (listRevLoopModel nextHeap nodes node).2)
              (listRevLoopModel nextHeap nodes node).1 := by
        intro env base
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        repeat
          apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [listRevCtx, mkCtx, listRevProgramBlocks, listBlocks,
                listRevBlocks, checkedBlocks, Machine.step,
                Machine.evalTerm, Machine.applyValue,
                Machine.driveSelectedOp, Machine.ofOption,
                Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock,
                Machine.enterInstrs, Machine.driveOp, Machine.start,
                hload, hstore, hptrOfNat, hptrAddr, loadOp, storeOp,
                ptrOfNatOp, ptrAddrOp, Op.ite, Op.effectful, Op.Body.collect,
                Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                Op.fixed, Block.entryEnv, Scope.get?, Term.nat, Term.ite,
                termPtr, valPtr, valUnit, asPtr?]
            rfl
        apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx listRevCtx.blockCtx) _).run heap) = _
          simpa [nextHeap] using storeOp_step listRevCtx.blockCtx _ _ heap node acc.addr
        repeat
          first
          | apply EvalTriple.State.EvaluatesFrom.call_then hrec
            intro scope
            repeat
              first
              | exact EvalTriple.State.EvaluatesFrom.return_to_call
              | exact EvalTriple.State.EvaluatesFrom.done
              | apply EvalTriple.State.EvaluatesFrom.step (middle :=
                  (listRevLoopModel nextHeap nodes node).1)
                · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
                    Machine.driveOp, Op.Body.resume?]
                  rfl
          | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
            · set_option linter.unusedSimpArgs false in
                simp [listRevCtx, mkCtx, listRevProgramBlocks, listBlocks,
                  listRevBlocks, checkedBlocks, Machine.step,
                  Machine.evalTerm, Machine.applyValue,
                  Machine.driveSelectedOp, Machine.ofOption,
                  Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock,
                  Machine.enterInstrs, Machine.driveOp, Machine.start,
                  hload, hstore, hptrOfNat, hptrAddr, loadOp, storeOp,
                  ptrOfNatOp, ptrAddrOp, Op.ite, Op.effectful, Op.Body.collect,
                  Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager,
                  Op.fixed, Block.entryEnv, Scope.get?, Term.nat, Term.ite,
                  termPtr, valPtr, valUnit, asPtr?]
              rfl
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx listRevCtx.blockCtx _ heap
        (valPtr (listRevLoopModel nextHeap nodes node).2)
        (listRevLoopModel nextHeap nodes node).1 base
      repeat
        first
        | apply EvalTriple.State.EvaluatesFrom.call_then hstepCall
          intro scope
          exact EvalTriple.State.EvaluatesFrom.return_through_done_call
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [listRevCtx, mkCtx, listRevProgramBlocks, listBlocks,
                listRevBlocks, checkedBlocks, Machine.step,
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

theorem listRevReverse_evaluates {heap : Heap} {head : Ptr} {nodes : List Ptr}
    (hlist : ValidList (listRevNext heap) head nodes) :
    let model := listRevLoopModel heap nodes null
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx listRevCtx.blockCtx
      "listRevReverse" [termPtr head.addr] heap (valPtr model.2) model.1 := by
  dsimp only
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hloop := listRevLoop_evaluates (acc := null) hlist
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [listRevCtx, mkCtx, listRevProgramBlocks, listBlocks, listRevBlocks,
            checkedBlocks, Machine.step, Machine.evalTerm,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, Machine.start,
            Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
            Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
            Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

/-- Monadic packaging: SL list-shape pre/post, with the executable model hidden in the proof. -/
@[zspec] theorem listRevReverse_spec (head : Ptr) (nodes : List Ptr) :
    Zag.EvaluatesCall listRevStateCtx "listRevReverse" [termPtr head.addr]
      (HProp.toAssertion (listRevFootprint head nodes))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr (reverseHead nodes) ∧
          (listRevFootprint (reverseHead nodes) nodes.reverse).holds final⌝) :=
  evaluatesCall_of_hprop_pre "listRevReverse" _
    (listRevFootprint head nodes)
    (fun _ => listRevFootprint (reverseHead nodes) nodes.reverse)
    (valPtr (reverseHead nodes))
    (fun h => (listRevLoopModel h nodes null).1)
    (fun h hp => by
      have hvalid := listRevFootprint_valid hp
      simpa [reverseHead, listRevLoopModel_result] using
        listRevReverse_evaluates (heap := h) (head := head) (nodes := nodes) hvalid)
    (fun h hp => by
      have hvalid := listRevFootprint_valid hp
      have hempty : ValidList (listRevNext h) null [] := by simp [ValidList, ListRep]
      let model := listRevLoopModel h nodes null
      have hpost : ValidList (listRevNext model.1) (reverseHead nodes) nodes.reverse := by
        simpa [model, reverseHead, listRevLoopModel_result] using
          listRevLoopModel_nextHeap hvalid hempty (by simp [ListsDisjoint])
      simpa [model] using listRevFootprint_of_valid hpost)

theorem listRevReverse_run :
    (match (Machine.evalFuel listRevCtx 500 []
        (.call "listRevReverse" [termPtr 1])).run
          { next := 7, cells := [(1, 3), (3, 5), (5, 0)] } with
      | (some value, final) => (asPtr? value, final)
      | (none, final) => (none, final)) =
    let model := listRevLoopModel
      { next := 7, cells := [(1, 3), (3, 5), (5, 0)] } [⟨1⟩, ⟨3⟩, ⟨5⟩] null
    (some model.2, model.1) := by
  native_decide

end Zag.Test.Autocorres.Examples
