import Test.Autocorres.Examples.Common

/-!
Block analogue of upstream
[`type_strengthen_tricks.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/type_strengthen_tricks.thy).

**Unsupported correspondence boundary.** The upstream theory configures and checks AutoCorres's
effect-strengthening lattice (`pure`, read-only, option, state, exception, and nondeterminism).
Zag's current block types contain no inferred effect or failure monad: heap reads and updates use
the ambient `StateM PeanoHeap`. Thus the declarations below test only the three
honest current-model signatures and their semantics; they do not claim to test strengthening,
forced lifting, option failure, exceptions, or nondeterminism.

Public specs are monadic `EvaluatesCall` with sep-logic `↦`.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev typeStrengthenBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    pureIdentity(x : Nat) : Nat {
      ret x
    },
    readCell(ptr : Ptr) : Nat {
      ret op "load"[ptr]
    },
    write42(ptr : Ptr) : Nat {
      stored := op "store"[ptr, nat(42)];
      ret op "load"[ptr]
    }
  ]

theorem typeStrengthenBlocksValid : BlockCtx.Valid typeStrengthenBlocks := by
  valid_blocks [typeStrengthenBlocks]

abbrev typeStrengthenCtx : Ctx :=
  mkCtx typeStrengthenBlocks typeStrengthenBlocksValid

theorem typeStrengthenCtx_wellTyped : Ctx.WellTyped typeStrengthenCtx := by
  typecheck_ctx

private abbrev typeStrengthenStateCtx : Ctx :=
  heapStateCtx typeStrengthenBlocks typeStrengthenBlocksValid

theorem typeStrengthen_read_write_same (heap : Heap) (ptr : Ptr) (value : Nat) :
    Heap.read (Heap.write heap ptr value) ptr = value := by
  simp [Heap.read, Heap.write]

private theorem pureIdentity_evaluates_state (heap : Heap) (x : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) "pureIdentity"
      [Term.nat x] heap (Val.nat x) heap := by
  zvcgen [typeStrengthenBlocks]

private theorem readCell_evaluates_state (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) "readCell"
      [termPtr ptr.addr] heap (Val.nat (Heap.read heap ptr)) heap := by
  rcases ptr with ⟨ptr⟩
  have hload := load_apply_evaluates
    (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) heap ⟨ptr⟩
  set_option zvcgen.useLocalApply true in
    set_option zvcgen.resumeReturn true in
      zvcgen [typeStrengthenBlocks, checkedBlocks, loadOp, Op.effectful,
        Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?,
        termPtr, valPtr, asPtr?, Val.ty_mk, Val.as?_mk, toPtr_ofPtr,
        driveOp_apply_done, resume_dependent_apply_done, resume_load_operand]
  all_goals subst_vars
  all_goals simp_all [asPtr?, valPtr, Val.as?_mk, toPtr_ofPtr]

private theorem write42_evaluates_state (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) "write42"
      [termPtr ptr.addr] heap (Val.nat 42) (Heap.write heap ptr 42) := by
  rcases ptr with ⟨ptr⟩
  have hstore := store_apply_evaluates
    (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) heap ⟨ptr⟩ 42
  have hload := load_apply_evaluates
    (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid)
      (Heap.write heap ⟨ptr⟩ 42) ⟨ptr⟩
  set_option zvcgen.useLocalApply true in
    set_option zvcgen.resumeReturn true in
      zvcgen [typeStrengthenBlocks, checkedBlocks, loadOp, storeOp, Op.effectful,
        Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?,
        Term.nat, termPtr, valPtr, valUnit, asPtr?, Val.ty_mk, Val.ty_nat,
        Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
        resume_dependent_apply_done, resume_load_operand, resume_store_value_operand,
        typeStrengthen_read_write_same]
  all_goals subst_vars
  all_goals try simp_all [EvalTriple.Singleton.statePre, EvalTriple.Singleton.statePost,
    asPtr?, valPtr, valUnit, Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr,
    typeStrengthen_read_write_same]

/-- Pure call: unconstrained heap footprint, result `x`. -/
@[zspec] theorem pureIdentity_spec (x : Nat) :
    Zag.EvaluatesCall typeStrengthenStateCtx "pureIdentity"
      [Term.nat x]
      (fun _ => ⌜True⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜∃ h0 : Heap, True ∧ result = Val.nat x ∧ final = h0⌝) :=
  evaluatesCall_of_prop "pureIdentity" _
    (fun _ => True)
    (fun _ => Val.nat x)
    id
    (fun h _ => pureIdentity_evaluates_state h x)

/--
```
{ ptr ↦ v }
  readCell(ptr)
{ r = v ∧ ptr ↦ v }
```
-/
@[zspec] theorem readCell_spec (ptr : Ptr) (v : Nat) :
    Zag.EvaluatesCall typeStrengthenStateCtx "readCell"
      [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ v))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat v ∧ (ptr ↦ v).holds final⌝) := by
  let PreHeap := { heap : Heap // (ptr ↦ v).holds heap }
  change EvalTriple.EvaluatesFrom typeStrengthenStateCtx
    (Machine.start [] (.call "readCell" [termPtr ptr.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hread : Heap.read hh.1 ptr = v := (cell_pointsTo_holds ptr v hh.1).1 hh.2
    have hex := readCell_evaluates_state hh.1 ptr
    have hex' : EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
        (checkedBlocks typeStrengthenBlocks typeStrengthenBlocksValid) "readCell"
        [termPtr ptr.addr] hh.1 (Val.nat v) hh.1 := by
      simpa [hread] using hex
    refine EvalTriple.EvaluatesFrom.consequence hex' .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hh.2]

/--
```
{ ptr ↦ old }
  write42(ptr)
{ r = 42 ∧ ptr ↦ 42 }
```
-/
@[zspec] theorem write42_spec (ptr : Ptr) (old : Nat) :
    Zag.EvaluatesCall typeStrengthenStateCtx "write42"
      [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat 42 ∧ (ptr ↦ 42).holds final⌝) :=
  evaluatesCall_of_hprop "write42" _
    (ptr ↦ old)
    (fun _ => ptr ↦ 42)
    (Val.nat 42)
    (fun h => Heap.write h ptr 42)
    (fun h => write42_evaluates_state h ptr)
    (fun h _hp =>
      (cell_pointsTo_holds ptr 42 (Heap.write h ptr 42)).2
        (by simp [Heap.read, Heap.write]))

theorem write42_run :
    (match (Machine.evalFuel typeStrengthenCtx 30 []
        (.call "write42" [termPtr 2])).run Heap.empty with
      | (some value, final) => (value.asNat?, final)
      | (none, final) => (none, final)) =
    (some 42, Heap.write Heap.empty ⟨2⟩ 42) := by
  native_decide

end Zag.Test.Autocorres.Examples
