import Test.Autocorres.Examples.Common

/-!
Current-model analogue of upstream
[`AC_Rename.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/AC_Rename.thy).

Public specs are monadic `EvaluatesCall` with sep-logic `↦`.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

def renameFunctionPrefix : String := "ac_"

def renameGetSourceName : String := "__get_real_var__"

def renameSetSourceName : String := "__set_real_var__"

def renameTargetName (source : String) : String := renameFunctionPrefix ++ source

abbrev renameBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    «ac___get_real_var__»(ptr : Ptr) : Nat {
      ret op "load"[ptr]
    },
    «ac___set_real_var__»(ptr : Ptr, value : Nat) : Unit {
      ret op "store"[ptr, value]
    }
  ]

theorem renameBlocksValid : BlockCtx.Valid renameBlocks := by
  valid_blocks [renameBlocks]

abbrev renameCtx : Ctx := mkCtx renameBlocks renameBlocksValid

theorem renameCtx_wellTyped : Ctx.WellTyped renameCtx := by
  typecheck_ctx

private abbrev renameStateCtx : Ctx := heapStateCtx renameBlocks renameBlocksValid

/-- Prefix normalization computes the exact local target names. -/
theorem renameTargetNames :
    renameTargetName renameGetSourceName = "ac___get_real_var__" ∧
    renameTargetName renameSetSourceName = "ac___set_real_var__" := by
  constructor <;> rfl

/-- The normalized target names retrieve the corresponding installed definitions. -/
theorem renameCtx_prefixedNames :
    renameCtx.blockCtx.get? (renameTargetName renameGetSourceName) = some renameBlocks[0].2 ∧
    renameCtx.blockCtx.get? (renameTargetName renameSetSourceName) = some renameBlocks[1].2 := by
  constructor <;> rfl

/-- Source-level names are not silently retained as aliases. -/
theorem renameCtx_unprefixedNamesAbsent :
    renameCtx.blockCtx.get? renameGetSourceName = none ∧
    renameCtx.blockCtx.get? renameSetSourceName = none := by
  constructor <;> rfl

private theorem renameGet_evaluates_state (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks renameBlocks renameBlocksValid) "ac___get_real_var__"
      [termPtr ptr.addr] heap (Val.nat (Heap.read heap ptr)) heap := by
  rcases ptr with ⟨ptr⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [renameBlocks, checkedBlocks, loadOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, termPtr,
      valPtr, asPtr?, Op.ofVals, Op.Body.eager, Op.fixed, Val.ty_mk,
      Val.mk_ofNat, Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, resume_load_operand]
  all_goals zvcgen [loadValAction_spec, loadOp_action_spec, loadOp_action_valPtr]
  all_goals subst_vars
  all_goals simp_all [asPtr?, valPtr, Val.as?_mk, toPtr_ofPtr]

private theorem renameSet_evaluates_state (heap : Heap) (ptr : Ptr) (value : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks renameBlocks renameBlocksValid) "ac___set_real_var__"
      [termPtr ptr.addr, .nat value] heap valUnit (Heap.write heap ptr value) := by
  rcases ptr with ⟨ptr⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [renameBlocks, checkedBlocks, storeOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
      termPtr, valPtr, valUnit, asPtr?, Op.ofVals, Op.Body.eager, Op.fixed,
      Val.ty_mk, Val.ty_nat, Val.mk_ofNat, Val.as?_mk, Val.asNat?_nat,
      toPtr_ofPtr, driveOp_apply_done, resume_dependent_apply_done,
      resume_store_value_operand]
  all_goals zvcgen [storeValAction_spec, storeOp_action_spec, storeOp_action_vals]
  all_goals try simp_all [asPtr?, valPtr, valUnit, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]
  all_goals try solve_by_elim
  all_goals obtain ⟨hleft, hright⟩ := ‹_ ∧ _›
  all_goals subst_vars
  all_goals simp_all [asPtr?, valPtr, valUnit, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]

/--
```
{ ptr ↦ v }
  ac___get_real_var__(ptr)
{ r = v ∧ ptr ↦ v }
```
-/
@[zspec] theorem renameGet_eval (ptr : Ptr) (v : Nat) :
    Zag.EvaluatesCall renameStateCtx "ac___get_real_var__"
      [termPtr ptr.addr]
      (HProp.toAssertion (ptr ↦ v))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = Val.nat v ∧ (ptr ↦ v).holds final⌝) := by
  let PreHeap := { heap : Heap // (ptr ↦ v).holds heap }
  change EvalTriple.EvaluatesFrom renameStateCtx
    (Machine.start [] (.call "ac___get_real_var__" [termPtr ptr.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hread : Heap.read hh.1 ptr = v := (cell_pointsTo_holds ptr v hh.1).1 hh.2
    have hex := renameGet_evaluates_state hh.1 ptr
    have hex' : EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
        (checkedBlocks renameBlocks renameBlocksValid) "ac___get_real_var__"
        [termPtr ptr.addr] hh.1 (Val.nat v) hh.1 := by
      simpa [hread] using hex
    refine EvalTriple.EvaluatesFrom.consequence hex' .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hh.2]

/--
```
{ ptr ↦ old }
  ac___set_real_var__(ptr, value)
{ ptr ↦ value }
```
-/
@[zspec] theorem renameSet_eval (ptr : Ptr) (old value : Nat) :
    Zag.EvaluatesCall renameStateCtx "ac___set_real_var__"
      [termPtr ptr.addr, .nat value]
      (HProp.toAssertion (ptr ↦ old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ (ptr ↦ value).holds final⌝) :=
  evaluatesCall_of_hprop "ac___set_real_var__" _
    (ptr ↦ old)
    (fun _ => ptr ↦ value)
    valUnit
    (fun h => Heap.write h ptr value)
    (fun h => renameSet_evaluates_state h ptr value)
    (fun h _hp =>
      (cell_pointsTo_holds ptr value (Heap.write h ptr value)).2
        (by simp [Heap.read, Heap.write]))

theorem rename_set_run :
    (match (Machine.evalFuel renameCtx 20 []
        (.call "ac___set_real_var__" [termPtr 2, .nat 17])).run Heap.empty with
      | (some _, final) => some final
      | (none, _) => none) =
    some (Heap.write Heap.empty ⟨2⟩ 17) := by
  native_decide

end Zag.Test.Autocorres.Examples
