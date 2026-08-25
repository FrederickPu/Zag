import Lib.PeanoHeap
import HeapAlgebra.Peano
import Meta.Eval.Induction
import Meta.Eval.VC
import Meta.Induction
import Meta.UnifyType

/-!
Prelude for the AutoCorres example analogues.

Each module below mirrors one upstream `tools/autocorres/tests/examples/*.thy` theory with a
small block-IR program over `PeanoHeap` and a checked typing context. Everything they use is
general purpose and lives outside `Test/`: `mkCtx` and `valid_blocks` in `Lib/PeanoHeap.lean`,
    the relational evaluator tactics in `Meta/Eval/VC.lean`, `typecheck_ctx` in
`Meta/UnifyType.lean`, and the reflected induction rule in `Meta/Induction.lean`. Examples that
need specialized Peano loop automation import `Meta/Peano/Eval.lean` directly.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra.Peano (OwnedPtr Region)
open scoped Std.Do

/-! ### Shared sep-logic surface for heap Autocorres examples -/

section SepLogic
open HeapAlgebra
open HProp
open scoped HProp

/-- 1-cell owned pointer for HeapAlgebra `↦`. -/
def cell (p : Ptr) : OwnedPtr :=
  ⟨p, 1, Nat.one_pos⟩

/-- One-cell points-to: `p ↦ v`. -/
abbrev pointsToVal (p : Ptr) (v : Nat) : HProp Heap OwnedPtr Region (fun _ => Nat) :=
  HProp.pointsTo (Value := fun _ : OwnedPtr => Nat) (cell p) v

scoped infix:55 " ↦ " => pointsToVal

theorem cell_pointsTo_holds (p : Ptr) (v : Nat) (h : Heap) :
    (p ↦ v).holds h ↔ Heap.read h p = v := by
  simp [pointsToVal, HProp.pointsTo, cell, HeapAlgebra.load]

def range (base len : Nat) : Region :=
  Set.Ico base (base + len)

def segment (base len : Nat) (contents : Nat → Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) where
  region := range base len
  holds h := ∀ i, i < len → Heap.read h ⟨base + i⟩ = contents i
  supported := by
    intro h h' hd
    constructor
    · intro hh i hi
      have hmem : base + i ∈ range base len := by simp [range, Set.mem_Ico]; omega
      have : Heap.read h ⟨base + i⟩ = Heap.read h' ⟨base + i⟩ := by
        by_contra hneq; exact Set.disjoint_right.mp hd hmem hneq
      exact this ▸ hh i hi
    · intro hh i hi
      have hmem : base + i ∈ range base len := by simp [range, Set.mem_Ico]; omega
      have : Heap.read h ⟨base + i⟩ = Heap.read h' ⟨base + i⟩ := by
        by_contra hneq; exact Set.disjoint_right.mp hd hmem hneq
      exact this ▸ hh i hi

/-- State-ctx view of a heap `mkCtx` program. -/
abbrev heapStateCtx (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) : Ctx :=
  Machine.stateCtx heapCtx heapOpCtx (checkedBlocks blocks h)

/-- Lift ∀-heap exact call specs to monadic SL `EvaluatesCall` with `HProp` pre/post. -/
theorem evaluatesCall_of_hprop
    {blocks : BlockCtx.Raw heapCtx} {hvalid : BlockCtx.Valid blocks}
    (name : String) (args : List (Term heapCtx))
    (P : HProp Heap OwnedPtr Region (fun _ => Nat))
    (Q : Val heapCtx → HProp Heap OwnedPtr Region (fun _ => Nat))
    (retVal : Val heapCtx) (f : Heap → Heap)
    (hexact : ∀ heap,
      EvalTriple.State.EvaluatesCall heapCtx heapOpCtx (checkedBlocks blocks hvalid)
        name args heap retVal (f heap))
    (hpost : ∀ heap, P.holds heap → (Q retVal).holds (f heap)) :
    Zag.EvaluatesCall (heapStateCtx blocks hvalid) name args
      (HProp.toAssertion P)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = retVal ∧ (Q result).holds final⌝) := by
  let PreHeap := { heap : Heap // P.holds heap }
  change EvalTriple.EvaluatesFrom (heapStateCtx blocks hvalid)
    (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hpost hh.1 hh.2]

/-- Lift precondition-dependent exact call specs to monadic SL `EvaluatesCall`. -/
theorem evaluatesCall_of_hprop_pre
    {blocks : BlockCtx.Raw heapCtx} {hvalid : BlockCtx.Valid blocks}
    (name : String) (args : List (Term heapCtx))
    (P : HProp Heap OwnedPtr Region (fun _ => Nat))
    (Q : Val heapCtx → HProp Heap OwnedPtr Region (fun _ => Nat))
    (retVal : Val heapCtx) (f : Heap → Heap)
    (hexact : ∀ heap, P.holds heap →
      EvalTriple.State.EvaluatesCall heapCtx heapOpCtx (checkedBlocks blocks hvalid)
        name args heap retVal (f heap))
    (hpost : ∀ heap, P.holds heap → (Q retVal).holds (f heap)) :
    Zag.EvaluatesCall (heapStateCtx blocks hvalid) name args
      (HProp.toAssertion P)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = retVal ∧ (Q result).holds final⌝) := by
  let PreHeap := { heap : Heap // P.holds heap }
  change EvalTriple.EvaluatesFrom (heapStateCtx blocks hvalid)
    (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1 hh.2
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hpost hh.1 hh.2]

/-- Like `evaluatesCall_of_hprop` but for an arbitrary `opCtx`. -/
theorem evaluatesCall_of_hprop_op
    {opCtx : OpCtx heapCtx (StateM Heap)}
    {blocks : BlockCtx.Raw heapCtx} {hvalid : BlockCtx.Valid blocks}
    (name : String) (args : List (Term heapCtx))
    (P : HProp Heap OwnedPtr Region (fun _ => Nat))
    (Q : Val heapCtx → HProp Heap OwnedPtr Region (fun _ => Nat))
    (retVal : Val heapCtx) (f : Heap → Heap)
    (hexact : ∀ heap,
      EvalTriple.State.EvaluatesCall heapCtx opCtx (checkedBlocks blocks hvalid)
        name args heap retVal (f heap))
    (hpost : ∀ heap, P.holds heap → (Q retVal).holds (f heap)) :
    Zag.EvaluatesCall (Machine.stateCtx heapCtx opCtx (checkedBlocks blocks hvalid)) name args
      (HProp.toAssertion P)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = retVal ∧ (Q result).holds final⌝) := by
  let PreHeap := { heap : Heap // P.holds heap }
  let stateCtx := Machine.stateCtx heapCtx opCtx (checkedBlocks blocks hvalid)
  change EvalTriple.EvaluatesFrom stateCtx
    (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hpost hh.1 hh.2]

/-- Lift exact-state specs under a monadic pure precondition `⌜P h⌝` (model packaging). -/
theorem evaluatesCall_of_prop
    {blocks : BlockCtx.Raw heapCtx} {hvalid : BlockCtx.Valid blocks}
    (name : String) (args : List (Term heapCtx))
    (P : Heap → Prop)
    (retVal : Heap → Val heapCtx)
    (f : Heap → Heap)
    (hexact : ∀ heap, P heap →
      EvalTriple.State.EvaluatesCall heapCtx heapOpCtx (checkedBlocks blocks hvalid)
        name args heap (retVal heap) (f heap)) :
    Zag.EvaluatesCall (heapStateCtx blocks hvalid) name args
      (fun h => ⌜P h⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜∃ h0 : Heap, P h0 ∧ result = retVal h0 ∧ final = f h0⌝) := by
  let PreHeap := { heap : Heap // P heap }
  change EvalTriple.EvaluatesFrom (heapStateCtx blocks hvalid)
    (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1 hh.2
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    exact ⟨hh.1, hh.2, rfl, rfl⟩

/-- Like `evaluatesCall_of_prop` with an extra relational postcondition on `(h0, result, final)`. -/
theorem evaluatesCall_of_prop_post
    {blocks : BlockCtx.Raw heapCtx} {hvalid : BlockCtx.Valid blocks}
    (name : String) (args : List (Term heapCtx))
    (P : Heap → Prop)
    (retVal : Heap → Val heapCtx)
    (f : Heap → Heap)
    (R : Heap → Val heapCtx → Heap → Prop)
    (hexact : ∀ heap, P heap →
      EvalTriple.State.EvaluatesCall heapCtx heapOpCtx (checkedBlocks blocks hvalid)
        name args heap (retVal heap) (f heap))
    (hpost : ∀ heap, P heap → R heap (retVal heap) (f heap)) :
    Zag.EvaluatesCall (heapStateCtx blocks hvalid) name args
      (fun h => ⌜P h⌝)
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜∃ h0 : Heap, P h0 ∧ result = retVal h0 ∧ final = f h0 ∧ R h0 result final⌝) := by
  let PreHeap := { heap : Heap // P heap }
  change EvalTriple.EvaluatesFrom (heapStateCtx blocks hvalid)
    (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1 hh.2
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails]
    exact ⟨hh.1, hh.2, rfl, rfl, hpost hh.1 hh.2⟩

end SepLogic

/-- Normalize the continuation installed after an effectful operator returns its value. -/
theorem driveOp_apply_done (fn : Val primCtx) (args : List (Val primCtx))
    (rest : List (Op.Arg primCtx)) (env : Env primCtx) (stack : List (Frame primCtx)) :
    Machine.driveOp (.apply fn args .done) rest env stack =
      some ⟨.apply fn args, env,
        .opBody (fun | some value => .done value | none => .fail) rest env :: stack⟩ := by
  simp [Machine.driveOp]
  funext value
  cases value <;> rfl

/-- Resume a final, type-dependent operand into an effectful operator application. -/
theorem resume_dependent_apply_done (ctx : Ctx) (select : Val ctx.primCtx → Option Ty)
    (fn : Val ctx.primCtx → Ty → Val ctx.primCtx)
    (args : Val ctx.primCtx → List (Val ctx.primCtx)) (value : Val ctx.primCtx)
    (outTy : Ty) (env : Env ctx.primCtx) (stack : List (Frame ctx.primCtx))
    (hout : select value = some outTy) :
    Machine.resumeFrame ctx
        (.opBody (fun
          | some actual =>
              match select actual with
              | some actualOutTy => .apply (fn actual actualOutTy) (args actual) .done
              | none => .fail
          | none => .fail) [] env)
        value stack =
      some ⟨.apply (fn value outTy) (args value), env,
        .opBody (fun | some result => .done result | none => .fail) [] env :: stack⟩ := by
  simp [Machine.resumeFrame, hout, driveOp_apply_done]
  funext result
  cases result <;> rfl

theorem resume_load_operand (opCtx : OpCtx heapCtx (StateM σ))
    (blockCtx : BlockCtx heapCtx) (env : Env heapCtx)
    (stack : List (Frame heapCtx)) (ptr : Ptr) :
    Machine.resumeFrame (Machine.stateCtx heapCtx opCtx blockCtx)
        (.opBody (fun
          | some value =>
              match if value.ty = PtrTy then some NatTy else none with
              | some outTy => .apply (.opRef "load" [] [value.ty] outTy) [value] .done
              | none => .fail
          | none => .fail) [] env)
        (valPtr ptr) stack =
      some ⟨.apply (.opRef "load" [] [PtrTy] NatTy) [valPtr ptr], env,
        .opBody (fun | some result => .done result | none => .fail) [] env :: stack⟩ := by
  simp [Machine.resumeFrame, valPtr, driveOp_apply_done]
  funext result
  cases result <;> rfl

theorem resume_store_value_operand (opCtx : OpCtx heapCtx (StateM σ))
    (blockCtx : BlockCtx heapCtx) (env : Env heapCtx)
    (stack : List (Frame heapCtx)) (ptr : Ptr) (value : Nat) :
    Machine.resumeFrame (Machine.stateCtx heapCtx opCtx blockCtx)
        (.opBody (fun
          | some actual =>
              match if actual.ty = NatTy then some UnitTy else none with
              | some outTy =>
                  .apply (.opRef "store" [] [PtrTy, actual.ty] outTy)
                    [valPtr ptr, actual] .done
              | none => .fail
          | none => .fail) [] env)
        (Val.nat value) stack =
      some ⟨.apply (.opRef "store" [] [PtrTy, NatTy] UnitTy)
          [valPtr ptr, Val.nat value], env,
        .opBody (fun | some result => .done result | none => .fail) [] env :: stack⟩ := by
  simp [Machine.resumeFrame, valPtr, driveOp_apply_done]
  funext result
  cases result <;> rfl

/-- Continue a generic derivation after a returned value resumes its pending frame. -/
theorem steps_resume_return {ctx : Ctx} {E : EvalTriple.ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → EvalTriple.Assertion ctx → Prop}
    {value : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {frame : Frame ctx.primCtx} {stack : List (Frame ctx.primCtx)}
    {next : Machine.Config ctx.primCtx} {P : EvalTriple.Assertion ctx}
    (hresume : Machine.resumeFrame ctx frame value stack = some next)
    (tail : EvalTriple.Steps ctx E Done next P) :
    EvalTriple.Steps ctx E Done ⟨.ret value, scope, frame :: stack⟩ P :=
  EvalTriple.Steps.resumeReturn hresume tail

theorem steps_subst_return {ctx : Ctx} {E : EvalTriple.ExceptConds ctx}
    {Done : Machine.Config ctx.primCtx → EvalTriple.Assertion ctx → Prop}
    {value expected : Val ctx.primCtx} {scope : Env ctx.primCtx}
    {stack : List (Frame ctx.primCtx)} {P : EvalTriple.Assertion ctx}
    (heq : P ⊢ₛ spred(⌜(⟨.ret value, scope, stack⟩ : Machine.Config ctx.primCtx) =
      ⟨.ret expected, scope, stack⟩⌝))
    (tail : EvalTriple.Steps ctx E Done ⟨.ret expected, scope, stack⟩ P) :
    EvalTriple.Steps ctx E Done ⟨.ret value, scope, stack⟩ P := by
  exact EvalTriple.Steps.subst heq .rfl tail

@[zspec] theorem loadValAction_spec (ptr : Ptr)
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple
      (do
        let value ← load ptr
        pure (some (Val.nat value)))
      (fun heap => Q.1 (some (Val.nat (Heap.read heap ptr))) heap) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, load, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem storeValAction_spec (ptr : Ptr) (value : Nat)
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple
      (do
        let _ ← store ptr value
        pure (some valUnit))
      (fun heap => Q.1 (some valUnit) (Heap.write heap ptr value)) Q := by
  simp only [Std.Do.Triple.iff, Std.Do.wp, store, MonadState.modifyGet,
    MonadStateOf.modifyGet, StateT.run, Id.run]
  exact fun _ h => h

@[zspec] theorem loadOp_action_spec (ptr : Ptr)
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple ((loadOp.action "load" [valPtr ptr]).get (by simp [loadOp, Op.effectful]))
      (fun heap => Q.1 (some (Val.nat (Heap.read heap ptr))) heap) Q := by
  simpa [loadOp, Op.effectful, valPtr, asPtr?, Val.as?_mk, toPtr_ofPtr] using
    loadValAction_spec ptr Q

@[zspec] theorem storeOp_action_spec (ptr : Ptr) (value : Nat)
    (Q : Std.Do.PostCond (Option (Val heapCtx)) (.arg Heap .pure)) :
    Std.Do.Triple
      ((storeOp.action "store" [valPtr ptr, Val.nat value]).get
        (by simp [storeOp, Op.effectful]))
      (fun heap => Q.1 (some valUnit) (Heap.write heap ptr value)) Q := by
  simpa [storeOp, Op.effectful, valPtr, valUnit, asPtr?, Val.as?_mk,
    Val.asNat?_nat, toPtr_ofPtr] using storeValAction_spec ptr value Q

theorem loadOp_action_valPtr (ptr : Ptr) :
    loadOp.action "load" [valPtr ptr] = some (do
      let value ← load ptr
      pure (some (Val.nat value))) := by
  simp [loadOp, Op.effectful, valPtr, asPtr?, Val.as?_mk, toPtr_ofPtr]

theorem storeOp_action_vals (ptr : Ptr) (value : Nat) :
    storeOp.action "store" [valPtr ptr, Val.nat value] = some (do
      let _ ← store ptr value
      pure (some valUnit)) := by
  simp [storeOp, Op.effectful, valPtr, valUnit, asPtr?, Val.as?_mk,
    Val.asNat?_nat, toPtr_ofPtr]

theorem allocPtrOp_action_val (size : Nat) :
    allocPtrOp.action "allocPtr" [Val.nat size] = some (do
      let ptr ← alloc size
      pure (some (valPtr ptr))) := by
  simp [allocPtrOp, Op.effectful, Val.asNat?_nat]

theorem memcpyOp_action_vals (dst src : Ptr) (len : Nat) :
    memcpyOp.action "memcpy" [valPtr dst, valPtr src, Val.nat len] =
      some (fun heap => (some (valPtr dst), Heap.copy heap dst src len)) := by
  simp [memcpyOp, Op.effectful, valPtr, asPtr?, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]
  congr 1

theorem memsetOp_action_vals (start : Ptr) (value len : Nat) :
    memsetOp.action "memset" [valPtr start, Val.nat value, Val.nat len] =
      some (fun heap =>
        (some (valPtr start), Heap.fill heap start (value % 256) len)) := by
  simp [memsetOp, Op.effectful, valPtr, asPtr?, Val.as?_mk, Val.asNat?_nat,
    toPtr_ofPtr]
  congr 1

theorem load_apply_evaluates (blockCtx : BlockCtx heapCtx) (heap : Heap) (ptr : Ptr) :
    EvalTriple.State.EvaluatesApply heapCtx heapOpCtx blockCtx
      (.opRef "load" [] [PtrTy] NatTy) [valPtr ptr]
      heap (Val.nat (Heap.read heap ptr)) heap := by
  intro env base
  have haction : Std.Do.Triple
      (do
        let value ← load ptr
        pure (some (Val.nat value)))
      (EvalTriple.Singleton.statePre heap)
      (EvalTriple.ActionPost (Machine.stateCtx heapCtx heapOpCtx blockCtx)
        (fun result => (EvalTriple.Singleton.statePost fun actual final =>
          actual = Val.nat (Heap.read heap ptr) ∧ final = heap).1 result)
        Std.Do.ExceptConds.false) := by
    zvcgen [load, Heap.read]
  apply EvalTriple.Steps.applyOpAction (oper := loadOp)
    (action := do
      let value ← load ptr
      pure (some (Val.nat value)))
  · rfl
  · exact loadOp_action_valPtr ptr
  · exact haction
  · intro result
    zvcgen [load, Heap.read]

theorem store_apply_evaluates (blockCtx : BlockCtx heapCtx) (heap : Heap)
    (ptr : Ptr) (value : Nat) :
    EvalTriple.State.EvaluatesApply heapCtx heapOpCtx blockCtx
      (.opRef "store" [] [PtrTy, NatTy] UnitTy) [valPtr ptr, Val.nat value]
      heap valUnit (Heap.write heap ptr value) := by
  intro env base
  have haction : Std.Do.Triple
      (do
        let _ ← store ptr value
        pure (some valUnit))
      (EvalTriple.Singleton.statePre heap)
      (EvalTriple.ActionPost (Machine.stateCtx heapCtx heapOpCtx blockCtx)
        (fun result => (EvalTriple.Singleton.statePost fun actual final =>
          actual = valUnit ∧ final = Heap.write heap ptr value).1 result)
        Std.Do.ExceptConds.false) := by
    zvcgen [store, Heap.write, valUnit]
  apply EvalTriple.Steps.applyOpAction (oper := storeOp)
    (action := do
      let _ ← store ptr value
      pure (some valUnit))
  · rfl
  · exact storeOp_action_vals ptr value
  · exact haction
  · intro result
    zvcgen [store, Heap.write, valUnit]

/-- The heap value language with only deterministic operators, for examples that do not access
memory. Keeping this context in `Id` makes their exact judgments honest after heap effects moved
to `StateM Heap`. -/
abbrev pureHeapOpCtx : OpCtx heapCtx Id :=
  Peano.opCtx heapCtx ++ [
    ("mod", binaryNatOp Nat.mod),
    ("le", binaryNatBoolOp fun a b => decide (a ≤ b)),
    ("not", Op.ofVals [BoolTy] BoolTy fun
      | [value] => do
          let b ← value.asBool?
          some (Val.bool (!b))
      | _ => none),
    ("bitAnd", binaryNatOp bitAnd),
    ("bitOr", binaryNatOp bitOr),
    ("bitXor", binaryNatOp bitXor),
    ("shl", binaryNatOp fun a b => a * pow2 b),
    ("shr", binaryNatOp fun a b => a / pow2 b),
    ("isDigit", Op.ofVals [NatTy] BoolTy fun
      | [value] => do
          let code ← value.asNat?
          some (Val.bool (isDigit code))
      | _ => none),
    ("digit", unaryNatOp parseDigit),
    ("ptrAdd", ptrAddOp),
    ("ptrAddr", ptrAddrOp),
    ("ptrOfNat", ptrOfNatOp),
    ("ptrEq", ptrEqOp),
    ("ptrIsNull", ptrIsNullOp),
    ("arrayGet", arrayGetOp),
    ("arraySet", arraySetOp),
    ("arraySwap", arraySwapOp),
    ("arrayLen", arrayLenOp),
    ("arrayCopy", arrayCopyOp),
    ("arrayFill", arrayFillOp),
    ("arraySort", arraySortOp),
    ("arrayInsertSorted", arrayInsertSortedOp)
  ]

abbrev mkPureCtx (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) : Ctx where
  primCtx := heapCtx
  opCtx := pureHeapOpCtx
  blockCtx := { val := blocks, isValid := h }

instance (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) :
    Peano.Model (mkPureCtx blocks h) where
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

end Zag.Test.Autocorres.Examples
