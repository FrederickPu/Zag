import Test.Autocorres.Examples.Common

/-!
Upstream C / AutoCorres `memcpy` example.

The **block program** matches the C loop (not a bulk `op "memcpy"`):

```c
for (i = 0; i < size; i++)
  d[i] = s[i];
return dest;
```

IR: `memcpyLoop` / `memcpyStep` with `ptrAdd`, `load`, `store`, `add`.
`Heap.copy` is the closed-form heap model of that loop. HeapAlgebra describes
footprint / frame / sep-copy of the model.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

private abbrev Ch (h h' : Heap) : Region :=
  HeapAlgebra.Peano.changed h h'

def sizeof_int : Nat := 1
def sizeof_my_structure : Nat := 3

/-! ### Block program (C `for`-loop shape) -/

abbrev memcpyBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    -- void *memcpy(void *dest, void *src, unsigned long size)
    -- Loop form: advance dst/src cursors (same as C `d[i]=s[i]; i++`).
    memcpyMemory(dst : Ptr, src : Ptr, len : Nat) : Ptr {
      ret call memcpyLoop [dst, dst, src, len]
    },
    -- (dst0, dst, src, remaining); done when remaining = 0
    memcpyLoop(dst0 : Ptr, dst : Ptr, src : Ptr, remaining : Nat) : Ptr {
      done := op "eq"[remaining, nat(0)];
      ret if done { dst0 }
        else { call memcpyStep [dst0, dst, src, remaining] }
    },
    -- *dst = *src; advance cursors; remaining--
    memcpyStep(dst0 : Ptr, dst : Ptr, src : Ptr, remaining : Nat) : Ptr {
      v := op "load"[src];
      written := op "store"[dst, v];
      dstNext := op "ptrAdd"[dst, nat(1)];
      srcNext := op "ptrAdd"[src, nat(1)];
      remNext := op "sub"[remaining, nat(1)];
      ret call memcpyLoop [dst0, dstNext, srcNext, remNext]
    },
    memcpyInt(dst : Ptr, src : Ptr) : Ptr {
      ret call memcpyMemory [dst, src, nat(sizeof_int)]
    },
    memcpyStruct(dst : Ptr, src : Ptr) : Ptr {
      ret call memcpyMemory [dst, src, nat(sizeof_my_structure)]
    }
  ]

theorem memcpyBlocksValid : BlockCtx.Valid memcpyBlocks := by
  valid_blocks [memcpyBlocks]

abbrev memcpyCtx : Ctx := mkCtx memcpyBlocks memcpyBlocksValid

theorem memcpyCtx_wellTyped : Ctx.WellTyped memcpyCtx := by typecheck_ctx

/-! ### Loop model (= pointer-stepping `Heap.copy`) -/

/-- Functional model of the remaining iterations with advancing `dst`/`src` cursors;
`dst0` is the original destination returned at the end. -/
def memcpyLoopFrom (dst0 : Ptr) : Heap → Ptr → Ptr → Nat → Heap × Ptr
  | h, _dst, _src, 0 => (h, dst0)
  | h, dst, src, remaining + 1 =>
      memcpyLoopFrom dst0
        (Heap.write h dst (Heap.read h src))
        ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ remaining

def memcpyLoopModel (h : Heap) (dst src : Ptr) (len : Nat) : Heap × Ptr :=
  memcpyLoopFrom dst h dst src len

theorem memcpyLoopFrom_eq_copy (dst0 : Ptr) :
    ∀ (h : Heap) (dst src : Ptr) (remaining : Nat),
      (memcpyLoopFrom dst0 h dst src remaining).1 = Heap.copy h dst src remaining ∧
      (memcpyLoopFrom dst0 h dst src remaining).2 = dst0 := by
  intro h dst src remaining
  induction remaining generalizing h dst src with
  | zero => simp [memcpyLoopFrom, Heap.copy]
  | succ remaining ih =>
      simp only [memcpyLoopFrom, Heap.copy]
      exact ih _ _ _

theorem memcpyLoopModel_eq_copy (h : Heap) (dst src : Ptr) (len : Nat) :
    (memcpyLoopModel h dst src len).1 = Heap.copy h dst src len ∧
    (memcpyLoopModel h dst src len).2 = dst :=
  memcpyLoopFrom_eq_copy dst h dst src len

/-! ### HeapAlgebra meaning of `Heap.copy` (loop's net effect) -/

def MemcpySeparated (dst src : Ptr) (len : Nat) : Prop :=
  noOverlap (range dst.addr len) (range src.addr len)

theorem range_shift_subset (base len : Nat) :
    range (base + 1) len ⊆ range base (len + 1) := by
  intro x hx
  simp only [range, Set.mem_Ico] at hx ⊢
  refine ⟨Nat.le_of_succ_le hx.1, ?_⟩
  have : base + 1 + len = base + (len + 1) := by omega
  exact this ▸ hx.2

theorem MemcpySeparated.shift {dst src : Ptr} {len : Nat}
    (h : MemcpySeparated dst src (len + 1)) :
    MemcpySeparated ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ len :=
  h.mono (range_shift_subset dst.addr len) (range_shift_subset src.addr len)

theorem Heap.read_copy_frame (h : Heap) (dst src : Ptr) (len a : Nat)
    (hout : a ∉ range dst.addr len) :
    Heap.read (Heap.copy h dst src len) ⟨a⟩ = Heap.read h ⟨a⟩ := by
  induction len generalizing h dst src with
  | zero => rfl
  | succ len ih =>
      simp only [Heap.copy]
      have hout' : a ∉ range (dst.addr + 1) len := by
        intro hin; apply hout; simp only [range, Set.mem_Ico] at hin ⊢; omega
      have hne : a ≠ dst.addr := by
        intro heq; subst heq
        exact hout ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos _)⟩
      exact (ih (Heap.write h dst (Heap.read h src)) ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ hout').trans
        (HeapAlgebra.Peano.Heap.read_write_of_ne h dst ⟨a⟩ (Heap.read h src) hne)

theorem Heap.copy_writes (h : Heap) (dst src : Ptr) (len : Nat) :
    Ch h (Heap.copy h dst src len) ≤ range dst.addr len := by
  induction len generalizing h dst src with
  | zero => intro a ha; simp [Heap.copy, HeapAlgebra.Peano.changed] at ha
  | succ len _ =>
      intro a ha
      by_cases hin : a ∈ range dst.addr (len + 1)
      · exact hin
      · exact absurd (Heap.read_copy_frame h dst src (len + 1) a hin).symm ha

theorem Heap.read_copy_dst (h : Heap) (dst src : Ptr) (len i : Nat)
    (hi : i < len) (hsep : MemcpySeparated dst src len) :
    Heap.read (Heap.copy h dst src len) ⟨dst.addr + i⟩ =
      Heap.read h ⟨src.addr + i⟩ := by
  induction len generalizing h dst src i with
  | zero => cases hi
  | succ len ih =>
      simp only [Heap.copy]
      cases i with
      | zero =>
          have hframe : dst.addr ∉ range (dst.addr + 1) len := by
            intro hin; simp [range, Set.mem_Ico] at hin; omega
          exact (Heap.read_copy_frame (Heap.write h dst (Heap.read h src))
            ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ len dst.addr hframe).trans
            (HeapAlgebra.Peano.Heap.read_write_same h dst (Heap.read h src))
      | succ i =>
          have hi' : i < len := Nat.lt_of_succ_lt_succ hi
          have ih' := ih (h := Heap.write h dst (Heap.read h src))
            (dst := ⟨dst.addr + 1⟩) (src := ⟨src.addr + 1⟩) (i := i) hi' hsep.shift
          have hne : src.addr + (i + 1) ≠ dst.addr := by
            intro heq
            exact Set.disjoint_left.1 hsep ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
          have hsrc := HeapAlgebra.Peano.Heap.read_write_of_ne h dst
            ⟨src.addr + (i + 1)⟩ (Heap.read h src) hne
          have ih'' :
              Heap.read
                  (Heap.copy (Heap.write h dst (Heap.read h src))
                    ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ len)
                  ⟨dst.addr + 1 + i⟩ =
                Heap.read (Heap.write h dst (Heap.read h src)) ⟨src.addr + 1 + i⟩ := by
            simpa using ih'
          have hsrc' :
              Heap.read (Heap.write h dst (Heap.read h src)) ⟨src.addr + 1 + i⟩ =
                Heap.read h ⟨src.addr + (i + 1)⟩ := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsrc
          have : dst.addr + (i + 1) = dst.addr + 1 + i := by omega
          rw [this]; exact ih''.trans hsrc'

/-- `src`-span holds `contents`, `dst`-span holds `dstOld` (only ownership of `dst` matters). -/
def memcpyPre (dst src : Ptr) (len : Nat) (contents dstOld : Nat → Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  segment dst.addr len dstOld ∗ segment src.addr len contents

/-- After copy: both spans hold `contents`. -/
def memcpyPost (dst src : Ptr) (len : Nat) (contents : Nat → Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  segment dst.addr len contents ∗ segment src.addr len contents

theorem memcpy_correct_sep (dst src : Ptr) (len : Nat) (contents dstOld : Nat → Nat)
    (h : Heap) (hp : (memcpyPre dst src len contents dstOld).holds h) :
    (memcpyPost dst src len contents).holds (Heap.copy h dst src len) := by
  have hsep : MemcpySeparated dst src len := hp.1
  refine ⟨hsep, ?_, ?_⟩
  · intro i hi
    exact (Heap.read_copy_dst h dst src len i hi hsep).trans (hp.2.2 i hi)
  · intro i hi
    have hout : src.addr + i ∉ range dst.addr len := by
      intro hin; exact Set.disjoint_left.1 hsep hin ⟨by omega, by omega⟩
    exact (Heap.read_copy_frame h dst src len (src.addr + i) hout).trans (hp.2.2 i hi)

/-! ### Operational correctness

Public specs: monadic `EvaluatesCall` with sep-logic assertions
`dst ↦ … ∗ src ↦ …` (no `Heap.copy` in the interface).
`Heap.copy` is only the private closed-form model of the loop spine.
-/

private abbrev subOpHeap : Op heapCtx (StateM Heap) :=
  Op.natBinary (primCtx := heapCtx) (M := StateM Heap) Nat.sub

private theorem heapOpCtx_get_eq : heapOpCtx.get? "eq" = some Op.eq := by
  simp [OpCtx.get?, heapOpCtx, Peano.opCtx]

private theorem heapOpCtx_get_ptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by
  simp [OpCtx.get?, heapOpCtx, Peano.opCtx]

private theorem heapOpCtx_get_ite : heapOpCtx.get? "ite" = some Op.ite := by
  simp [OpCtx.get?, heapOpCtx, Peano.opCtx]

private theorem heapOpCtx_get_sub' : heapOpCtx.get? "sub" = some subOpHeap := by
  simpa [subOpHeap] using heapOpCtx_get_sub

/-- `asNat?` on any `Val.mk NatTy` payload reduces via `toNat`. -/
private theorem asNat?_mk_payload (payload : Ty.type heapCtx Peano.NatTy) :
    (Val.mk Peano.NatTy payload : Val heapCtx).asNat? =
      some (Ty.toNat heapCtx payload) := by
  simp [Val.asNat?, Val.as?]

private theorem asNat?_mk_ofNat (n : Nat) :
    (Val.mk Peano.NatTy (Ty.ofNat heapCtx n) : Val heapCtx).asNat? = some n := by
  rw [asNat?_mk_payload, Ty.toNat_ofNat]

/-- Operand evaluation leaves `cast h n` payloads; reduce them like `Val.nat n`. -/
private theorem asNat?_mk_cast (n : Nat)
    (h : Nat = Ty.type heapCtx Peano.NatTy) :
    (Val.mk Peano.NatTy (cast h n) : Val heapCtx).asNat? = some n := by
  simp only [Val.asNat?, Val.as?, Ty.toNat]
  apply congrArg some
  -- `cast type_ground (cast h n) = n`
  have hcast : ∀ {α} (e₁ : Nat = α) (e₂ : α = Nat) (x : Nat),
      cast e₂ (cast e₁ x) = x := fun e₁ e₂ x => by
    cases e₁; rfl
  exact hcast h _ n

private theorem primEq?_mk_cast_self (n : Nat)
    (h₁ h₂ : Nat = Ty.type heapCtx Peano.NatTy) :
    (Val.mk Peano.NatTy (cast h₁ n) : Val heapCtx).primEq?
      (Val.mk Peano.NatTy (cast h₂ n)) = some true := by
  simp [Val.primEq?, asNat?_mk_cast]

private theorem toBool_true :
    Ty.toBool heapCtx (Ty.ofBool heapCtx true) = true :=
  Ty.toBool_ofBool heapCtx true

private theorem asBool?_bool_true :
    (Val.bool (primCtx := heapCtx) true).asBool? = some true :=
  Val.asBool?_bool true

/-- Resume `ret value` into a trivial `opBody (done ·)` frame. -/
private theorem resume_opBody_done_step
    (blockCtx : BlockCtx heapCtx) (env opEnv : Env heapCtx)
    (stack : List (Frame heapCtx)) (heap : Heap) (value : Val heapCtx) :
    Id.run ((Machine.step (Machine.stateCtx heapCtx heapOpCtx blockCtx)
      { control := .ret value, env := env,
        stack :=
          .opBody (fun | some v => .done v | none => .fail) [] opEnv :: stack }).run
      heap) =
      (some { control := .ret value, env := opEnv, stack := stack }, heap) := by
  simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp,
    Pure.pure, StateT.pure, Id.run, OptionT.mk, OptionT.run]

/-! ### Operational correctness

Public specs are monadic `Zag.EvaluatesCall` with sep-logic `HProp` assertions (`toAssertion` /
`⌜…⌝`). Exact-state `State.Evaluates*` is the private spine.
-/

/-- Internal: exact-state spine for the cursor loop. -/
private theorem memcpyLoop_evaluates_state (heap : Heap) (dst0 dst src : Ptr) (remaining : Nat) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx memcpyCtx.blockCtx
      "memcpyLoop" [valPtr dst0, valPtr dst, valPtr src, Val.nat remaining]
      heap (valPtr dst0) (Heap.copy heap dst src remaining) := by
  induction remaining generalizing heap dst src with
  | zero =>
      have hdone : decide ((0 : Nat) = 0) = true := by simp
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      simp only [Heap.copy]
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx memcpyCtx.blockCtx _
        heap (valPtr dst0) heap base
      repeat
        first
        | exact EvalTriple.State.EvaluatesFrom.done
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
                Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
                Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
                Machine.driveOp, Machine.start, heapOpCtx_get_eq, heapOpCtx_get_ite,
                hdone, Op.eq, Op.compare, Op.ite, Op.effectful, Op.Body.collect,
                Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
                Block.entryEnv, Scope.get?, Term.nat, Term.ite, Term.prim, Ty.ofNat,
                Ty.toNat, termPtr, valPtr, valUnit, asPtr?, Val.asNat?_nat,
                asNat?_mk_ofNat, asNat?_mk_cast, asNat?_mk_payload, primEq?_mk_cast_self,
                Val.as?, Val.mk_ofNat, Val.nat, Val.primEq?_nat, Val.primEq?,
                Val.asBool?_bool, Val.bool, Ty.toBool, Ty.ofBool, toBool_true,
                Option.bind, Id.run]
            rfl

  | succ remaining ih =>
      have hnot : decide ((remaining + 1 : Nat) = 0) = false := by simp
      let nextHeap := Heap.write heap dst (Heap.read heap src)
      have hrec :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx memcpyCtx.blockCtx
            "memcpyLoop"
            [valPtr dst0, valPtr ⟨dst.addr + 1⟩, valPtr ⟨src.addr + 1⟩,
              Val.nat (remaining + 1 - 1)]
            nextHeap (valPtr dst0)
            (Heap.copy nextHeap ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ remaining) := by
        simpa [Nat.add_sub_cancel] using
          ih (heap := nextHeap) (dst := ⟨dst.addr + 1⟩) (src := ⟨src.addr + 1⟩)
      have hstepCall :
          EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx memcpyCtx.blockCtx
            "memcpyStep" [valPtr dst0, valPtr dst, valPtr src, Val.nat (remaining + 1)]
            heap (valPtr dst0)
            (Heap.copy nextHeap ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ remaining) := by
        intro env base
        refine ⟨_, _, by rfl, by rfl, ?_⟩
        -- ListRev-style walker for step body
        repeat
          apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
                Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
                Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
                Machine.driveOp, Machine.start, heapOpCtx_get_ptrAdd, heapOpCtx_get_sub',
                heapOpCtx_get_load, heapOpCtx_get_store, ptrAddOp, subOpHeap, loadOp,
                storeOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
                Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
                Term.nat, Term.prim, Ty.ofNat, termPtr, valPtr, valUnit, asPtr?,
                Val.asNat?_nat, asNat?_mk_cast, asNat?_mk_ofNat]
            rfl
        apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx memcpyCtx.blockCtx) _).run heap) = _
          simpa [nextHeap] using storeOp_step memcpyCtx.blockCtx _ _ heap dst
            (Heap.read heap src)
        repeat
          first
          | apply EvalTriple.State.EvaluatesFrom.call_then hrec
            intro scope
            exact EvalTriple.State.EvaluatesFrom.return_to_call
          | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
            · set_option linter.unusedSimpArgs false in
                simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
                  Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
                  Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                  Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
                  Machine.driveOp, Machine.start, heapOpCtx_get_ptrAdd, heapOpCtx_get_sub',
                  heapOpCtx_get_load, heapOpCtx_get_store, ptrAddOp, subOpHeap, loadOp,
                  storeOp, Op.natBinary, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
                  Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
                  Scope.get?, Term.nat, Term.prim, Ty.ofNat, termPtr, valPtr, valUnit,
                  asPtr?, Val.asNat?_nat, asNat?_mk_cast, asNat?_mk_ofNat,
                  Nat.add_sub_cancel, resume_opBody_done_step]
              try exact resume_opBody_done_step memcpyCtx.blockCtx _ _ _ nextHeap _
              try rfl
      intro env base
      refine ⟨_, _, by rfl, by rfl, ?_⟩
      simp only [Heap.copy]
      change EvalTriple.State.EvaluatesFrom heapCtx heapOpCtx memcpyCtx.blockCtx _
        heap (valPtr dst0)
        (Heap.copy nextHeap ⟨dst.addr + 1⟩ ⟨src.addr + 1⟩ remaining) base
      repeat
        first
        | apply EvalTriple.State.EvaluatesFrom.call_then hstepCall
          intro scope
          exact EvalTriple.State.EvaluatesFrom.return_through_done_call
        | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
          · set_option linter.unusedSimpArgs false in
              simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
                Machine.evalTerm, Machine.applyValue, Machine.driveSelectedOp,
                Machine.ofOption, Machine.evalTermImmediate, Machine.applyValueImmediate,
                Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
                Machine.driveOp, Machine.start, heapOpCtx_get_eq, heapOpCtx_get_ite,
                hnot, Op.eq, Op.compare, Op.ite, Op.effectful, Op.Body.collect,
                Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
                Block.entryEnv, Scope.get?, Term.nat, Term.ite, Term.prim, Ty.ofNat,
                termPtr, valPtr, valUnit, asPtr?, Val.asNat?_nat, asNat?_mk_cast,
                asNat?_mk_ofNat, primEq?_mk_cast_self, Val.primEq?_nat, Val.primEq?]
            rfl

/-- Monadic post: `r = dst` and `dst ↦ contents ∗ src ↦ contents`. -/
def memcpyAssertPost (dst src : Ptr) (len : Nat) (contents : Nat → Nat)
    (result : Val heapCtx) : Std.Do.Assertion (Std.Do.PostShape.arg Heap .pure) :=
  fun h => ⌜result = valPtr dst ∧ (memcpyPost dst src len contents).holds h⌝

/-- Heaps satisfying the sep-logic pre of `memcpy`. -/
abbrev MemcpyPreHeap (dst src : Ptr) (len : Nat) (contents dstOld : Nat → Nat) : Type :=
  { h : Heap // (memcpyPre dst src len contents dstOld).holds h }

private abbrev memcpyStateCtx : Ctx :=
  Machine.stateCtx heapCtx heapOpCtx memcpyCtx.blockCtx

/-- Lift exact-state call specs to a sep-logic monadic `EvaluatesCall`. -/
private theorem evaluatesCall_of_sep
    (name : String) (args : List (Term heapCtx))
    (dst src : Ptr) (len : Nat) (contents dstOld : Nat → Nat)
    (f : Heap → Heap)
    (hexact : ∀ h, EvalTriple.State.EvaluatesCall heapCtx heapOpCtx memcpyCtx.blockCtx
      name args h (valPtr dst) (f h))
    (hpost : ∀ h, (memcpyPre dst src len contents dstOld).holds h →
      (memcpyPost dst src len contents).holds (f h)) :
    Zag.EvaluatesCall memcpyStateCtx name args
      (HProp.toAssertion (memcpyPre dst src len contents dstOld))
      (Std.Do.PostCond.noThrow (memcpyAssertPost dst src len contents)) := by
  change EvalTriple.EvaluatesFrom memcpyStateCtx (Machine.start [] (.call name args)) [] _ _
  apply EvalTriple.Steps.split
    (cases := fun hh : MemcpyPreHeap dst src len contents dstOld =>
      EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    have hex := hexact hh.1
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, memcpyAssertPost,
      hpost hh.1 hh.2]


private theorem memcpyMemory_evaluates_values_state
 (heap : Heap) (dst src : Ptr) (len : Nat) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx memcpyCtx.blockCtx
      "memcpyMemory" [valPtr dst, valPtr src, Val.nat len]
      heap (valPtr dst) (Heap.copy heap dst src len) := by
  have hloop := memcpyLoop_evaluates_state heap dst dst src len
  intro env base
  refine ⟨_, _, by rfl, by rfl, ?_⟩
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

private theorem memcpyMemory_evaluates_state (heap : Heap) (dst src : Ptr) (len : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx memcpyCtx.blockCtx
      "memcpyMemory" [termPtr dst.addr, termPtr src.addr, .nat len]
      heap (valPtr dst) (Heap.copy heap dst src len) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hloop := memcpyLoop_evaluates_state heap dst dst src len
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

/--
Sep-logic monadic spec of `memcpyMemory` (no `Heap.copy` in the interface):

```
{ dst ↦ old ∗ src ↦ contents }
  memcpyMemory(dst, src, len)
{ r = dst ∧ dst ↦ contents ∗ src ↦ contents }
```
-/
@[zspec] theorem memcpyMemory_eval (dst src : Ptr) (len : Nat)
    (contents dstOld : Nat → Nat) :
    Zag.EvaluatesCall memcpyStateCtx "memcpyMemory"
      [termPtr dst.addr, termPtr src.addr, .nat len]
      (HProp.toAssertion (memcpyPre dst src len contents dstOld))
      (Std.Do.PostCond.noThrow (memcpyAssertPost dst src len contents)) :=
  evaluatesCall_of_sep "memcpyMemory" _ dst src len contents dstOld
    (fun h => Heap.copy h dst src len)
    (fun h => memcpyMemory_evaluates_state h dst src len)
    (fun h hp => memcpy_correct_sep dst src len contents dstOld h hp)

private theorem memcpyInt_evaluates_state (heap : Heap) (dst src : Ptr) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx memcpyCtx.blockCtx
      "memcpyInt" [termPtr dst.addr, termPtr src.addr]
      heap (valPtr dst) (Heap.copy heap dst src sizeof_int) := by
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  have hmem := memcpyMemory_evaluates_values_state heap dst src sizeof_int
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hmem
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [memcpyCtx, mkCtx, memcpyBlocks, checkedBlocks, Machine.step,
            Machine.evalTerm, Machine.driveSelectedOp, Machine.ofOption,
            Machine.evalTermImmediate, Machine.applyValueImmediate,
            Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, Machine.start, Op.effectful, Op.Body.collect,
            Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
            Block.entryEnv, Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?,
            sizeof_int]
        rfl

private theorem cell_span (p : Ptr) :
    (cell p).span = range p.addr 1 := by
  simp [cell, OwnedPtr.span, range]

private theorem pointsTo_pre_holds (dst src : Ptr) (v old : Nat) (h : Heap) :
    ((dst ↦ old) ∗ (src ↦ v)).holds h ↔
      (memcpyPre dst src sizeof_int (fun _ => v) (fun _ => old)).holds h := by
  constructor
  · intro hholds
    have hdisj : noOverlap (cell dst).span (cell src).span := hholds.1
    have hold' : Heap.read h dst = old := (cell_pointsTo_holds dst old h).1 hholds.2.1
    have hv' : Heap.read h src = v := (cell_pointsTo_holds src v h).1 hholds.2.2
    refine ⟨?sep, ?dst, ?src⟩
    · change noOverlap (range dst.addr sizeof_int) (range src.addr sizeof_int)
      simpa [cell_span, sizeof_int] using hdisj
    · intro i hi
      have : i = 0 := by simp [sizeof_int] at hi; omega
      subst this; simpa [segment, sizeof_int] using hold'
    · intro i hi
      have : i = 0 := by simp [sizeof_int] at hi; omega
      subst this; simpa [segment, sizeof_int] using hv'
  · intro hholds
    have hsep : noOverlap (range dst.addr sizeof_int) (range src.addr sizeof_int) := hholds.1
    have hold : Heap.read h dst = old := by
      simpa [segment, sizeof_int] using hholds.2.1 0 (by simp [sizeof_int])
    have hv : Heap.read h src = v := by
      simpa [segment, sizeof_int] using hholds.2.2 0 (by simp [sizeof_int])
    refine ⟨?_, (cell_pointsTo_holds dst old h).2 hold, (cell_pointsTo_holds src v h).2 hv⟩
    change noOverlap (cell dst).span (cell src).span
    simpa [cell_span, sizeof_int] using hsep

private theorem pointsTo_post_holds (dst src : Ptr) (v : Nat) (h : Heap) :
    ((dst ↦ v) ∗ (src ↦ v)).holds h ↔
      (memcpyPost dst src sizeof_int (fun _ => v)).holds h := by
  -- same shape as pre with old = v
  simpa [memcpyPost, memcpyPre, HProp.sep] using pointsTo_pre_holds dst src v v h

/--
One-cell copy with `↦` in the actual theorem type:

```
{ dst ↦ old ∗ src ↦ v }
  memcpyInt(dst, src)
{ r = dst ∧ dst ↦ v ∗ src ↦ v }
```
-/
@[zspec] theorem memcpyInt_eval (dst src : Ptr) (v old : Nat) :
    Zag.EvaluatesCall memcpyStateCtx "memcpyInt"
      [termPtr dst.addr, termPtr src.addr]
      (HProp.toAssertion ((dst ↦ old) ∗ (src ↦ v)))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr dst ∧ ((dst ↦ v) ∗ (src ↦ v)).holds final⌝) := by
  have hpre :
      HProp.toAssertion ((dst ↦ old) ∗ (src ↦ v)) =
        HProp.toAssertion (memcpyPre dst src sizeof_int (fun _ => v) (fun _ => old)) := by
    funext heap; simp [HProp.toAssertion, pointsTo_pre_holds]
  have hpost :
      (fun result final =>
          ⌜result = valPtr dst ∧ ((dst ↦ v) ∗ (src ↦ v)).holds final⌝) =
        memcpyAssertPost dst src sizeof_int (fun _ => v) := by
    funext result final; simp [memcpyAssertPost, pointsTo_post_holds]
  rw [hpre, show Std.Do.PostCond.noThrow _ = Std.Do.PostCond.noThrow _ from
    congrArg Std.Do.PostCond.noThrow hpost]
  exact evaluatesCall_of_sep "memcpyInt" _ dst src sizeof_int (fun _ => v) (fun _ => old)
    (fun heap => Heap.copy heap dst src sizeof_int)
    (fun heap => memcpyInt_evaluates_state heap dst src)
    (fun heap hp =>
      memcpy_correct_sep dst src sizeof_int (fun _ => v) (fun _ => old) heap hp)

/-! ### Executable check -/

def heapReads (h : Heap) (addrs : List Nat) : List Nat :=
  addrs.map fun a => Heap.read h ⟨a⟩

theorem memcpyMemory_run :
    (match (Machine.evalFuel memcpyCtx 200 []
        (.call "memcpyMemory" [termPtr 4, termPtr 1, .nat 2])).run
          { next := 8, cells := [(1, 7), (2, 9), (4, 0), (5, 0)] } with
      | (some value, final) =>
          (asPtr? value, heapReads final [1, 2, 4, 5], final.next)
      | (none, final) => (none, heapReads final [1, 2, 4, 5], final.next)) =
    (some ⟨4⟩, [7, 9, 7, 9], 8) := by
  native_decide

end Zag.Test.Autocorres.Examples
