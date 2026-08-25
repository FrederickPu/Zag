import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`Memset.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/Memset.thy).

Public specs are monadic `EvaluatesCall` with sep-logic segments. `Heap.fill` is the private model.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev memsetBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    memsetMemory(start : Ptr, value : Nat, len : Nat) : Ptr {
      ret op "memset"[start, value, len]
    },
    zeroNode(start : Ptr) : Ptr {
      ret call memsetMemory [start, nat(0), nat(2)]
    }
  ]

theorem memsetBlocksValid : BlockCtx.Valid memsetBlocks := by
  valid_blocks [memsetBlocks]

abbrev memsetCtx : Ctx := mkCtx memsetBlocks memsetBlocksValid

theorem memsetCtx_wellTyped : Ctx.WellTyped memsetCtx := by
  typecheck_ctx

private abbrev memsetStateCtx : Ctx := heapStateCtx memsetBlocks memsetBlocksValid

def memsetByte (value : Nat) : Nat := value % 256

/-- Pre: span holds arbitrary old contents. -/
def memsetPre (start : Ptr) (len : Nat) (old : Nat → Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  segment start.addr len old

/-- Post: span filled with the truncated byte. -/
def memsetPost (start : Ptr) (len value : Nat) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  segment start.addr len (fun _ => memsetByte value)

private theorem Heap.read_fill_frame (h : Heap) (start : Ptr) (value len a : Nat)
    (hout : a < start.addr ∨ start.addr + len ≤ a) :
    Heap.read (Heap.fill h start value len) ⟨a⟩ = Heap.read h ⟨a⟩ := by
  induction len generalizing h start with
  | zero => rfl
  | succ len ih =>
      simp only [Heap.fill]
      have hout' : a < start.addr + 1 ∨ start.addr + 1 + len ≤ a := by
        cases hout with
        | inl h => exact Or.inl (Nat.lt_trans h (Nat.lt_succ_self _))
        | inr h =>
            right
            have : start.addr + 1 + len = start.addr + (len + 1) := by omega
            omega
      have hne : a ≠ start.addr := by
        intro heq; subst heq
        cases hout with
        | inl h => exact Nat.lt_irrefl _ h
        | inr h => exact Nat.not_le_of_gt (Nat.lt_add_of_pos_right (Nat.succ_pos _)) h
      exact (ih (Heap.write h start value) ⟨start.addr + 1⟩ hout').trans
        (HeapAlgebra.Peano.Heap.read_write_of_ne h start ⟨a⟩ value hne)

theorem memset_fill_contents (heap : Heap) (start : Ptr) (value len : Nat) :
    (memsetPost start len value).holds (Heap.fill heap start (memsetByte value) len) := by
  induction len generalizing heap start with
  | zero => intro i hi; cases hi
  | succ len ih =>
      intro i hi
      simp only [Heap.fill, memsetPost, segment, memsetByte]
      cases i with
      | zero =>
          have hframe :=
            Heap.read_fill_frame (Heap.write heap start (value % 256)) ⟨start.addr + 1⟩
              (value % 256) len start.addr (Or.inl (Nat.lt_succ_self _))
          exact hframe.trans (HeapAlgebra.Peano.Heap.read_write_same heap start (value % 256))
      | succ i =>
          have hi' : i < len := Nat.lt_of_succ_lt_succ hi
          have hrec := ih (Heap.write heap start (value % 256)) ⟨start.addr + 1⟩ i hi'
          have hadd : start.addr + (i + 1) = (start.addr + 1) + i := by omega
          rw [hadd]; exact hrec

theorem memset_sep_correct (heap : Heap) (start : Ptr) (value len : Nat)
    (old : Nat → Nat)
    (_hp : (memsetPre start len old).holds heap) :
    (memsetPost start len value).holds (Heap.fill heap start (memsetByte value) len) :=
  memset_fill_contents heap start value len

private theorem memsetMemory_evaluates_state (heap : Heap) (start : Ptr) (value len : Nat) :
    EvalTriple.State.EvaluatesCall heapCtx heapOpCtx
      (checkedBlocks memsetBlocks memsetBlocksValid) "memsetMemory"
      [termPtr start.addr, .nat value, .nat len] heap (valPtr start)
      (Heap.fill heap start (value % 256) len) := by
  rcases start with ⟨start⟩
  set_option zvcgen.resumeReturn true in
    zvcgen [memsetBlocks, checkedBlocks, memsetOp, Op.effectful, Op.Body.collect,
      Op.Arg.ofTerms, Op.Arg.ofVals, Block.entryEnv, Scope.get?, Term.nat,
      termPtr, valPtr, asPtr?, Val.ty_mk, Val.ty_nat, Val.mk_ofNat,
      Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr, driveOp_apply_done,
      resume_dependent_apply_done, memsetOp_action_vals]
  all_goals try solve_by_elim
  all_goals try obtain ⟨hstart, hvalue, hlen⟩ := ‹_ ∧ _ ∧ _›
  all_goals subst_vars
  all_goals try simp_all [Val.as?_mk, Val.asNat?_nat, toPtr_ofPtr]

/--
```
{ start ↦* old }
  memsetMemory(start, value, len)
{ r = start ∧ start ↦* (value % 256) }
```
-/
@[zspec] theorem memsetMemory_eval (start : Ptr) (value len : Nat) (old : Nat → Nat) :
    Zag.EvaluatesCall memsetStateCtx "memsetMemory"
      [termPtr start.addr, .nat value, .nat len]
      (HProp.toAssertion (memsetPre start len old))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valPtr start ∧ (memsetPost start len value).holds final⌝) :=
  evaluatesCall_of_hprop "memsetMemory" _
    (memsetPre start len old)
    (fun _ => memsetPost start len value)
    (valPtr start)
    (fun h => Heap.fill h start (memsetByte value) len)
    (fun h => by
      simpa [memsetByte] using memsetMemory_evaluates_state h start value len)
    (fun h _hp => memset_fill_contents h start value len)

theorem memsetMemory_run :
    (match (Machine.evalFuel memsetCtx 50 []
        (.call "memsetMemory" [termPtr 3, .nat 511, .nat 3])).run
          { next := 8, cells := [(3, 1), (4, 2), (5, 3)] } with
      | (some result, final) => (asPtr? result, final)
      | (none, final) => (none, final)) =
    (some ⟨3⟩,
      Heap.fill { next := 8, cells := [(3, 1), (4, 2), (5, 3)] } ⟨3⟩ (511 % 256) 3) := by
  native_decide

end Zag.Test.Autocorres.Examples
