import Test.Autocorres.Examples.Common

/-!
Upstream Isabelle theory:
[`SchorrWaite.thy`](https://github.com/seL4/l4v/blob/master/tools/autocorres/tests/examples/SchorrWaite.thy).

This is the source Schorr-Waite control flow over the flat PeanoHeap layout `[l, r, m, c]`.
`schorrWaitePush`, `schorrWaiteSwing`, and `schorrWaitePop` are the three pointer-reversal
transitions. Marks and link tests use the source convention that zero is false and every nonzero
value is true.

PeanoHeap has no allocation provenance or C object-validity predicate. Those source guards must be
stated separately by clients; they are not needed to encode the algorithm or its mutations.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap
open Zag.EvalTriple.Exact
open HeapAlgebra
open HeapAlgebra.Peano (OwnedPtr Region)
open HProp
open scoped HProp
open scoped Std.Do

abbrev schorrWaiteBlocks : BlockCtx.Raw heapCtx :=
  blocks% [
    schorrWaite(root : Ptr) : Unit {
      ret call schorrWaiteLoop [raw(termPtr 0), root]
    },
    schorrWaiteLoop(p : Ptr, t : Ptr) : Unit {
      pNull := op "ptrIsNull"[p];
      tNull := op "ptrIsNull"[t];
      tUnmarked := primEq (op "load"[op "ptrAdd"[t, nat(2)]]) nat(0);
      ret if pNull {
        if tNull { raw(termUnit) } else {
          if tUnmarked { call schorrWaitePush [p, t] } else { raw(termUnit) }
        }
      } else {
        if tNull { call schorrWaitePopOrSwing [p, t] } else {
          if tUnmarked { call schorrWaitePush [p, t] }
            else { call schorrWaitePopOrSwing [p, t] }
        }
      }
    },
    schorrWaitePush(p : Ptr, t : Ptr) : Unit {
      leftAddr := op "load"[t];
      leftPtr := op "ptrOfNat"[leftAddr];
      pAddr := op "ptrAddr"[p];
      storedLeft := op "store"[t, pAddr];
      storedMark := op "store"[op "ptrAdd"[t, nat(2)], nat(1)];
      storedControl := op "store"[op "ptrAdd"[t, nat(3)], nat(0)];
      ret call schorrWaiteLoop [t, leftPtr]
    },
    schorrWaitePopOrSwing(p : Ptr, t : Ptr) : Unit {
      clear := primEq (op "load"[op "ptrAdd"[p, nat(3)]]) nat(0);
      ret if clear { call schorrWaiteSwing [p, t] }
        else { call schorrWaitePop [p, t] }
    },
    schorrWaiteSwing(p : Ptr, t : Ptr) : Unit {
      rightAddr := op "load"[op "ptrAdd"[p, nat(1)]];
      rightPtr := op "ptrOfNat"[rightAddr];
      leftAddr := op "load"[p];
      tAddr := op "ptrAddr"[t];
      storedRight := op "store"[op "ptrAdd"[p, nat(1)], leftAddr];
      storedLeft := op "store"[p, tAddr];
      storedControl := op "store"[op "ptrAdd"[p, nat(3)], nat(1)];
      ret call schorrWaiteLoop [p, rightPtr]
    },
    schorrWaitePop(p : Ptr, t : Ptr) : Unit {
      rightAddr := op "load"[op "ptrAdd"[p, nat(1)]];
      rightPtr := op "ptrOfNat"[rightAddr];
      tAddr := op "ptrAddr"[t];
      storedRight := op "store"[op "ptrAdd"[p, nat(1)], tAddr];
      ret call schorrWaiteLoop [rightPtr, p]
    }
  ]

theorem schorrWaiteBlocksValid : BlockCtx.Valid schorrWaiteBlocks := by
  valid_blocks [schorrWaiteBlocks, termUnit]

abbrev schorrWaiteCtx : Ctx := mkCtx schorrWaiteBlocks schorrWaiteBlocksValid

theorem schorrWaiteCtx_wellTyped : Ctx.WellTyped schorrWaiteCtx := by
  typecheck_ctx

private abbrev schorrWaiteStateCtx : Ctx :=
  heapStateCtx schorrWaiteBlocks schorrWaiteBlocksValid

def swLeftField (ptr : Ptr) : Ptr := ptr
def swRightField (ptr : Ptr) : Ptr := ⟨ptr.addr + 1⟩
def swMarkField (ptr : Ptr) : Ptr := ⟨ptr.addr + 2⟩
def swControlField (ptr : Ptr) : Ptr := ⟨ptr.addr + 3⟩

def swField (ptr : Ptr) (offset : Nat) : Ptr := ⟨ptr.addr + offset⟩

def swNodeFootprint (initial : Heap) (node : Ptr) :
    HProp Heap OwnedPtr Region (fun _ => Nat) :=
  (swLeftField node ↦ Heap.read initial (swLeftField node)) ∗
    (swRightField node ↦ Heap.read initial (swRightField node)) ∗
      (swMarkField node ↦ Heap.read initial (swMarkField node)) ∗
        (swControlField node ↦ Heap.read initial (swControlField node))

def swGraphFootprint (initial : Heap) : List Ptr →
    HProp Heap OwnedPtr Region (fun _ => Nat)
| [] => HProp.emp
| node :: nodes => swNodeFootprint initial node ∗ swGraphFootprint initial nodes

@[simp] theorem swField_zero (ptr : Ptr) : swField ptr 0 = swLeftField ptr := by
  rfl

@[simp] theorem swField_one (ptr : Ptr) : swField ptr 1 = swRightField ptr := by
  simp [swField, swRightField]

@[simp] theorem swField_two (ptr : Ptr) : swField ptr 2 = swMarkField ptr := by
  rfl

@[simp] theorem swField_three (ptr : Ptr) : swField ptr 3 = swControlField ptr := by
  rfl

@[simp] theorem swRead_write_same (heap : Heap) (ptr : Ptr) (value : Nat) :
    Heap.read (Heap.write heap ptr value) ptr = value := by
  simp [Heap.read, Heap.write]

theorem swRead_write_of_ne {heap : Heap} {written read : Ptr} {value : Nat}
    (hne : written ≠ read) :
    Heap.read (Heap.write heap written value) read = Heap.read heap read := by
  simp [Heap.read, Heap.write, show written.addr ≠ read.addr by
    intro h
    apply hne
    cases written
    cases read
    simp_all]

/-- A finite collection of non-overlapping four-cell nodes in the initial heap. -/
structure SWGraph (heap : Heap) where
  nodes : List Ptr
  nodes_nodup : nodes.Nodup
  root : Ptr
  root_valid : root = null ∨ root ∈ nodes
  null_not_mem : null ∉ nodes
  fields_separated : ∀ {x y : Ptr} {i j : Nat}, x ∈ nodes → y ∈ nodes →
    i < 4 → j < 4 → swField x i = swField y j → x = y ∧ i = j
  left_valid : ∀ x ∈ nodes,
    Ptr.mk (Heap.read heap (swLeftField x)) = null ∨
      Ptr.mk (Heap.read heap (swLeftField x)) ∈ nodes
  right_valid : ∀ x ∈ nodes,
    Ptr.mk (Heap.read heap (swRightField x)) = null ∨
      Ptr.mk (Heap.read heap (swRightField x)) ∈ nodes
  initially_unmarked : ∀ x ∈ nodes, Heap.read heap (swMarkField x) = 0

def swOriginalLeft (heap : Heap) (node : Ptr) : Ptr :=
  ⟨Heap.read heap (swLeftField node)⟩

def swOriginalRight (heap : Heap) (node : Ptr) : Ptr :=
  ⟨Heap.read heap (swRightField node)⟩

inductive SWReachable (heap : Heap) (root : Ptr) : Ptr → Prop where
  | root (hne : root ≠ null) : SWReachable heap root root
  | left {node : Ptr} (hnode : SWReachable heap root node)
      (hne : swOriginalLeft heap node ≠ null) :
      SWReachable heap root (swOriginalLeft heap node)
  | right {node : Ptr} (hnode : SWReachable heap root node)
      (hne : swOriginalRight heap node ≠ null) :
      SWReachable heap root (swOriginalRight heap node)

structure SWFrame where
  node : Ptr
  rightPhase : Bool
deriving DecidableEq, Repr

def swFrameTarget (initial : Heap) (frame : SWFrame) : Ptr :=
  if frame.rightPhase then swOriginalRight initial frame.node
  else swOriginalLeft initial frame.node

def swStackNodes (stack : List SWFrame) : List Ptr := stack.map SWFrame.node

def swStackHead : List SWFrame → Ptr
  | [] => null
  | frame :: _ => frame.node

def SWStackPath (initial : Heap) : List SWFrame → Ptr → Prop
  | [], _ => True
  | frame :: rest, target =>
      swFrameTarget initial frame = target ∧ SWStackPath initial rest frame.node

def swMarked (heap : Heap) (node : Ptr) : Prop :=
  Heap.read heap (swMarkField node) ≠ 0

def swChildDone (heap : Heap) (child : Ptr) : Prop :=
  child = null ∨ swMarked heap child

def SWReversed (initial heap : Heap) : List SWFrame → Prop
  | [] => True
  | frame :: rest =>
      let parent := swStackHead rest
      (if frame.rightPhase then
          Heap.read heap (swLeftField frame.node) =
              Heap.read initial (swLeftField frame.node) ∧
            Heap.read heap (swRightField frame.node) = parent.addr ∧
            Heap.read heap (swControlField frame.node) ≠ 0 ∧
            swChildDone heap (swOriginalLeft initial frame.node)
        else
          Heap.read heap (swLeftField frame.node) = parent.addr ∧
            Heap.read heap (swRightField frame.node) =
              Heap.read initial (swRightField frame.node) ∧
            Heap.read heap (swControlField frame.node) = 0) ∧
        SWReversed initial heap rest

/-- The ghost stack describes exactly the links reversed by the executable program. -/
structure SWInvariant {initial : Heap} (graph : SWGraph initial)
    (heap : Heap) (p t : Ptr) (stack : List SWFrame) : Prop where
  p_eq : p = swStackHead stack
  stack_nodup : (swStackNodes stack).Nodup
  stack_path : SWStackPath initial stack t
  reversed : SWReversed initial heap stack
  restored : ∀ x ∈ graph.nodes, x ∉ swStackNodes stack →
    Heap.read heap (swLeftField x) = Heap.read initial (swLeftField x) ∧
      Heap.read heap (swRightField x) = Heap.read initial (swRightField x)
  stack_marked : ∀ x ∈ swStackNodes stack, swMarked heap x
  stack_reachable : ∀ x ∈ swStackNodes stack, SWReachable initial graph.root x
  marked_reachable : ∀ x ∈ graph.nodes, swMarked heap x →
    SWReachable initial graph.root x
  finished : ∀ x ∈ graph.nodes, swMarked heap x → x ∉ swStackNodes stack →
    swChildDone heap (swOriginalLeft initial x) ∧
      swChildDone heap (swOriginalRight initial x)
  target_valid : t = null ∨
    (t ∈ graph.nodes ∧ SWReachable initial graph.root t)
  root_started : graph.root = null ∨ swMarked heap graph.root ∨
    (stack = [] ∧ t = graph.root)

theorem SWGraph.swField_eq_iff {initial : Heap} (graph : SWGraph initial)
    {x y : Ptr} (hx : x ∈ graph.nodes) (hy : y ∈ graph.nodes)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    swField x i = swField y j ↔ x = y ∧ i = j := by
  constructor
  · exact graph.fields_separated hx hy hi hj
  · rintro ⟨rfl, rfl⟩
    rfl

theorem SWGraph.swField_ne {initial : Heap} (graph : SWGraph initial)
    {x y : Ptr} (hx : x ∈ graph.nodes) (hy : y ∈ graph.nodes)
    {i j : Nat} (hi : i < 4) (hj : j < 4) (hne : x ≠ y ∨ i ≠ j) :
    swField x i ≠ swField y j := by
  intro hfield
  have h := graph.fields_separated hx hy hi hj hfield
  exact hne.elim (fun hxy => hxy h.1) (fun hij => hij h.2)

theorem SWGraph.read_write_other {initial heap : Heap} (graph : SWGraph initial)
    {x y : Ptr} (hx : x ∈ graph.nodes) (hy : y ∈ graph.nodes)
    {i j value : Nat} (hi : i < 4) (hj : j < 4) (hne : x ≠ y ∨ i ≠ j) :
    Heap.read (Heap.write heap (swField x i) value) (swField y j) =
      Heap.read heap (swField y j) := by
  exact swRead_write_of_ne (graph.swField_ne hx hy hi hj hne)

theorem swNodeFootprint_read {initial heap : Heap} {node : Ptr} {i : Nat}
    (hp : (swNodeFootprint initial node).holds heap) (hi : i < 4) :
    Heap.read heap (swField node i) = Heap.read initial (swField node i) := by
  rcases hp with ⟨_hsepLeft, hleft, hrest⟩
  rcases hrest with ⟨_hsepRight, hright, hrest⟩
  rcases hrest with ⟨_hsepMark, hmark, hcontrol⟩
  cases i with
  | zero =>
      simpa using (cell_pointsTo_holds (swLeftField node)
        (Heap.read initial (swLeftField node)) heap).1 hleft
  | succ i =>
      cases i with
      | zero =>
          simpa using (cell_pointsTo_holds (swRightField node)
            (Heap.read initial (swRightField node)) heap).1 hright
      | succ i =>
          cases i with
          | zero =>
              simpa using (cell_pointsTo_holds (swMarkField node)
                (Heap.read initial (swMarkField node)) heap).1 hmark
          | succ i =>
              cases i with
              | zero =>
                  simpa using (cell_pointsTo_holds (swControlField node)
                    (Heap.read initial (swControlField node)) heap).1 hcontrol
              | succ i => omega

theorem swGraphFootprint_read {initial heap : Heap} {nodes : List Ptr}
    {node : Ptr} {i : Nat}
    (hp : (swGraphFootprint initial nodes).holds heap)
    (hnode : node ∈ nodes) (hi : i < 4) :
    Heap.read heap (swField node i) = Heap.read initial (swField node i) := by
  induction nodes with
  | nil => cases hnode
  | cons head tail ih =>
      rcases hp with ⟨_hsep, hhead, htail⟩
      simp only [List.mem_cons] at hnode
      rcases hnode with rfl | hnode
      · exact swNodeFootprint_read hhead hi
      · exact ih htail hnode

def swGraphRebase {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) : SWGraph heap where
  nodes := graph.nodes
  nodes_nodup := graph.nodes_nodup
  root := graph.root
  root_valid := graph.root_valid
  null_not_mem := graph.null_not_mem
  fields_separated := graph.fields_separated
  left_valid := by
    intro x hx
    have hread : Ptr.mk (Heap.read heap (swLeftField x)) =
        Ptr.mk (Heap.read initial (swLeftField x)) := by
      exact congrArg Ptr.mk (by
        simpa using swGraphFootprint_read (initial := initial) (heap := heap)
          (nodes := graph.nodes) hp hx (i := 0) (by omega))
    simpa [hread] using graph.left_valid x hx
  right_valid := by
    intro x hx
    have hread : Ptr.mk (Heap.read heap (swRightField x)) =
        Ptr.mk (Heap.read initial (swRightField x)) := by
      exact congrArg Ptr.mk (by
        simpa using swGraphFootprint_read (initial := initial) (heap := heap)
          (nodes := graph.nodes) hp hx (i := 1) (by omega))
    simpa [hread] using graph.right_valid x hx
  initially_unmarked := by
    intro x hx
    have hread := swGraphFootprint_read (initial := initial) (heap := heap)
      (nodes := graph.nodes) hp hx (i := 2) (by omega)
    simpa using hread.trans (graph.initially_unmarked x hx)

theorem SWReachable.mem {initial : Heap} (graph : SWGraph initial) {x : Ptr}
    (hreach : SWReachable initial graph.root x) : x ∈ graph.nodes := by
  induction hreach with
  | root hne => exact graph.root_valid.resolve_left hne
  | left hreach hne ih =>
      exact (graph.left_valid _ ih).resolve_left hne
  | right hreach hne ih =>
      exact (graph.right_valid _ ih).resolve_left hne

theorem SWReachable.ne_null {initial : Heap} {root x : Ptr}
    (hreach : SWReachable initial root x) : x ≠ null := by
  cases hreach with
  | root hne => exact hne
  | left _ hne => exact hne
  | right _ hne => exact hne

theorem swOriginalLeft_eq_of_footprint {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) {node : Ptr}
    (hnode : node ∈ graph.nodes) :
    swOriginalLeft heap node = swOriginalLeft initial node := by
  have hread := swGraphFootprint_read (initial := initial) (heap := heap)
    (nodes := graph.nodes) hp hnode (i := 0) (by omega)
  simpa [swOriginalLeft] using congrArg Ptr.mk hread

theorem swOriginalRight_eq_of_footprint {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) {node : Ptr}
    (hnode : node ∈ graph.nodes) :
    swOriginalRight heap node = swOriginalRight initial node := by
  have hread := swGraphFootprint_read (initial := initial) (heap := heap)
    (nodes := graph.nodes) hp hnode (i := 1) (by omega)
  simpa [swOriginalRight] using congrArg Ptr.mk hread

theorem swReachable_of_footprint {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) {x : Ptr}
    (hreach : SWReachable heap graph.root x) :
    SWReachable initial graph.root x := by
  induction hreach with
  | root hne => exact SWReachable.root hne
  | left hnode hne ih =>
      rename_i parent
      have hmem : parent ∈ graph.nodes := by
        simpa [swGraphRebase] using SWReachable.mem (swGraphRebase graph hp) hnode
      have heq := swOriginalLeft_eq_of_footprint graph hp hmem
      have hleft := SWReachable.left ih (by simpa [heq] using hne)
      simpa [heq] using hleft
  | right hnode hne ih =>
      rename_i parent
      have hmem : parent ∈ graph.nodes := by
        simpa [swGraphRebase] using SWReachable.mem (swGraphRebase graph hp) hnode
      have heq := swOriginalRight_eq_of_footprint graph hp hmem
      have hright := SWReachable.right ih (by simpa [heq] using hne)
      simpa [heq] using hright

theorem swReachable_to_footprint {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) {x : Ptr}
    (hreach : SWReachable initial graph.root x) :
    SWReachable heap graph.root x := by
  induction hreach with
  | root hne => exact SWReachable.root hne
  | left hnode hne ih =>
      rename_i parent
      have hmem : parent ∈ graph.nodes := SWReachable.mem graph hnode
      have heq := swOriginalLeft_eq_of_footprint graph hp hmem
      have hleft := SWReachable.left ih (by simpa [heq] using hne)
      simpa [heq] using hleft
  | right hnode hne ih =>
      rename_i parent
      have hmem : parent ∈ graph.nodes := SWReachable.mem graph hnode
      have heq := swOriginalRight_eq_of_footprint graph hp hmem
      have hright := SWReachable.right ih (by simpa [heq] using hne)
      simpa [heq] using hright

theorem swReachable_iff_footprint {initial heap : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap) {x : Ptr} :
    SWReachable heap graph.root x ↔ SWReachable initial graph.root x :=
  ⟨swReachable_of_footprint graph hp, swReachable_to_footprint graph hp⟩

theorem swInvariant_initial {initial : Heap} (graph : SWGraph initial) :
    SWInvariant graph initial null graph.root [] := by
  constructor
  · rfl
  · simp [swStackNodes]
  · simp [SWStackPath]
  · simp [SWReversed]
  · simp [swStackNodes]
  · simp [swStackNodes]
  · simp [swStackNodes]
  · intro x hx hmarked
    exact False.elim (hmarked (graph.initially_unmarked x hx))
  · intro x hx hmarked
    exact False.elim (hmarked (graph.initially_unmarked x hx))
  · exact graph.root_valid.elim (fun h => Or.inl h) fun h =>
      Or.inr ⟨h, SWReachable.root (fun hnull => graph.null_not_mem (hnull ▸ h))⟩
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem swInvariant_finished {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} (inv : SWInvariant graph heap p t [])
    (ht : t = null ∨ swMarked heap t) :
    (∀ x ∈ graph.nodes,
      (swMarked heap x ↔ SWReachable initial graph.root x) ∧
        Heap.read heap (swLeftField x) = Heap.read initial (swLeftField x) ∧
        Heap.read heap (swRightField x) = Heap.read initial (swRightField x)) := by
  have hroot : swChildDone heap graph.root := by
    rcases inv.root_started with hnull | hmarked | hstart
    · exact Or.inl hnull
    · exact Or.inr hmarked
    · exact hstart.2 ▸ ht
  have hreachMarked : ∀ {x : Ptr}, SWReachable initial graph.root x → swMarked heap x := by
    intro x hreach
    induction hreach with
    | root hne => exact hroot.resolve_left hne
    | left hparent hne ih =>
        have hchildren := inv.finished _ (SWReachable.mem graph hparent) ih (by simp [swStackNodes])
        exact hchildren.1.resolve_left hne
    | right hparent hne ih =>
        have hchildren := inv.finished _ (SWReachable.mem graph hparent) ih (by simp [swStackNodes])
        exact hchildren.2.resolve_left hne
  intro x hx
  have hlinks := inv.restored x hx (by simp [swStackNodes])
  exact ⟨⟨inv.marked_reachable x hx, hreachMarked⟩, hlinks.1, hlinks.2⟩

def swPushSpec (heap : Heap) (p t : Ptr) : Heap × Ptr × Ptr :=
  let nextT := Ptr.mk (Heap.read heap (swLeftField t))
  let heap := Heap.write heap (swLeftField t) p.addr
  let heap := Heap.write heap (swMarkField t) 1
  let heap := Heap.write heap (swControlField t) 0
  (heap, t, nextT)

def swSwingSpec (heap : Heap) (p t : Ptr) : Heap × Ptr × Ptr :=
  let nextT := Ptr.mk (Heap.read heap (swRightField p))
  let left := Heap.read heap (swLeftField p)
  let heap := Heap.write heap (swRightField p) left
  let heap := Heap.write heap (swLeftField p) t.addr
  let heap := Heap.write heap (swControlField p) 1
  (heap, p, nextT)

def swPopSpec (heap : Heap) (p t : Ptr) : Heap × Ptr × Ptr :=
  let nextP := Ptr.mk (Heap.read heap (swRightField p))
  let heap := Heap.write heap (swRightField p) t.addr
  (heap, nextP, p)

theorem swPushSpec_marks (heap : Heap) (p t : Ptr) :
    Heap.read (swPushSpec heap p t).1 (swMarkField t) = 1 := by
  simp [swPushSpec, swMarkField, swControlField, Heap.read, Heap.write]

theorem swPushSpec_sets_control (heap : Heap) (p t : Ptr) :
    Heap.read (swPushSpec heap p t).1 (swControlField t) = 0 := by
  simp [swPushSpec, swControlField, Heap.read, Heap.write]

theorem swPushSpec_sets_left (heap : Heap) (p t : Ptr) :
    Heap.read (swPushSpec heap p t).1 (swLeftField t) = p.addr := by
  simp [swPushSpec, swLeftField, swMarkField, swControlField, Heap.read, Heap.write]

theorem swPushSpec_preserves_mark_other {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (ht : t ∈ graph.nodes) (hx : x ∈ graph.nodes) (hne : x ≠ t) :
    Heap.read (swPushSpec heap p t).1 (swMarkField x) =
      Heap.read heap (swMarkField x) := by
  simp only [swPushSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField t 0) p.addr)
    (swField t 2) 1) (swField t 3) 0) (swField x 2) = Heap.read heap (swField x 2)
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inl hne.symm)]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inl hne.symm)]

theorem swPushSpec_preserves_left_other {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (ht : t ∈ graph.nodes) (hx : x ∈ graph.nodes) (hne : x ≠ t) :
    Heap.read (swPushSpec heap p t).1 (swLeftField x) =
      Heap.read heap (swLeftField x) := by
  simp only [swPushSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField t 0) p.addr)
    (swField t 2) 1) (swField t 3) 0) (swField x 0) = Heap.read heap (swField x 0)
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inl hne.symm)]

theorem swPushSpec_preserves_right {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (ht : t ∈ graph.nodes) (hx : x ∈ graph.nodes) :
    Heap.read (swPushSpec heap p t).1 (swRightField x) =
      Heap.read heap (swRightField x) := by
  simp only [swPushSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField t 0) p.addr)
    (swField t 2) 1) (swField t 3) 0) (swField x 1) = Heap.read heap (swField x 1)
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]

theorem swPushSpec_preserves_control_other {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (ht : t ∈ graph.nodes) (hx : x ∈ graph.nodes) (hne : x ≠ t) :
    Heap.read (swPushSpec heap p t).1 (swControlField x) =
      Heap.read heap (swControlField x) := by
  simp only [swPushSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField t 0) p.addr)
    (swField t 2) 1) (swField t 3) 0) (swField x 3) = Heap.read heap (swField x 3)
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inl hne.symm)]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other ht hx (by omega) (by omega) (Or.inl hne.symm)]

theorem swPushSpec_reversed_tail {initial heap : Heap} (graph : SWGraph initial)
    {p t : Ptr} {stack : List SWFrame} (ht : t ∈ graph.nodes)
    (htnot : t ∉ swStackNodes stack)
    (hstack : ∀ x ∈ swStackNodes stack, x ∈ graph.nodes)
    (hrev : SWReversed initial heap stack) :
    SWReversed initial (swPushSpec heap p t).1 stack := by
  induction stack with
  | nil => exact trivial
  | cons frame rest ih =>
      have hframe : frame.node ∈ graph.nodes := hstack frame.node (by simp [swStackNodes])
      have hne : frame.node ≠ t := by
        intro h
        apply htnot
        simp [swStackNodes, h]
      have doneMono : swChildDone heap (swOriginalLeft initial frame.node) →
          swChildDone (swPushSpec heap p t).1 (swOriginalLeft initial frame.node) := by
        intro hdone
        rcases hdone with hnull | hmarked
        · exact Or.inl hnull
        · rcases graph.left_valid frame.node hframe with hnull | hchildMem
          · exact Or.inl hnull
          · right
            by_cases hchild : swOriginalLeft initial frame.node = t
            · subst t
              simp [swMarked, swPushSpec_marks]
            · unfold swMarked at hmarked ⊢
              rw [swPushSpec_preserves_mark_other (x := swOriginalLeft initial frame.node)
                graph ht hchildMem hchild]
              exact hmarked
      simp only [SWReversed] at hrev ⊢
      constructor
      · cases hr : frame.rightPhase <;> simp [hr] at hrev ⊢
        · exact ⟨(swPushSpec_preserves_left_other graph ht hframe hne).trans hrev.1.1,
            (swPushSpec_preserves_right graph ht hframe).trans hrev.1.2.1,
            (swPushSpec_preserves_control_other graph ht hframe hne).symm ▸ hrev.1.2.2⟩
        · exact ⟨(swPushSpec_preserves_left_other graph ht hframe hne).trans hrev.1.1,
            (swPushSpec_preserves_right graph ht hframe).trans hrev.1.2.1,
            by rw [swPushSpec_preserves_control_other graph ht hframe hne]; exact hrev.1.2.2.1,
            doneMono hrev.1.2.2.2⟩
      · apply ih
        · intro hmem
          apply htnot
          change t ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hmem
        · intro x hx
          apply hstack x
          change x ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hx
        · exact hrev.2

theorem swPush_preserves_invariant {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {stack : List SWFrame} (inv : SWInvariant graph heap p t stack)
    (htNonNull : t ≠ null) (htUnmarked : ¬swMarked heap t) :
    SWInvariant graph (swPushSpec heap p t).1 t (swOriginalLeft initial t)
      ({ node := t, rightPhase := false } :: stack) := by
  have htReach : SWReachable initial graph.root t :=
    (inv.target_valid.resolve_left htNonNull).2
  have htMem : t ∈ graph.nodes := (inv.target_valid.resolve_left htNonNull).1
  have htNotStack : t ∉ swStackNodes stack := by
    intro hmem
    exact htUnmarked (inv.stack_marked t hmem)
  have hstackMem : ∀ x ∈ swStackNodes stack, x ∈ graph.nodes := by
    intro x hx
    exact SWReachable.mem graph (inv.stack_reachable x hx)
  have hleft : Heap.read heap (swLeftField t) = Heap.read initial (swLeftField t) :=
    (inv.restored t htMem htNotStack).1
  have hright : Heap.read heap (swRightField t) = Heap.read initial (swRightField t) :=
    (inv.restored t htMem htNotStack).2
  have markMono : ∀ {x : Ptr}, x ∈ graph.nodes → swMarked heap x →
      swMarked (swPushSpec heap p t).1 x := by
    intro x hx hmarked
    by_cases hxt : x = t
    · subst x
      simp [swMarked, swPushSpec_marks]
    · rw [swMarked, swPushSpec_preserves_mark_other graph htMem hx hxt]
      exact hmarked
  constructor
  · rfl
  · change (t :: swStackNodes stack).Nodup
    exact List.nodup_cons.mpr ⟨htNotStack, inv.stack_nodup⟩
  · exact ⟨rfl, inv.stack_path⟩
  · simp only [SWReversed]
    constructor
    · exact ⟨(swPushSpec_sets_left heap p t).trans (congrArg Ptr.addr inv.p_eq),
        (swPushSpec_preserves_right graph htMem htMem).trans hright,
        swPushSpec_sets_control heap p t⟩
    · exact swPushSpec_reversed_tail graph htMem htNotStack hstackMem inv.reversed
  · intro x hx hnot
    have hne : x ≠ t := by
      intro h
      apply hnot
      simp [swStackNodes, h]
    have hold := inv.restored x hx (by
      intro hmem
      apply hnot
      change x ∈ t :: swStackNodes stack
      exact List.mem_cons_of_mem _ hmem)
    exact ⟨(swPushSpec_preserves_left_other graph htMem hx hne).trans hold.1,
      (swPushSpec_preserves_right graph htMem hx).trans hold.2⟩
  · intro x hx
    have hx' : x = t ∨ x ∈ swStackNodes stack := by simpa [swStackNodes] using hx
    rcases hx' with rfl | hx
    · simp [swMarked, swPushSpec_marks]
    · exact markMono (hstackMem x hx) (inv.stack_marked x hx)
  · intro x hx
    have hx' : x = t ∨ x ∈ swStackNodes stack := by simpa [swStackNodes] using hx
    exact hx'.elim (fun h => h ▸ htReach) (inv.stack_reachable x)
  · intro x hx hmarked
    by_cases hxt : x = t
    · exact hxt ▸ htReach
    · apply inv.marked_reachable x hx
      rw [swMarked, swPushSpec_preserves_mark_other graph htMem hx hxt] at hmarked
      exact hmarked
  · intro x hx hmarked hnot
    have hne : x ≠ t := by
      intro h
      apply hnot
      simp [swStackNodes, h]
    have holdMarked : swMarked heap x := by
      rw [swMarked, swPushSpec_preserves_mark_other graph htMem hx hne] at hmarked
      exact hmarked
    have hnotOld : x ∉ swStackNodes stack := by
      intro hmem
      apply hnot
      change x ∈ t :: swStackNodes stack
      exact List.mem_cons_of_mem _ hmem
    have hchildren := inv.finished x hx holdMarked hnotOld
    constructor
    · rcases hchildren.1 with hnull | hchild
      · exact Or.inl hnull
      · rcases graph.left_valid x hx with hnull | hmem
        · exact Or.inl hnull
        · exact Or.inr (markMono hmem hchild)
    · rcases hchildren.2 with hnull | hchild
      · exact Or.inl hnull
      · rcases graph.right_valid x hx with hnull | hmem
        · exact Or.inl hnull
        · exact Or.inr (markMono hmem hchild)
  · let child := swOriginalLeft initial t
    by_cases hnull : child = null
    · exact Or.inl hnull
    · exact Or.inr ⟨(graph.left_valid t htMem).resolve_left hnull,
        SWReachable.left htReach hnull⟩
  · rcases inv.root_started with hnull | hmarked | hstart
    · exact Or.inl hnull
    · rcases graph.root_valid with hnull | hrootMem
      · exact Or.inl hnull
      · exact Or.inr (Or.inl (markMono hrootMem hmarked))
    · by_cases hroot : graph.root = t
      · exact Or.inr (Or.inl (hroot ▸ (by simp [swMarked, swPushSpec_marks])))
      · exact (hroot hstart.2.symm).elim

theorem swPopSpec_restores_right (heap : Heap) (p t : Ptr) :
    Heap.read (swPopSpec heap p t).1 (swRightField p) = t.addr := by
  simp [swPopSpec, swRightField, Heap.read, Heap.write]

theorem swPopSpec_preserves_mark {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (hp : p ∈ graph.nodes) (hx : x ∈ graph.nodes) :
    Heap.read (swPopSpec heap p t).1 (swMarkField x) = Heap.read heap (swMarkField x) := by
  simp only [swPopSpec]
  change Heap.read (Heap.write heap (swField p 1) t.addr) (swField x 2) =
    Heap.read heap (swField x 2)
  rw [graph.read_write_other hp hx (by omega) (by omega) (Or.inr (by omega))]

theorem swPopSpec_preserves_field_other {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (hp : p ∈ graph.nodes) (hx : x ∈ graph.nodes) (hne : x ≠ p)
    {j : Nat} (hj : j < 4) :
    Heap.read (swPopSpec heap p t).1 (swField x j) = Heap.read heap (swField x j) := by
  simp only [swPopSpec]
  change Heap.read (Heap.write heap (swField p 1) t.addr) (swField x j) =
    Heap.read heap (swField x j)
  rw [graph.read_write_other hp hx (by omega) hj (Or.inl hne.symm)]

theorem swPopSpec_preserves_left (heap : Heap) (p t : Ptr) :
    Heap.read (swPopSpec heap p t).1 (swLeftField p) = Heap.read heap (swLeftField p) := by
  simp [swPopSpec, swLeftField, swRightField, Heap.read, Heap.write]

theorem swPopSpec_reversed_tail {initial heap : Heap} (graph : SWGraph initial)
    {p t : Ptr} {stack : List SWFrame} (hp : p ∈ graph.nodes)
    (hpnot : p ∉ swStackNodes stack)
    (hstack : ∀ x ∈ swStackNodes stack, x ∈ graph.nodes)
    (hrev : SWReversed initial heap stack) :
    SWReversed initial (swPopSpec heap p t).1 stack := by
  induction stack with
  | nil => exact trivial
  | cons frame rest ih =>
      have hframe : frame.node ∈ graph.nodes := hstack frame.node (by simp [swStackNodes])
      have hne : frame.node ≠ p := by
        intro h
        apply hpnot
        simp [swStackNodes, h]
      simp only [SWReversed] at hrev ⊢
      constructor
      · cases hr : frame.rightPhase <;> simp [hr] at hrev ⊢
        · exact ⟨(swPopSpec_preserves_field_other graph hp hframe hne (j := 0) (by omega)).trans
              hrev.1.1,
            (swPopSpec_preserves_field_other graph hp hframe hne (j := 1) (by omega)).trans
              hrev.1.2.1,
            (swPopSpec_preserves_field_other graph hp hframe hne (j := 3) (by omega)).trans
              hrev.1.2.2⟩
        · refine ⟨(swPopSpec_preserves_field_other graph hp hframe hne (j := 0) (by omega)).trans
              hrev.1.1,
            (swPopSpec_preserves_field_other graph hp hframe hne (j := 1) (by omega)).trans
              hrev.1.2.1, ?_, ?_⟩
          · have hc := swPopSpec_preserves_field_other (heap := heap) (p := p) (t := t)
              graph hp hframe hne (j := 3) (by omega)
            have hc' : Heap.read (swPopSpec heap p t).1 (swControlField frame.node) =
                Heap.read heap (swControlField frame.node) := by
              simpa [swField, swControlField] using hc
            rw [hc']
            exact hrev.1.2.2.1
          · rcases hrev.1.2.2.2 with hnull | hmarked
            · exact Or.inl hnull
            · rcases graph.left_valid frame.node hframe with hnull | hchildMem
              · exact Or.inl hnull
              · exact Or.inr (by
                  unfold swMarked at hmarked ⊢
                  have hm := swPopSpec_preserves_mark (heap := heap) (p := p) (t := t)
                    (x := swOriginalLeft initial frame.node) graph hp hchildMem
                  rw [hm]
                  exact hmarked)
      · apply ih
        · intro hmem
          apply hpnot
          change p ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hmem
        · intro x hx
          apply hstack x
          change x ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hx
        · exact hrev.2

theorem swSwingSpec_sets_control (heap : Heap) (p t : Ptr) :
    Heap.read (swSwingSpec heap p t).1 (swControlField p) = 1 := by
  simp [swSwingSpec, swControlField, Heap.read, Heap.write]

theorem swSwingSpec_sets_left (heap : Heap) (p t : Ptr) :
    Heap.read (swSwingSpec heap p t).1 (swLeftField p) = t.addr := by
  simp [swSwingSpec, swLeftField, swRightField, swControlField, Heap.read, Heap.write]

theorem swSwingSpec_sets_right (heap : Heap) (p t : Ptr) :
    Heap.read (swSwingSpec heap p t).1 (swRightField p) =
      Heap.read heap (swLeftField p) := by
  simp [swSwingSpec, swLeftField, swRightField, swControlField, Heap.read, Heap.write]

theorem swSwingSpec_preserves_mark {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (hp : p ∈ graph.nodes) (hx : x ∈ graph.nodes) :
    Heap.read (swSwingSpec heap p t).1 (swMarkField x) =
      Heap.read heap (swMarkField x) := by
  simp only [swSwingSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField p 1)
    (Heap.read heap (swField p 0))) (swField p 0) t.addr) (swField p 3) 1)
    (swField x 2) = Heap.read heap (swField x 2)
  rw [graph.read_write_other hp hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other hp hx (by omega) (by omega) (Or.inr (by omega))]
  rw [graph.read_write_other hp hx (by omega) (by omega) (Or.inr (by omega))]

theorem swSwingSpec_preserves_field_other {initial heap : Heap} (graph : SWGraph initial)
    {p t x : Ptr} (hp : p ∈ graph.nodes) (hx : x ∈ graph.nodes) (hne : x ≠ p)
    {j : Nat} (hj : j < 4) :
    Heap.read (swSwingSpec heap p t).1 (swField x j) = Heap.read heap (swField x j) := by
  simp only [swSwingSpec]
  change Heap.read (Heap.write (Heap.write (Heap.write heap (swField p 1)
    (Heap.read heap (swField p 0))) (swField p 0) t.addr) (swField p 3) 1)
    (swField x j) = Heap.read heap (swField x j)
  rw [graph.read_write_other hp hx (by omega) hj (Or.inl hne.symm)]
  rw [graph.read_write_other hp hx (by omega) hj (Or.inl hne.symm)]
  rw [graph.read_write_other hp hx (by omega) hj (Or.inl hne.symm)]

theorem swSwingSpec_reversed_tail {initial heap : Heap} (graph : SWGraph initial)
    {p t : Ptr} {stack : List SWFrame} (hp : p ∈ graph.nodes)
    (hpnot : p ∉ swStackNodes stack)
    (hstack : ∀ x ∈ swStackNodes stack, x ∈ graph.nodes)
    (hrev : SWReversed initial heap stack) :
    SWReversed initial (swSwingSpec heap p t).1 stack := by
  induction stack with
  | nil => exact trivial
  | cons frame rest ih =>
      have hframe : frame.node ∈ graph.nodes := hstack frame.node (by simp [swStackNodes])
      have hne : frame.node ≠ p := by
        intro h
        apply hpnot
        simp [swStackNodes, h]
      simp only [SWReversed] at hrev ⊢
      constructor
      · cases hr : frame.rightPhase <;> simp [hr] at hrev ⊢
        · exact ⟨(swSwingSpec_preserves_field_other graph hp hframe hne (j := 0) (by omega)).trans
              hrev.1.1,
            (swSwingSpec_preserves_field_other graph hp hframe hne (j := 1) (by omega)).trans
              hrev.1.2.1,
            (swSwingSpec_preserves_field_other graph hp hframe hne (j := 3) (by omega)).trans
              hrev.1.2.2⟩
        · exact ⟨(swSwingSpec_preserves_field_other graph hp hframe hne (j := 0) (by omega)).trans
              hrev.1.1,
            (swSwingSpec_preserves_field_other graph hp hframe hne (j := 1) (by omega)).trans
              hrev.1.2.1,
            by
              have hc := swSwingSpec_preserves_field_other (heap := heap) (p := p) (t := t)
                graph hp hframe hne (j := 3) (by omega)
              have hc' : Heap.read (swSwingSpec heap p t).1 (swControlField frame.node) =
                  Heap.read heap (swControlField frame.node) := by
                simpa [swField, swControlField] using hc
              rw [hc']
              exact hrev.1.2.2.1,
            by
              rcases hrev.1.2.2.2 with hnull | hmarked
              · exact Or.inl hnull
              · rcases graph.left_valid frame.node hframe with hnull | hchildMem
                · exact Or.inl hnull
                · exact Or.inr (by
                    unfold swMarked at hmarked ⊢
                    have hm := swSwingSpec_preserves_mark (heap := heap) (p := p) (t := t)
                      (x := swOriginalLeft initial frame.node) graph hp hchildMem
                    rw [hm]
                    exact hmarked)⟩
      · apply ih
        · intro hmem
          apply hpnot
          change p ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hmem
        · intro x hx
          apply hstack x
          change x ∈ frame.node :: swStackNodes rest
          exact List.mem_cons_of_mem _ hx
        · exact hrev.2

theorem swSwing_preserves_invariant {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = false) (htDone : swChildDone heap t) :
    SWInvariant graph (swSwingSpec heap p t).1 p (swOriginalRight initial p)
      ({ node := p, rightPhase := true } :: rest) := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hpMemStack : p ∈ swStackNodes (frame :: rest) := by simp [swStackNodes, hp]
  have hpReach := inv.stack_reachable p hpMemStack
  have hpMem := SWReachable.mem graph hpReach
  have hpNotRest : p ∉ swStackNodes rest := by
    have hnodup := inv.stack_nodup
    change (frame.node :: swStackNodes rest).Nodup at hnodup
    simpa [hp] using (List.nodup_cons.mp hnodup).1
  have hrestMem : ∀ x ∈ swStackNodes rest, x ∈ graph.nodes := by
    intro x hx
    apply SWReachable.mem graph
    apply inv.stack_reachable x
    change x ∈ frame.node :: swStackNodes rest
    exact List.mem_cons_of_mem _ hx
  have hpath := inv.stack_path
  simp only [SWStackPath] at hpath
  have htarget : swOriginalLeft initial p = t := by
    simpa [swFrameTarget, hphase, hp] using hpath.1
  have hrev := inv.reversed
  simp only [SWReversed] at hrev
  simp [hphase] at hrev
  have markEq : ∀ {x : Ptr}, x ∈ graph.nodes →
      (swMarked (swSwingSpec heap p t).1 x ↔ swMarked heap x) := by
    intro x hx
    unfold swMarked
    rw [swSwingSpec_preserves_mark graph hpMem hx]
  have doneEq : ∀ {x child : Ptr}, x ∈ graph.nodes →
      (child = swOriginalLeft initial x ∨ child = swOriginalRight initial x) →
      (swChildDone (swSwingSpec heap p t).1 child ↔ swChildDone heap child) := by
    intro x child hx hchild
    rcases hchild with rfl | rfl
    · rcases graph.left_valid x hx with hnull | hmem
      · change swOriginalLeft initial x = null at hnull
        simp [swChildDone, hnull]
      · simp only [swChildDone]
        exact or_congr Iff.rfl (markEq hmem)
    · rcases graph.right_valid x hx with hnull | hmem
      · change swOriginalRight initial x = null at hnull
        simp [swChildDone, hnull]
      · simp only [swChildDone]
        exact or_congr Iff.rfl (markEq hmem)
  constructor
  · simpa [swStackHead]
  · change (p :: swStackNodes rest).Nodup
    exact List.nodup_cons.mpr ⟨hpNotRest, by
      have hnodup := inv.stack_nodup
      change (frame.node :: swStackNodes rest).Nodup at hnodup
      exact (List.nodup_cons.mp hnodup).2⟩
  · exact ⟨rfl, by simpa [hp] using hpath.2⟩
  · simp only [SWReversed]
    constructor
    · simp only [Bool.if_true_right, ↓reduceIte]
      refine ⟨?_, ?_, by
        intro hzero
        have hone := swSwingSpec_sets_control heap p t
        omega, ?_⟩
      · rw [swSwingSpec_sets_left, ← htarget]
        rfl
      · exact (swSwingSpec_sets_right heap p t).trans (by simpa [hp] using hrev.1.1)
      · rw [doneEq hpMem (Or.inl rfl)]
        simpa [htarget] using htDone
    · exact swSwingSpec_reversed_tail graph hpMem hpNotRest hrestMem hrev.2
  · intro x hx hnot
    have hne : x ≠ p := by
      intro h
      apply hnot
      simp [swStackNodes, h]
    have hold := inv.restored x hx (by
      intro hmem
      apply hnot
      have hmem' : x = frame.node ∨ x ∈ swStackNodes rest := by
        simpa [swStackNodes] using hmem
      simpa [swStackNodes, hp] using hmem')
    exact ⟨(swSwingSpec_preserves_field_other graph hpMem hx hne (j := 0) (by omega)).trans
        hold.1,
      (swSwingSpec_preserves_field_other graph hpMem hx hne (j := 1) (by omega)).trans
        hold.2⟩
  · intro x hx
    rw [markEq (SWReachable.mem graph (by
      apply inv.stack_reachable x
      have hx' : x = p ∨ x ∈ swStackNodes rest := by simpa [swStackNodes] using hx
      simpa [swStackNodes, hp] using hx'))]
    apply inv.stack_marked x
    have hx' : x = p ∨ x ∈ swStackNodes rest := by simpa [swStackNodes] using hx
    simpa [swStackNodes, hp] using hx'
  · intro x hx
    have hx' : x = p ∨ x ∈ swStackNodes rest := by simpa [swStackNodes] using hx
    apply inv.stack_reachable x
    simpa [swStackNodes, hp] using hx'
  · intro x hx hmarked
    apply inv.marked_reachable x hx
    exact (markEq hx).mp hmarked
  · intro x hx hmarked hnot
    have holdMarked := (markEq hx).mp hmarked
    have hnotOld : x ∉ swStackNodes (frame :: rest) := by
      intro hmem
      apply hnot
      have hmem' : x = frame.node ∨ x ∈ swStackNodes rest := by
        simpa [swStackNodes] using hmem
      simpa [swStackNodes, hp] using hmem'
    have hchildren := inv.finished x hx holdMarked hnotOld
    exact ⟨(doneEq hx (Or.inl rfl)).mpr hchildren.1,
      (doneEq hx (Or.inr rfl)).mpr hchildren.2⟩
  · let child := swOriginalRight initial p
    by_cases hnull : child = null
    · exact Or.inl hnull
    · exact Or.inr ⟨(graph.right_valid p hpMem).resolve_left hnull,
        SWReachable.right hpReach hnull⟩
  · rcases inv.root_started with hnull | hmarked | hstart
    · exact Or.inl hnull
    · rcases graph.root_valid with hnull | hmem
      · exact Or.inl hnull
      · exact Or.inr (Or.inl ((markEq hmem).mpr hmarked))
    · have : False := by simpa [swStackHead] using congrArg List.length hstart.1
      contradiction

theorem swPop_preserves_invariant {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = true) (htDone : swChildDone heap t) :
    SWInvariant graph (swPopSpec heap p t).1 (swStackHead rest) p rest := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hpMemStack : p ∈ swStackNodes (frame :: rest) := by simp [swStackNodes, hp]
  have hpReach := inv.stack_reachable p hpMemStack
  have hpMem := SWReachable.mem graph hpReach
  have hpMarked := inv.stack_marked p hpMemStack
  have hpNotRest : p ∉ swStackNodes rest := by
    have hnodup := inv.stack_nodup
    change (frame.node :: swStackNodes rest).Nodup at hnodup
    simpa [hp] using (List.nodup_cons.mp hnodup).1
  have hrestMem : ∀ x ∈ swStackNodes rest, x ∈ graph.nodes := by
    intro x hx
    apply SWReachable.mem graph
    apply inv.stack_reachable x
    change x ∈ frame.node :: swStackNodes rest
    exact List.mem_cons_of_mem _ hx
  have hpath := inv.stack_path
  simp only [SWStackPath] at hpath
  have htarget : swOriginalRight initial p = t := by
    simpa [swFrameTarget, hphase, hp] using hpath.1
  have hrev := inv.reversed
  simp only [SWReversed] at hrev
  simp [hphase] at hrev
  have markEq : ∀ {x : Ptr}, x ∈ graph.nodes →
      (swMarked (swPopSpec heap p t).1 x ↔ swMarked heap x) := by
    intro x hx
    unfold swMarked
    rw [swPopSpec_preserves_mark graph hpMem hx]
  have doneEq : ∀ {x child : Ptr}, x ∈ graph.nodes →
      (child = swOriginalLeft initial x ∨ child = swOriginalRight initial x) →
      (swChildDone (swPopSpec heap p t).1 child ↔ swChildDone heap child) := by
    intro x child hx hchild
    rcases hchild with rfl | rfl
    · rcases graph.left_valid x hx with hnull | hmem
      · change swOriginalLeft initial x = null at hnull
        simp [swChildDone, hnull]
      · simp only [swChildDone]
        exact or_congr Iff.rfl (markEq hmem)
    · rcases graph.right_valid x hx with hnull | hmem
      · change swOriginalRight initial x = null at hnull
        simp [swChildDone, hnull]
      · simp only [swChildDone]
        exact or_congr Iff.rfl (markEq hmem)
  constructor
  · rfl
  · exact (List.nodup_cons.mp (by
      have h := inv.stack_nodup
      change (frame.node :: swStackNodes rest).Nodup at h
      exact h)).2
  · simpa [hp] using hpath.2
  · exact swPopSpec_reversed_tail graph hpMem hpNotRest hrestMem hrev.2
  · intro x hx hnot
    by_cases hxp : x = p
    · subst x
      constructor
      · exact (swPopSpec_preserves_left heap p t).trans (by simpa [hp] using hrev.1.1)
      · exact (swPopSpec_restores_right heap p t).trans
          (congrArg Ptr.addr htarget).symm
    · have hold := inv.restored x hx (by
        intro hmem
        have hmem' : x = frame.node ∨ x ∈ swStackNodes rest := by
          simpa [swStackNodes] using hmem
        exact hmem'.elim (fun h => hxp (h.trans hp.symm)) hnot)
      exact ⟨(swPopSpec_preserves_field_other graph hpMem hx hxp (j := 0) (by omega)).trans
          hold.1,
        (swPopSpec_preserves_field_other graph hpMem hx hxp (j := 1) (by omega)).trans
          hold.2⟩
  · intro x hx
    rw [markEq (hrestMem x hx)]
    apply inv.stack_marked x
    change x ∈ frame.node :: swStackNodes rest
    exact List.mem_cons_of_mem _ hx
  · intro x hx
    apply inv.stack_reachable x
    change x ∈ frame.node :: swStackNodes rest
    exact List.mem_cons_of_mem _ hx
  · intro x hx hmarked
    exact inv.marked_reachable x hx ((markEq hx).mp hmarked)
  · intro x hx hmarked hnot
    by_cases hxp : x = p
    · subst x
      exact ⟨(doneEq hpMem (Or.inl rfl)).mpr (by simpa [hp] using hrev.1.2.2.2),
        (doneEq hpMem (Or.inr rfl)).mpr (by simpa [htarget] using htDone)⟩
    · have holdMarked := (markEq hx).mp hmarked
      have hnotOld : x ∉ swStackNodes (frame :: rest) := by
        intro hmem
        have hmem' : x = frame.node ∨ x ∈ swStackNodes rest := by
          simpa [swStackNodes] using hmem
        exact hmem'.elim (fun h => hxp (h.trans hp.symm)) hnot
      have hchildren := inv.finished x hx holdMarked hnotOld
      exact ⟨(doneEq hx (Or.inl rfl)).mpr hchildren.1,
        (doneEq hx (Or.inr rfl)).mpr hchildren.2⟩
  · exact Or.inr ⟨hpMem, hpReach⟩
  · rcases inv.root_started with hnull | hmarked | hstart
    · exact Or.inl hnull
    · rcases graph.root_valid with hnull | hmem
      · exact Or.inl hnull
      · exact Or.inr (Or.inl ((markEq hmem).mpr hmarked))
    · have : False := by simpa [swStackHead] using congrArg List.length hstart.1
      contradiction

def swUnmarkedCount {initial : Heap} (graph : SWGraph initial) (heap : Heap) : Nat :=
  (graph.nodes.filter fun x => Heap.read heap (swMarkField x) = 0).length

def swLeftCount (stack : List SWFrame) : Nat :=
  (stack.filter fun frame => frame.rightPhase = false).length

def swMeasure {initial : Heap} (graph : SWGraph initial) (heap : Heap)
    (stack : List SWFrame) : Nat :=
  4 * swUnmarkedCount graph heap + 2 * swLeftCount stack + stack.length

theorem swFilter_remove_one {α : Type} [DecidableEq α] {xs : List α} {target : α}
    {pred : α → Bool} (hnodup : xs.Nodup) (hmem : target ∈ xs) (hpred : pred target = true) :
    (xs.filter fun x => x != target && pred x).length + 1 = (xs.filter pred).length := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
      have htailNodup := (List.nodup_cons.mp hnodup).2
      by_cases hxt : x = target
      · subst x
        have heq : xs.filter (fun y => y != target && pred y) = xs.filter pred := by
          apply List.filter_congr
          intro y hy
          have hyne : y ≠ target := by
            intro h
            subst y
            exact (List.nodup_cons.mp hnodup).1 hy
          simp [hyne]
        simp [hpred, heq]
      · have htargetTail : target ∈ xs := (List.mem_cons.mp hmem).resolve_left
          (fun h => hxt h.symm)
        have hrec := ih htailNodup htargetTail
        by_cases hp : pred x
        · simp [hxt, hp, hrec]
        · simp [hxt, hp, hrec]

theorem swPush_measure_decreases {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {stack : List SWFrame} (inv : SWInvariant graph heap p t stack)
    (htNonNull : t ≠ null) (htUnmarked : ¬swMarked heap t) :
    swMeasure graph (swPushSpec heap p t).1
        ({ node := t, rightPhase := false } :: stack) <
      swMeasure graph heap stack := by
  have htMem := (inv.target_valid.resolve_left htNonNull).1
  have htZero : Heap.read heap (swMarkField t) = 0 := by
    simp only [swMarked] at htUnmarked
    omega
  have hpoint : graph.nodes.filter
        (fun x => Heap.read (swPushSpec heap p t).1 (swMarkField x) = 0) =
      graph.nodes.filter (fun x => x != t && Heap.read heap (swMarkField x) = 0) := by
    apply List.filter_congr
    intro x hx
    by_cases hxt : x = t
    · subst x
      simp [swPushSpec_marks]
    · simp [hxt, swPushSpec_preserves_mark_other graph htMem hx hxt]
  have hcount : swUnmarkedCount graph (swPushSpec heap p t).1 + 1 =
      swUnmarkedCount graph heap := by
    rw [swUnmarkedCount, hpoint, swUnmarkedCount]
    exact swFilter_remove_one graph.nodes_nodup htMem (by simp [htZero])
  simp [swMeasure, swLeftCount]
  omega

theorem swSwing_measure_decreases {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = false) :
    swMeasure graph (swSwingSpec heap p t).1 ({ node := p, rightPhase := true } :: rest) <
      swMeasure graph heap (frame :: rest) := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hpMem : p ∈ graph.nodes := SWReachable.mem graph
    (inv.stack_reachable p (by simp [swStackNodes, hp]))
  have hcount : swUnmarkedCount graph (swSwingSpec heap p t).1 =
      swUnmarkedCount graph heap := by
    unfold swUnmarkedCount
    apply congrArg List.length
    apply List.filter_congr
    intro x hx
    rw [swSwingSpec_preserves_mark graph hpMem hx]
  simp [swMeasure, swLeftCount, hcount, hphase]

theorem swPop_measure_decreases {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = true) :
    swMeasure graph (swPopSpec heap p t).1 rest < swMeasure graph heap (frame :: rest) := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hpMem : p ∈ graph.nodes := SWReachable.mem graph
    (inv.stack_reachable p (by simp [swStackNodes, hp]))
  have hcount : swUnmarkedCount graph (swPopSpec heap p t).1 =
      swUnmarkedCount graph heap := by
    unfold swUnmarkedCount
    apply congrArg List.length
    apply List.filter_congr
    intro x hx
    rw [swPopSpec_preserves_mark graph hpMem hx]
  simp [swMeasure, swLeftCount, hcount, hphase]

def SWPost {initial : Heap} (graph : SWGraph initial) (heap : Heap) : Prop :=
  ∀ x ∈ graph.nodes,
    (swMarked heap x ↔ SWReachable initial graph.root x) ∧
      Heap.read heap (swLeftField x) = Heap.read initial (swLeftField x) ∧
      Heap.read heap (swRightField x) = Heap.read initial (swRightField x)

theorem SWPost.of_footprint {initial heap final : Heap} (graph : SWGraph initial)
    (hp : (swGraphFootprint initial graph.nodes).holds heap)
    (hpost : SWPost (swGraphRebase graph hp) final) :
    SWPost graph final := by
  intro x hx
  have hpostX := hpost x (by simpa [swGraphRebase] using hx)
  have hmarked : swMarked final x ↔ SWReachable initial graph.root x := by
    have hmarkedHeap : swMarked final x ↔ SWReachable heap graph.root x := by
      simpa [swGraphRebase] using hpostX.1
    exact hmarkedHeap.trans (swReachable_iff_footprint graph hp)
  have hleftHeap : Heap.read final (swLeftField x) = Heap.read heap (swLeftField x) := by
    simpa [swGraphRebase] using hpostX.2.1
  have hrightHeap : Heap.read final (swRightField x) = Heap.read heap (swRightField x) := by
    simpa [swGraphRebase] using hpostX.2.2
  refine ⟨hmarked, ?_, ?_⟩
  · exact hleftHeap.trans (by
      simpa using swGraphFootprint_read (initial := initial) (heap := heap)
        (nodes := graph.nodes) hp hx (i := 0) (by omega))
  · exact hrightHeap.trans (by
      simpa using swGraphFootprint_read (initial := initial) (heap := heap)
        (nodes := graph.nodes) hp hx (i := 1) (by omega))

private theorem schorrWaitePush_evaluates_values (heap final : Heap) (p t : Ptr)
    (hloop : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr (swPushSpec heap p t).2.1,
        valPtr (swPushSpec heap p t).2.2] (swPushSpec heap p t).1 valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePush" [valPtr p, valPtr t] heap valUnit final := by
  let leftHeap := Heap.write heap (swLeftField t) p.addr
  let markedHeap := Heap.write leftHeap (swMarkField t) 1
  let nextHeap := Heap.write markedHeap (swControlField t) 0
  have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr t,
        valPtr (Ptr.mk (Heap.read heap (swLeftField t)))] nextHeap valUnit final := by
    simpa [swPushSpec, leftHeap, markedHeap, nextHeap] using hloop
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have hstore : heapOpCtx.get? "store" = some storeOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by rfl
  have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by rfl
  intro env base
  let block := schorrWaiteBlocks[2].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaitePush" env :: base),
    by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
        simpa using loadOp_step schorrWaiteCtx.blockCtx _ _ heap (swLeftField t)
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := leftHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
    simpa [leftHeap, swLeftField] using storeOp_step schorrWaiteCtx.blockCtx _ _ heap
      (swLeftField t) p.addr
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := leftHeap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := markedHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run leftHeap) = _
    simpa [markedHeap, swMarkField] using storeOp_step schorrWaiteCtx.blockCtx _ _ leftHeap
      (swMarkField t) 1
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := markedHeap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run markedHeap) = _
    simpa [nextHeap, swControlField] using storeOp_step schorrWaiteCtx.blockCtx _ _ markedHeap
      (swControlField t) 0
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop'
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

private theorem schorrWaiteSwing_evaluates_values (heap final : Heap) (p t : Ptr)
    (hloop : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr (swSwingSpec heap p t).2.1,
        valPtr (swSwingSpec heap p t).2.2] (swSwingSpec heap p t).1 valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteSwing" [valPtr p, valPtr t] heap valUnit final := by
  let rightHeap := Heap.write heap (swRightField p) (Heap.read heap (swLeftField p))
  let leftHeap := Heap.write rightHeap (swLeftField p) t.addr
  let nextHeap := Heap.write leftHeap (swControlField p) 1
  have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr p,
        valPtr (Ptr.mk (Heap.read heap (swRightField p)))] nextHeap valUnit final := by
    simpa [swSwingSpec, rightHeap, leftHeap, nextHeap] using hloop
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have hstore : heapOpCtx.get? "store" = some storeOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by rfl
  have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by rfl
  intro env base
  let block := schorrWaiteBlocks[4].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaiteSwing" env :: base),
    by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
        first
        | simpa [swRightField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swRightField p)
        | simpa [swLeftField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swLeftField p)
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := rightHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
    simpa [rightHeap, swLeftField, swRightField] using
      storeOp_step schorrWaiteCtx.blockCtx _ _ heap
      (swRightField p) (Heap.read heap (swLeftField p))
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := rightHeap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := leftHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run rightHeap) = _
    simpa [leftHeap, swLeftField] using storeOp_step schorrWaiteCtx.blockCtx _ _ rightHeap
      (swLeftField p) t.addr
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := leftHeap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run leftHeap) = _
    simpa [nextHeap, swControlField] using storeOp_step schorrWaiteCtx.blockCtx _ _ leftHeap
      (swControlField p) 1
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop'
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

private theorem schorrWaitePop_evaluates_values (heap final : Heap) (p t : Ptr)
    (hloop : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr (swPopSpec heap p t).2.1,
        valPtr (swPopSpec heap p t).2.2] (swPopSpec heap p t).1 valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePop" [valPtr p, valPtr t] heap valUnit final := by
  let nextHeap := Heap.write heap (swRightField p) t.addr
  have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr (Ptr.mk (Heap.read heap (swRightField p))),
        valPtr p] nextHeap valUnit final := by
    simpa [swPopSpec, nextHeap] using hloop
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have hstore : heapOpCtx.get? "store" = some storeOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hptrOfNat : heapOpCtx.get? "ptrOfNat" = some ptrOfNatOp := by rfl
  have hptrAddr : heapOpCtx.get? "ptrAddr" = some ptrAddrOp := by rfl
  intro env base
  let block := schorrWaiteBlocks[5].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaitePop" env :: base),
    by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
        simpa [swRightField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
          (swRightField p)
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
            Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
  · change Id.run ((Machine.step
      (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
    simpa [nextHeap, swRightField] using storeOp_step schorrWaiteCtx.blockCtx _ _ heap
      (swRightField p) t.addr
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop'
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := nextHeap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hstore, hptrAdd,
            hptrOfNat, hptrAddr, loadOp, storeOp, ptrAddOp, ptrOfNatOp,
            ptrAddrOp, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
            Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
            Scope.get?, Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

private theorem schorrWaitePopOrSwing_swing_evaluates_values (heap final : Heap)
    (p t : Ptr) (hclear : Heap.read heap (swControlField p) = 0)
    (hswing : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteSwing" [valPtr p, valPtr t] heap valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePopOrSwing" [valPtr p, valPtr t] heap valUnit final := by
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by rfl
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by rfl
  have hclear' : Heap.read heap ⟨p.addr + 3⟩ = 0 := by
    simpa [swControlField] using hclear
  intro env base
  let block := schorrWaiteBlocks[3].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaitePopOrSwing" env :: base),
    by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  iterate 22
    first
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
        simpa [swControlField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
          (swControlField p)
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock, Machine.enterInstrs,
            Machine.driveOp, hload, hptrAdd, heq, hite, hclear', swControlField,
            loadOp, ptrAddOp, Op.eq, Op.compare, Op.ite,
            Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
            Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
            Term.nat, Term.ite, termPtr, valPtr, valUnit, asPtr?]
        rfl
  apply EvalTriple.State.EvaluatesFrom.call_then hswing
  intro scope
  apply EvalTriple.State.EvaluatesFrom.step (middle := final)
  · simp [Machine.step, Machine.ofOption, Machine.resumeFrame, Machine.driveOp]
    rfl
  exact EvalTriple.State.EvaluatesFrom.return_to_call

private theorem schorrWaitePopOrSwing_pop_evaluates_values (heap final : Heap)
    (p t : Ptr) (hset : Heap.read heap (swControlField p) ≠ 0)
    (hpop : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePop" [valPtr p, valPtr t] heap valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePopOrSwing" [valPtr p, valPtr t] heap valUnit final := by
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by rfl
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by rfl
  have hset' : Heap.read heap ⟨p.addr + 3⟩ ≠ 0 := by
    simpa [swControlField] using hset
  intro env base
  let block := schorrWaiteBlocks[3].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaitePopOrSwing" env :: base),
    by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hpop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_through_done_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · change Id.run ((Machine.step
          (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
        simpa [swControlField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
          (swControlField p)
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hload, hptrAdd, heq, hite,
            hset', swControlField, loadOp, ptrAddOp, Op.eq, Op.compare, Op.ite,
            Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
            Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
            Term.nat, Term.ite, termPtr, valPtr, valUnit, asPtr?]
        rfl

private theorem schorrWaiteLoop_push_evaluates_values (heap final : Heap) (p t : Ptr)
    (htNonNull : t ≠ null) (htUnmarked : ¬swMarked heap t)
    (hpush : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePush" [valPtr p, valPtr t] heap valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr p, valPtr t] heap valUnit final := by
  have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by rfl
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by rfl
  have hpushBlock : schorrWaiteCtx.blockCtx.get? "schorrWaitePush" =
      some (schorrWaiteBlocks[2].2) := by rfl
  have htClear : Heap.read heap (swMarkField t) = 0 := by
    simpa [swMarked] using htUnmarked
  have htClear' : Heap.read heap ⟨t.addr + 2⟩ = 0 := by
    simpa [swMarkField] using htClear
  by_cases hpNull : p = null
  all_goals
    have hpush' := hpush
    simp only [hpNull] at hpush'
    intro env base
    let block := schorrWaiteBlocks[1].2
    refine ⟨block, Machine.enterInstrs block.instrs block.result
      (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaiteLoop" env :: base),
      by rfl, ?_, ?_⟩
    · simp [Machine.enterBlock, block]
    dsimp [block, schorrWaiteBlocks]
    iterate 36
      first
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
          simpa [swMarkField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swMarkField t)
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · set_option linter.unusedSimpArgs false in
            simp [Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hptrIsNull, hptrAdd,
              hload, heq, hite, hpushBlock, hpNull, htNonNull, htClear', ptrIsNullOp,
              ptrAddOp, loadOp, Op.eq, Op.compare, Op.ite, Op.effectful,
              Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
              Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
              Term.ite, termPtr, termUnit, valPtr, valUnit, asPtr?]
          rfl
    apply EvalTriple.State.EvaluatesFrom.call_then hpush'
    intro scope
    iterate 3
      apply EvalTriple.State.EvaluatesFrom.step (middle := final)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
          Machine.driveOp]
        rfl
    exact EvalTriple.State.EvaluatesFrom.return_to_call

private theorem schorrWaiteLoop_continue_evaluates_values (heap final : Heap) (p t : Ptr)
    (hpNonNull : p ≠ null) (htDone : swChildDone heap t)
    (hnext : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaitePopOrSwing" [valPtr p, valPtr t] heap valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr p, valPtr t] heap valUnit final := by
  have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by rfl
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by rfl
  have hnextBlock : schorrWaiteCtx.blockCtx.get? "schorrWaitePopOrSwing" =
      some (schorrWaiteBlocks[3].2) := by rfl
  by_cases htNull : t = null
  · have hnext' := hnext
    simp only [htNull] at hnext'
    intro env base
    let block := schorrWaiteBlocks[1].2
    refine ⟨block, Machine.enterInstrs block.instrs block.result
      (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaiteLoop" env :: base),
      by rfl, ?_, ?_⟩
    · simp [Machine.enterBlock, block]
    dsimp [block, schorrWaiteBlocks]
    iterate 33
      first
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
          simpa [swMarkField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swMarkField t)
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · set_option linter.unusedSimpArgs false in
            simp [Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hptrIsNull, hptrAdd,
              hload, heq, hite, hnextBlock, hpNonNull, htNull, ptrIsNullOp, ptrAddOp, loadOp,
              Op.eq, Op.compare, Op.ite, Op.effectful, Op.Body.collect,
              Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
              Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr, termUnit,
              valPtr, valUnit, asPtr?]
          rfl
    apply EvalTriple.State.EvaluatesFrom.call_then hnext'
    intro scope
    iterate 2
      apply EvalTriple.State.EvaluatesFrom.step (middle := final)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
          Machine.driveOp]
        rfl
    exact EvalTriple.State.EvaluatesFrom.return_to_call
  · have htMarked : swMarked heap t := htDone.resolve_left htNull
    have htSet' : Heap.read heap ⟨t.addr + 2⟩ ≠ 0 := by
      simpa [swMarked, swMarkField] using htMarked
    intro env base
    let block := schorrWaiteBlocks[1].2
    refine ⟨block, Machine.enterInstrs block.instrs block.result
      (block.entryEnv [valPtr p, valPtr t]) (.call "schorrWaiteLoop" env :: base),
      by rfl, ?_, ?_⟩
    · simp [Machine.enterBlock, block]
    dsimp [block, schorrWaiteBlocks]
    iterate 36
      first
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
          simpa [swMarkField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swMarkField t)
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · set_option linter.unusedSimpArgs false in
            simp [Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hptrIsNull, hptrAdd,
              hload, heq, hite, hnextBlock, hpNonNull, htNull, htSet', ptrIsNullOp,
              ptrAddOp, loadOp, Op.eq, Op.compare, Op.ite, Op.effectful,
              Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
              Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
              Term.ite, termPtr, termUnit, valPtr, valUnit, asPtr?]
          rfl
    apply EvalTriple.State.EvaluatesFrom.call_then hnext
    intro scope
    iterate 3
      apply EvalTriple.State.EvaluatesFrom.step (middle := final)
      · simp [Machine.step, Machine.ofOption, Machine.resumeFrame,
          Machine.driveOp]
        rfl
    exact EvalTriple.State.EvaluatesFrom.return_to_call

private theorem schorrWaiteLoop_done_evaluates_values (heap : Heap) (t : Ptr)
    (htDone : t = null ∨ (t ≠ null ∧ swMarked heap t)) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr null, valPtr t] heap valUnit heap := by
  have hptrIsNull : heapOpCtx.get? "ptrIsNull" = some ptrIsNullOp := by rfl
  have hptrAdd : heapOpCtx.get? "ptrAdd" = some ptrAddOp := by rfl
  have hload : heapOpCtx.get? "load" = some loadOp := by rfl
  have heq : heapOpCtx.get? "eq" = some (Op.eq (M := StateM Heap)) := by rfl
  have hite : heapOpCtx.get? "ite" = some (Op.ite (M := StateM Heap)) := by rfl
  rcases htDone with rfl | ⟨htNonNull, htMarked⟩
  · intro env base
    let block := schorrWaiteBlocks[1].2
    refine ⟨block, Machine.enterInstrs block.instrs block.result
      (block.entryEnv [valPtr null, valPtr null]) (.call "schorrWaiteLoop" env :: base),
      by rfl, ?_, ?_⟩
    · simp [Machine.enterBlock, block]
    dsimp [block, schorrWaiteBlocks]
    repeat
      first
      | exact EvalTriple.State.EvaluatesFrom.done
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
          simpa [swMarkField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swMarkField null)
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · set_option linter.unusedSimpArgs false in
            simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
              Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hptrIsNull, hptrAdd,
              hload, heq, hite, ptrIsNullOp, ptrAddOp, loadOp, Op.eq,
              Op.compare, Op.ite, Op.effectful, Op.Body.collect, Op.Arg.ofTerms,
              Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv,
              Scope.get?, Term.nat, Term.ite, termPtr, termUnit, valPtr, valUnit,
              asPtr?]
          rfl
  · have htSet : Heap.read heap (swMarkField t) ≠ 0 := htMarked
    have htSet' : Heap.read heap ⟨t.addr + 2⟩ ≠ 0 := by
      simpa [swMarkField] using htSet
    intro env base
    let block := schorrWaiteBlocks[1].2
    refine ⟨block, Machine.enterInstrs block.instrs block.result
      (block.entryEnv [valPtr null, valPtr t]) (.call "schorrWaiteLoop" env :: base),
      by rfl, ?_, ?_⟩
    · simp [Machine.enterBlock, block]
    dsimp [block, schorrWaiteBlocks]
    repeat
      first
      | exact EvalTriple.State.EvaluatesFrom.done
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · change Id.run ((Machine.step
            (Machine.stateCtx heapCtx heapOpCtx schorrWaiteCtx.blockCtx) _).run heap) = _
          simpa [swMarkField] using loadOp_step schorrWaiteCtx.blockCtx _ _ heap
            (swMarkField t)
      | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
        · set_option linter.unusedSimpArgs false in
            simp [block, schorrWaiteCtx, mkCtx, schorrWaiteBlocks, checkedBlocks,
              Machine.step, Machine.evalTerm, Machine.applyValue,
              Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
              Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
              Machine.enterInstrs, Machine.driveOp, hptrIsNull, hptrAdd,
              hload, heq, hite, htNonNull, htSet', ptrIsNullOp, ptrAddOp, loadOp,
              Op.eq, Op.compare, Op.ite, Op.effectful, Op.Body.collect,
              Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals, Op.Body.eager, Op.fixed,
              Block.entryEnv, Scope.get?, Term.nat, Term.ite, termPtr, termUnit,
              valPtr, valUnit, asPtr?]
          rfl

theorem swPushSpec_target {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {stack : List SWFrame} (inv : SWInvariant graph heap p t stack)
    (htNonNull : t ≠ null) (htUnmarked : ¬swMarked heap t) :
    (swPushSpec heap p t).2.2 = swOriginalLeft initial t := by
  have htMem := (inv.target_valid.resolve_left htNonNull).1
  have htNotStack : t ∉ swStackNodes stack := by
    intro hmem
    exact htUnmarked (inv.stack_marked t hmem)
  have hleft := (inv.restored t htMem htNotStack).1
  simp [swPushSpec, swOriginalLeft, hleft]

@[simp] theorem swPushSpec_p (heap : Heap) (p t : Ptr) :
    (swPushSpec heap p t).2.1 = t := by
  simp [swPushSpec]

theorem swSwingSpec_target {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = false) :
    (swSwingSpec heap p t).2.2 = swOriginalRight initial p := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hrev := inv.reversed
  simp only [SWReversed] at hrev
  simp [hphase] at hrev
  simp [swSwingSpec, swOriginalRight, hp, hrev.1.2.1]

@[simp] theorem swSwingSpec_p (heap : Heap) (p t : Ptr) :
    (swSwingSpec heap p t).2.1 = p := by
  simp [swSwingSpec]

theorem swPopSpec_parent {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {frame : SWFrame} {rest : List SWFrame}
    (inv : SWInvariant graph heap p t (frame :: rest))
    (hphase : frame.rightPhase = true) :
    (swPopSpec heap p t).2.1 = swStackHead rest := by
  have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
  have hrev := inv.reversed
  simp only [SWReversed] at hrev
  simp [hphase] at hrev
  simp [swPopSpec, hp, hrev.1.2.1]

@[simp] theorem swPopSpec_t (heap : Heap) (p t : Ptr) :
    (swPopSpec heap p t).2.2 = p := by
  simp [swPopSpec]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
theorem schorrWaiteLoop_graph {initial heap : Heap} {graph : SWGraph initial}
    {p t : Ptr} {stack : List SWFrame} (inv : SWInvariant graph heap p t stack) :
    ∃ final : Heap,
      EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
        "schorrWaiteLoop" [valPtr p, valPtr t] heap valUnit final ∧
      SWPost graph final := by
  cases stack with
  | nil =>
      have hp : p = null := by simpa [swStackHead] using inv.p_eq
      subst p
      by_cases htNull : t = null
      · subst t
        exact ⟨heap, schorrWaiteLoop_done_evaluates_values heap null (Or.inl rfl),
          swInvariant_finished inv (Or.inl rfl)⟩
      · by_cases htMarked : swMarked heap t
        · exact ⟨heap,
            schorrWaiteLoop_done_evaluates_values heap t (Or.inr ⟨htNull, htMarked⟩),
            swInvariant_finished inv (Or.inr htMarked)⟩
        · let nextInv := swPush_preserves_invariant inv htNull htMarked
          obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
          have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
              schorrWaiteCtx.blockCtx "schorrWaiteLoop"
              [valPtr (swPushSpec heap null t).2.1,
                valPtr (swPushSpec heap null t).2.2]
              (swPushSpec heap null t).1 valUnit final := by
            simpa only [swPushSpec_p, swPushSpec_target inv htNull htMarked] using hloop
          have hpush := schorrWaitePush_evaluates_values heap final null t hloop'
          exact ⟨final,
            schorrWaiteLoop_push_evaluates_values heap final null t htNull htMarked hpush,
            hpost⟩
  | cons frame rest =>
      have hpNonNull : p ≠ null := by
        apply SWReachable.ne_null
        apply inv.stack_reachable p
        simp [swStackNodes, swStackHead, inv.p_eq]
      by_cases htNull : t = null
      · have htDone : swChildDone heap t := Or.inl htNull
        cases hphase : frame.rightPhase with
        | false =>
            let nextInv := swSwing_preserves_invariant inv hphase htDone
            obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
            have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
                schorrWaiteCtx.blockCtx "schorrWaiteLoop"
                [valPtr (swSwingSpec heap p t).2.1,
                  valPtr (swSwingSpec heap p t).2.2]
                (swSwingSpec heap p t).1 valUnit final := by
              simpa only [swSwingSpec_p, swSwingSpec_target inv hphase] using hloop
            have hswing := schorrWaiteSwing_evaluates_values heap final p t hloop'
            have hrev := inv.reversed
            simp only [SWReversed] at hrev
            simp [hphase] at hrev
            have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
            have hnext := schorrWaitePopOrSwing_swing_evaluates_values heap final p t
              (by simpa [hp] using hrev.1.2.2) hswing
            exact ⟨final,
              schorrWaiteLoop_continue_evaluates_values heap final p t hpNonNull htDone hnext,
              hpost⟩
        | true =>
            let nextInv := swPop_preserves_invariant inv hphase htDone
            obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
            have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
                schorrWaiteCtx.blockCtx "schorrWaiteLoop"
                [valPtr (swPopSpec heap p t).2.1, valPtr (swPopSpec heap p t).2.2]
                (swPopSpec heap p t).1 valUnit final := by
              simpa only [swPopSpec_t, swPopSpec_parent inv hphase] using hloop
            have hpop := schorrWaitePop_evaluates_values heap final p t hloop'
            have hrev := inv.reversed
            simp only [SWReversed] at hrev
            simp [hphase] at hrev
            have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
            have hnext := schorrWaitePopOrSwing_pop_evaluates_values heap final p t
              (by simpa [hp] using hrev.1.2.2.1) hpop
            exact ⟨final,
              schorrWaiteLoop_continue_evaluates_values heap final p t hpNonNull htDone hnext,
              hpost⟩
      · by_cases htMarked : swMarked heap t
        · have htDone : swChildDone heap t := Or.inr htMarked
          cases hphase : frame.rightPhase with
          | false =>
              let nextInv := swSwing_preserves_invariant inv hphase htDone
              obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
              have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
                  schorrWaiteCtx.blockCtx "schorrWaiteLoop"
                  [valPtr (swSwingSpec heap p t).2.1,
                    valPtr (swSwingSpec heap p t).2.2]
                  (swSwingSpec heap p t).1 valUnit final := by
                simpa only [swSwingSpec_p, swSwingSpec_target inv hphase] using hloop
              have hswing := schorrWaiteSwing_evaluates_values heap final p t hloop'
              have hrev := inv.reversed
              simp only [SWReversed] at hrev
              simp [hphase] at hrev
              have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
              have hnext := schorrWaitePopOrSwing_swing_evaluates_values heap final p t
                (by simpa [hp] using hrev.1.2.2) hswing
              exact ⟨final,
                schorrWaiteLoop_continue_evaluates_values heap final p t hpNonNull htDone hnext,
                hpost⟩
          | true =>
              let nextInv := swPop_preserves_invariant inv hphase htDone
              obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
              have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
                  schorrWaiteCtx.blockCtx "schorrWaiteLoop"
                  [valPtr (swPopSpec heap p t).2.1, valPtr (swPopSpec heap p t).2.2]
                  (swPopSpec heap p t).1 valUnit final := by
                simpa only [swPopSpec_t, swPopSpec_parent inv hphase] using hloop
              have hpop := schorrWaitePop_evaluates_values heap final p t hloop'
              have hrev := inv.reversed
              simp only [SWReversed] at hrev
              simp [hphase] at hrev
              have hp : p = frame.node := by simpa [swStackHead] using inv.p_eq
              have hnext := schorrWaitePopOrSwing_pop_evaluates_values heap final p t
                (by simpa [hp] using hrev.1.2.2.1) hpop
              exact ⟨final,
                schorrWaiteLoop_continue_evaluates_values heap final p t hpNonNull htDone hnext,
                hpost⟩
        · let nextInv := swPush_preserves_invariant inv htNull htMarked
          obtain ⟨final, hloop, hpost⟩ := schorrWaiteLoop_graph nextInv
          have hloop' : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx
              schorrWaiteCtx.blockCtx "schorrWaiteLoop"
              [valPtr (swPushSpec heap p t).2.1, valPtr (swPushSpec heap p t).2.2]
              (swPushSpec heap p t).1 valUnit final := by
            simpa only [swPushSpec_p, swPushSpec_target inv htNull htMarked] using hloop
          have hpush := schorrWaitePush_evaluates_values heap final p t hloop'
          exact ⟨final,
            schorrWaiteLoop_push_evaluates_values heap final p t htNull htMarked hpush,
            hpost⟩
termination_by swMeasure graph heap stack
decreasing_by
  all_goals subst stack
  all_goals try subst p
  · exact swPush_measure_decreases inv htNull htMarked
  · exact swSwing_measure_decreases inv hphase
  · exact swPop_measure_decreases inv hphase
  · exact swSwing_measure_decreases inv hphase
  · exact swPop_measure_decreases inv hphase
  · exact swPush_measure_decreases inv htNull htMarked

private theorem schorrWaite_evaluates_values (heap final : Heap) (root : Ptr)
    (hloop : EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaiteLoop" [valPtr null, valPtr root] heap valUnit final) :
    EvalTriple.State.EvaluatesCallValues heapCtx heapOpCtx schorrWaiteCtx.blockCtx
      "schorrWaite" [valPtr root] heap valUnit final := by
  have hloopBlock : schorrWaiteCtx.blockCtx.get? "schorrWaiteLoop" =
      some (schorrWaiteBlocks[1].2) := by rfl
  intro env base
  let block := schorrWaiteBlocks[0].2
  refine ⟨block, Machine.enterInstrs block.instrs block.result
    (block.entryEnv [valPtr root]) (.call "schorrWaite" env :: base), by rfl, ?_, ?_⟩
  · simp [Machine.enterBlock, block]
  dsimp [block, schorrWaiteBlocks]
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hloop
      intro scope
      exact EvalTriple.State.EvaluatesFrom.return_to_call
    | apply EvalTriple.State.EvaluatesFrom.step (middle := heap)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, hloopBlock, Op.effectful,
            Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals, Op.ofVals,
            Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?, Term.nat,
            termPtr, valPtr, valUnit, asPtr?]
        rfl

theorem schorrWaite_evaluates (initial : Heap) (graph : SWGraph initial) :
    ∃ final : Heap,
      EvalTriple.State.EvaluatesCall heapCtx heapOpCtx schorrWaiteCtx.blockCtx
        "schorrWaite" [termPtr graph.root.addr] initial valUnit final ∧
      SWPost graph final := by
  obtain ⟨final, hloop, hpost⟩ :=
    schorrWaiteLoop_graph (swInvariant_initial graph)
  have hcall := schorrWaite_evaluates_values initial final graph.root hloop
  refine ⟨final, ?_, hpost⟩
  unfold EvalTriple.State.EvaluatesCall
  apply EvalTriple.State.EvaluatesTo.of_evaluatesFrom
  repeat
    first
    | apply EvalTriple.State.EvaluatesFrom.call_then hcall
      intro scope
      exact EvalTriple.State.EvaluatesFrom.done
    | apply EvalTriple.State.EvaluatesFrom.step (middle := initial)
      · set_option linter.unusedSimpArgs false in
          simp [Machine.step, Machine.evalTerm, Machine.applyValue,
            Machine.driveSelectedOp, Machine.ofOption, Machine.evalTermImmediate,
            Machine.applyValueImmediate, Machine.resumeFrame, Machine.enterBlock,
            Machine.enterInstrs, Machine.driveOp, Machine.start,
            Op.effectful, Op.Body.collect, Op.Arg.ofTerms, Op.Arg.ofVals,
            Op.ofVals, Op.Body.eager, Op.fixed, Block.entryEnv, Scope.get?,
            Term.nat, termPtr, valPtr, valUnit, asPtr?]
        rfl

/-- The embedded Schorr-Waite program marks exactly the reachable nodes and restores both links.
The precondition snapshots the four owned fields of every graph node; the exact initial heap is not
part of the public contract. -/
@[zspec] theorem SchorrWaiteAlgorithm (initial : Heap) (graph : SWGraph initial) :
    Zag.EvaluatesCall schorrWaiteStateCtx
      "schorrWaite" [termPtr graph.root.addr]
      (HProp.toAssertion (swGraphFootprint initial graph.nodes))
      (Std.Do.PostCond.noThrow fun result final =>
        ⌜result = valUnit ∧ SWPost graph final⌝) := by
  let PreHeap := { heap : Heap // (swGraphFootprint initial graph.nodes).holds heap }
  change EvalTriple.EvaluatesFrom schorrWaiteStateCtx
    (Machine.start [] (.call "schorrWaite" [termPtr graph.root.addr])) [] _ _
  apply EvalTriple.Steps.split (cases := fun hh : PreHeap => EvalTriple.Singleton.statePre hh.1)
  · intro s hs
    refine ⟨⟨s, by simpa [HProp.toAssertion] using hs⟩, ?_⟩
    simp [EvalTriple.Singleton.statePre]
  · intro hh
    let graphHeap := swGraphRebase graph hh.2
    obtain ⟨final, heval, hpost⟩ := schorrWaite_evaluates hh.1 graphHeap
    have hex : EvalTriple.State.EvaluatesCall heapCtx heapOpCtx schorrWaiteCtx.blockCtx
        "schorrWaite" [termPtr graph.root.addr] hh.1 valUnit final := by
      simpa [graphHeap, swGraphRebase] using heval
    have hpost' : SWPost graph final := SWPost.of_footprint graph hh.2 hpost
    refine EvalTriple.EvaluatesFrom.consequence hex .rfl ?_
    simp [EvalTriple.Singleton.statePost, Std.Do.PostCond.entails, hpost']

def schorrWaiteSample : Heap :=
  { next := 9
    cells := [(1, 5), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0)] }

def runSchorrWaite (heap : Heap) (root : Ptr) : Option Heap :=
  match (Machine.evalFuel schorrWaiteCtx 10000 []
      (.call "schorrWaite" [termPtr root.addr])).run heap with
  | (some _, final) => some final
  | (none, _) => none

theorem schorrWaiteSample_run :
    (runSchorrWaite schorrWaiteSample ⟨1⟩).map (fun heap =>
      [Heap.read heap ⟨1⟩, Heap.read heap ⟨2⟩, Heap.read heap ⟨3⟩,
        Heap.read heap ⟨5⟩, Heap.read heap ⟨6⟩, Heap.read heap ⟨7⟩]) =
      some [5, 0, 1, 0, 0, 1] := by
  native_decide

end Zag.Test.Autocorres.Examples
