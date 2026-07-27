import Lang.SSA
import Lang.Simple.Corres

/-!
  # HL — AutoCorres HeapLift

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>
  (`HeapLift.thy`, `heap_lift.ML`). Line numbers against l4v `master`.

  * `L2Tcorres st A C = corresXF st (λr _. r) (λr _. r) ⊤ A C` — HeapLift.thy:17
    (note: unlike `L2corres`, the return and exception extractors are the
    identity — HL changes only the *state*, never the value shape)
  * `abs_guard st A C ≡ ∀s. A (st s) ⟶ C s` — HeapLift.thy:30
  * `abs_expr st P A C ≡ ∀s. P (st s) ⟶ C s = A (st s)` — HeapLift.thy:31
  * `abs_modifies st P A C ≡ ∀s. P (st s) ⟶ st (C s) = A (st s)` — HeapLift.thy:32
  * `struct_rewrite_guard/expr/modifies` — HeapLift.thy:39–41
  * entry point `HeapLift.translate` — heap_lift.ML:617

  Zag: concrete `heap.load` / `heap.store` on a byte/`Word` heap become
  `heap.w.get` / `heap.w.set` on the typed `HeapW`, guarded by `heap.w.valid`
  (AC's `c_guard`/validity obligation, discharged by `abs_guard`).
  Optional on the C0 path (no heap in Basics), matching AC's `skip_heap_abs`
  (autocorres.ML:596). Full `valRel` heap correspondence is still open.
-/

namespace Lang.Simple.Lift.HL

open Zag
open Zag.Lang.SSA

/--
  AC `L2Tcorres st A C = corresXF st (λr _. r) (λr _. r) ⊤ A C`
  — HeapLift.thy:17. Identity return/exception extractors: HL abstracts the
  state only, so the abstract body must return the *same* value as the
  concrete one under the state abstraction `st`.
-/
def L2Tcorres {CS AS V : Type}
    (st : CS → AS)
    (A : AS → Corres.XFResult V AS) (C : CS → Corres.XFResult V CS) : Prop :=
  Corres.CorresXF st (fun v _ => v) (fun v _ => v) (fun _ => True) A C

/--
  The extractors really are the identity — HL abstracts the *state*, so the
  abstract body returns the very same value as the concrete one. This is what
  distinguishes `L2Tcorres` from `L2corres` (which has non-trivial `ret_xf`).
-/
theorem L2Tcorres_value_unchanged {CS AS V : Type}
    {st : CS → AS} {A : AS → Corres.XFResult V AS} {C : CS → Corres.XFResult V CS}
    (h : L2Tcorres st A C) {s : CS} (hA : (A (st s)).isSome)
    {v : V} {t : CS} (hC : C s = some (.inr v, t)) :
    A (st s) = some (.inr v, st t) :=
  (h s trivial hA).2 _ t hC

/--
  AC's struct-rewrite stage (`struct_rewrite_expr`/`_guard`/`_modifies`,
  HeapLift.thy:39–41) is **not** ported. This detects the struct-heap
  primitives it would be responsible for, so `apply` can refuse rather than
  silently drop them.
-/
partial def mentionsStructHeap {p : PrimitiveCtx} : SSAExpr p → Bool
  | .ret v => val v
  | .let_ _ v n => val v || mentionsStructHeap n
  | .seq a b => mentionsStructHeap a || mentionsStructHeap b
  | .ite c t e => val c || mentionsStructHeap t || mentionsStructHeap e
  | .yield vs => vs.any val
where
  val : SSAValue p → Bool
    | .raw (.primFunc "heap.load.struct") => true
    | .raw (.primFunc "heap.store.struct") => true
    | .call f as => val f || as.any val
    | .struct _ fs => fs.any val
    | .field _ _ v => val v
    | .op _ as => as.any val
    | .block _ b => mentionsStructHeap b
    | .loopBody _ _ init _ b => init.any val || mentionsStructHeap b
    | _ => false

/--
  Rewrite heap ops — the `abs_expr` / `abs_modifies` side of AC HeapLift
  (HeapLift.thy:31,32), with the validity binding standing for `abs_guard`
  (HeapLift.thy:30):

  * `heap.load` → `heap.w.valid` then `heap.w.get`  (`abs_expr`)
  * `heap.store` → `heap.w.valid` then `heap.w.set` (`abs_modifies`)

  Structural, mirroring `heap_lift.ML:617`; the full `valRel` between the
  byte heap and the typed heap is open.
-/
partial def rewriteHeap {p : PrimitiveCtx} : SSAExpr p → Option (SSAExpr p)
  | .ret v => do
      let v' ← rewriteVal v
      some (.ret v')
  | .let_ n v b => do
      let v' ← rewriteVal v
      let b' ← rewriteHeap b
      some (.let_ n v' b')
  | .seq a b => do
      let a' ← rewriteHeap a
      let b' ← rewriteHeap b
      some (.seq a' b')
  | .ite c t e => do
      let c' ← rewriteVal c
      let t' ← rewriteHeap t
      let e' ← rewriteHeap e
      some (.ite c' t' e')
  | .yield vs => do
      let vs' ← vs.mapM rewriteVal
      some (.yield vs')
where
  /--
    `heap.w.valid` is binary (`["HeapW","Ptr"]`, `ABI.heapWValidFunc`), so the
    guard takes only the heap and pointer — **not** `heap.store`'s value
    argument. Passing all three would emit an ill-typed guard.
  -/
  validArgs : List (SSAValue p) → Option (List (SSAValue p))
    | h :: ptr :: _ => some [h, ptr]
    | _ => none
  rewriteVal : SSAValue p → Option (SSAValue p)
    | .call (.primFunc "heap.load") args => do
        let g ← validArgs args
        some (.block (.prim "Word") <|
          .let_ "__hl_valid" (.call (.primFunc "heap.w.valid") g) <|
          .ret (.call (.primFunc "heap.w.get") args))
    | .call (.primFunc "heap.store") args => do
        let g ← validArgs args
        some (.block (.prim "Heap") <|
          .let_ "__hl_valid" (.call (.primFunc "heap.w.valid") g) <|
          .ret (.call (.primFunc "heap.w.set") args))
    | .call f as => do
        let f' ← rewriteVal f
        let as' ← as.mapM rewriteVal
        some (.call f' as')
    | .struct tys fs => do
        let fs' ← fs.mapM rewriteVal
        some (.struct tys fs')
    | .field tys i v => do
        let v' ← rewriteVal v
        some (.field tys i v')
    | .op n as => do
        let as' ← as.mapM rewriteVal
        some (.op n as')
    | .block ty b => do
        let b' ← rewriteHeap b
        some (.block ty b')
    | v => some v

/--
  AC `HeapLift.translate` — heap_lift.ML:617.
  Refuses bodies needing the unported struct-rewrite stage (HeapLift.thy:39–41).
-/
def apply {p : PrimitiveCtx} (e : SSAExpr p) : Option (SSAExpr p) :=
  if mentionsStructHeap e then none else rewriteHeap e

end Lang.Simple.Lift.HL
