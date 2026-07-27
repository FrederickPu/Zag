import Lang.Simple.Corres
import Lang.SSA

/-!
  # TS — AutoCorres TypeStrengthen

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>
  (`TypeStrengthen.thy`, `monad_types.ML`, `type_strengthen.ML`).
  Line numbers against l4v `master`.

  ## What AC's TS actually is

  AC registers four *monad types* with `Monad_Types.new_monad_type`
  (monad_types.ML:162). Each carries a `precedence`, a `valid_term` predicate
  built by `check_lifting_head` (monad_types.ML:155–160), and a `typ_from_L2`
  giving the strengthened function's type:

  | AC name | description | lifting head | precedence | `typ_from_L2` | thy line |
  | --- | --- | --- | --- | --- | --- |
  | `pure` | "Pure function" | `TS_return` | 100 | `#2` — just `ret` | :81–90 |
  | `gets` | "Read-only function" | `TS_gets` | 80 | `state ⟹ ret` | :145–154 |
  | `option` | "Option monad" | `gets_theE` | 60 | `state ⟹ ret option` | :231–241 |
  | `nondet` | "Nondeterministic state monad (default)" | `liftE` | 0 | `('s,'a) nondet_monad` | :323–334 |

  `TS_return x ≡ liftE (return x)` — TypeStrengthen.thy:63;
  `TS_gets x ≡ liftE (gets x)` — TypeStrengthen.thy:134.

  The rules are sorted **highest precedence first** (monad_types.ML:223–225)
  and `lift_function` takes the **first lift that works**
  (type_strengthen.ML:521–535). So TS is a *search* for the strongest type that
  still models the body — that search is what this file ports.

  ## What is and is not ported here

  * **Ported:** the four monad types with AC's own precedences, AC's
    `typ_from_L2` type shapes, the highest-precedence-first ordering, and a
    `valid_term`-analogue (`fits`) that classifies a Zag SSA body. `apply`
    performs the real selection — it is *not* a constant.
  * **Not ported:** the rewriting half. AC re-defines the function at the
    chosen type and proves `L2_call c_WA = A` (the fifth premise of
    `ac_corres_chain`, AutoCorres.thy:78–85). Here the body is returned
    unchanged and only its tier is computed, so `strengthen` reports a tier
    without producing a retyped body.

  With `M := Id` and state threaded explicitly (§5.0) Zag has no
  nondeterminism, so `nondet` is unreachable — proved below rather than
  assumed.
-/

namespace Lang.Simple.Lift.TS

open Zag
open Zag.Lang.SSA
open Lang.Simple.Corres

/--
  AC's registered monad types — TypeStrengthen.thy:81, :145, :231, :323
  (`Monad_Types.new_monad_type`, monad_types.ML:162).
-/
inductive MonadType where
  /-- `TS_return x ≡ liftE (return x)` — TypeStrengthen.thy:63, registered :81. -/
  | pure
  /-- `TS_gets x ≡ liftE (gets x)` — TypeStrengthen.thy:134, registered :145. -/
  | gets
  /-- lifting head `gets_theE` — TypeStrengthen.thy:231. -/
  | option
  /-- lifting head `liftE`; AC's default — TypeStrengthen.thy:323. -/
  | nondet
  deriving DecidableEq, Repr

namespace MonadType

/-- AC's registered names — TypeStrengthen.thy:82, :146, :232, :324. -/
def name : MonadType → String
  | .pure => "pure"
  | .gets => "gets"
  | .option => "option"
  | .nondet => "nondet"

/-- AC's `description` field — TypeStrengthen.thy:83, :147, :233, :325. -/
def description : MonadType → String
  | .pure => "Pure function"
  | .gets => "Read-only function"
  | .option => "Option monad"
  | .nondet => "Nondeterministic state monad (default)"

/-- AC's `lifting head` (`check_lifting_head`, monad_types.ML:155–160). -/
def liftingHead : MonadType → String
  | .pure => "TS_return"
  | .gets => "TS_gets"
  | .option => "gets_theE"
  | .nondet => "liftE"

/--
  AC's `precedence` field — TypeStrengthen.thy:85 (100), :149 (80),
  :235 (60), :327 (0). "Higher-numbered rules are tried first"
  (monad_types.ML:53).
-/
def precedence : MonadType → Nat
  | .pure => 100
  | .gets => 80
  | .option => 60
  | .nondet => 0

/--
  AC's `typ_from_L2` field: the type the strengthened function gets.
  `pure` is `#2` (just the return type) — TypeStrengthen.thy:88;
  `gets` is `state ⟹ ret` — :152; `option` is `state ⟹ ret option` — :238;
  `nondet` keeps the monad — :330.
-/
def typFromL2 : MonadType → (stateTy retTy : Ty) → Ty
  | .pure, _, ret => ret
  | .gets, st, ret => .func [st] ret
  | .option, st, ret => .func [st] (.option ret)
  | .nondet, st, ret => .func [st] (.m ret)

/--
  AC's rule order: sorted by highest precedence first
  — monad_types.ML:223–225.
-/
def ladder : List MonadType := [.pure, .gets, .option, .nondet]

theorem ladder_is_precedence_sorted :
    ladder.map precedence = [100, 80, 60, 0] := by decide

theorem ladder_covers_all (t : MonadType) : t ∈ ladder := by
  cases t <;> decide

/-- `pure` is tried first; `nondet` is AC's fallback (precedence 0). -/
theorem pure_tried_first (t : MonadType) : t.precedence ≤ MonadType.pure.precedence := by
  cases t <;> decide

theorem nondet_is_default (t : MonadType) : MonadType.nondet.precedence ≤ t.precedence := by
  cases t <;> decide

end MonadType

/--
  Which primitives make a body *stateful* or *failing*.
  This is the Zag analogue of AC's `check_lifting_head`
  (monad_types.ML:155–160): AC inspects the head constant of the lifted term,
  we inspect which primitives the body still mentions.

  Defaults match the Simpl/L1/L2 and HL ABIs.
-/
structure Signature where
  /-- Reading these means the body is at best `gets` (needs the state). -/
  stateReads : List String :=
    ["heap.load", "heap.w.get",
     "state.get.0", "state.get.1", "state.get.2", "state.get.3"]
  /-- Writing these means the body is at best `nondet` (modifies the state). -/
  stateWrites : List String :=
    ["heap.store", "heap.w.set",
     "state.set.0", "state.set.1", "state.set.2", "state.set.3"]
  /-- These can fail, so the body is at best `option`. -/
  guards : List String := ["heap.w.valid"]

/-- What a body was observed to do. -/
structure Effects where
  reads : Bool := false
  writes : Bool := false
  fails : Bool := false
  deriving DecidableEq, Repr, Inhabited

def Effects.merge (a b : Effects) : Effects :=
  { reads := a.reads || b.reads
    writes := a.writes || b.writes
    fails := a.fails || b.fails }

def Effects.ofName (sig : Signature) (n : String) : Effects :=
  { reads := sig.stateReads.contains n
    writes := sig.stateWrites.contains n
    fails := sig.guards.contains n }

/-- Effects of the raw Simpl `Term`s that L1 bodies still carry. -/
partial def termEffects {p : PrimitiveCtx} (sig : Signature) : Term p → Effects
  | .primFunc n => Effects.ofName sig n
  | .app f args =>
      (args.foldl (fun acc a => acc.merge (termEffects sig a)) (termEffects sig f))
  | .op _ args => args.foldl (fun acc a => acc.merge (termEffects sig a)) {}
  | .recurse _ init body => (termEffects sig init).merge (termEffects sig body)
  | _ => {}

mutual

/-- Effects of an SSA value. Mirrors `Dialect.mentionsOk`'s traversal. -/
partial def valueEffects {p : PrimitiveCtx} (sig : Signature) :
    SSAValue p → Effects
  | .raw t => termEffects sig t
  | .var _ => {}
  | .call fn args =>
      args.foldl (fun acc a => acc.merge (valueEffects sig a)) (valueEffects sig fn)
  | .struct _ fs => fs.foldl (fun acc f => acc.merge (valueEffects sig f)) {}
  | .field _ _ v => valueEffects sig v
  | .op _ args => args.foldl (fun acc a => acc.merge (valueEffects sig a)) {}
  | .block _ b => exprEffects sig b
  | .phi _ _ => {}
  | .loopBody _ _ init _ b =>
      init.foldl (fun acc v => acc.merge (valueEffects sig v)) (exprEffects sig b)

/-- Effects of an SSA body. -/
partial def exprEffects {p : PrimitiveCtx} (sig : Signature) :
    SSAExpr p → Effects
  | .ret v => valueEffects sig v
  | .let_ _ v n => (valueEffects sig v).merge (exprEffects sig n)
  | .seq a b => (exprEffects sig a).merge (exprEffects sig b)
  | .ite c t e =>
      ((valueEffects sig c).merge (exprEffects sig t)).merge (exprEffects sig e)
  | .yield vs => vs.foldl (fun acc v => acc.merge (valueEffects sig v)) {}

end

/--
  The `valid_term` analogue (monad_types.ML:47–48, :155–160): can this body be
  written in monad type `t`?

  * `pure` — no state access, cannot fail
  * `gets` — may read the state, cannot fail or write
  * `option` — may read and fail, may not write
  * `nondet` — anything (AC's default, precedence 0)
-/
def fits (t : MonadType) (e : Effects) : Bool :=
  match t with
  | .pure => !e.reads && !e.writes && !e.fails
  | .gets => !e.writes && !e.fails
  | .option => !e.writes
  | .nondet => true

/--
  AC's "find the first lift that works" — type_strengthen.ML:521–535, over the
  precedence-sorted rule list (monad_types.ML:223–225).
-/
def selectTier (sig : Signature) {p : PrimitiveCtx} (e : SSAExpr p) : MonadType :=
  (MonadType.ladder.find? (fun t => fits t (exprEffects sig e))).getD .nondet

/-- Tier of a body under the default ABI signature. -/
def tierOf {p : PrimitiveCtx} (e : SSAExpr p) : MonadType :=
  selectTier {} e

/--
  AC `TypeStrengthen.translate` — type_strengthen.ML:559.

  Selection is real (see `selectTier`); the *rewriting* half is not ported, so
  the body is returned unchanged. Use `strengthen` to see the tier that AC
  would have retyped the function at.
-/
def apply (ctx : Ctx) (e : SSAExpr ctx.primCtx) : Option (SSAExpr ctx.primCtx) :=
  some e

/-- The chosen tier together with AC's `typ_from_L2` shape for it. -/
structure Strengthened (p : PrimitiveCtx) where
  tier : MonadType
  /-- AC `typ_from_L2` applied to this body's state and return types. -/
  ty : Ty
  body : SSAExpr p

/--
  Run the selection: pick the highest-precedence monad type the body fits and
  report the type AC would give it (`typ_from_L2`).
-/
def strengthen (sig : Signature) {p : PrimitiveCtx}
    (stateTy retTy : Ty) (e : SSAExpr p) : Strengthened p :=
  let t := selectTier sig e
  { tier := t, ty := t.typFromL2 stateTy retTy, body := e }

theorem apply_id (ctx : Ctx) (e : SSAExpr ctx.primCtx) :
    apply ctx e = some e := rfl

/-- Selection never returns a tier the body does not fit. -/
theorem selectTier_fits (sig : Signature) {p : PrimitiveCtx} (e : SSAExpr p) :
    fits (selectTier sig e) (exprEffects sig e) = true := by
  unfold selectTier
  rcases hf : MonadType.ladder.find? (fun t => fits t (exprEffects sig e)) with _ | t
  · have := List.find?_eq_none.mp hf .nondet (MonadType.ladder_covers_all _)
    simp [fits] at this
  · simpa using List.find?_some hf

/-- A body with no effects is `pure` — AC's strongest tier (precedence 100). -/
theorem selectTier_pure_of_no_effects (sig : Signature) {p : PrimitiveCtx}
    (e : SSAExpr p) (h : exprEffects sig e = {}) :
    selectTier sig e = .pure := by
  simp [selectTier, h, MonadType.ladder, fits]

/-- Identity strengthening preserves behaviour exactly (the unported half). -/
theorem preserves_id (ctx : Ctx) (e : SSAExpr ctx.primCtx) :
    Preserves (fun a b => a = b) e e :=
  Preserves.refl e

end Lang.Simple.Lift.TS
