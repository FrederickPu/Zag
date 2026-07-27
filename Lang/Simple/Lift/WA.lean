import Lang.Simple.ABI
import Lang.SSA

/-!
  # WA — AutoCorres WordAbstract

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>
  (`WordAbstract.thy`, `word_abstract.ML`). Line numbers against l4v `master`.

  * `UWORD_MAX x ≡ (2 ^ len_of x) - 1` — WordAbstract.thy:16;
    `UWORD_MAX TYPE(32) = 2^32 - 1` — WordAbstract.thy:31
  * `abstract_binop P f X X' ≡ ∀a b. P (f a) (f b) ⟶ (f (X' a b) = X (f a) (f b))`
    — WordAbstract.thy:113–117
  * `abstract_bool_binop P f X X' ≡ ∀a b. P (f a) (f b) ⟶ (X' a b = X (f a) (f b))`
    — WordAbstract.thy:106–110
  * `abstract_val P a f b ≡ P ⟶ (a = f b)` — WordAbstract.thy:120
  * the unsigned laws we port, `unat_abstract_binops` — WordAbstract.thy:165–170,
    and `unat_abstract_bool_binops` — WordAbstract.thy:153–156
  * `corresTA P rx ex A C ≡ corresXF (λs. s) (λr s. rx r) (λr s. ex r) P A C`
    — WordAbstract.thy:549
  * entry point `WordAbstract.translate` — word_abstract.ML:184

  Zag: abstraction function `f` is `Word.toNat` (AC's `unat`), concrete `Word`
  = `BitVec 32` wraps, abstract `Nat` does not. AC discharges the `P` of
  `abstract_binop` by emitting a real `L2_guard` into the body
  (`corresTA_L2_seq`, WordAbstract.thy:597–601). **Zag does not**: the
  rewrites below target `wa.guard.add` / `wa.guard.sub`, which **fuse** AC's
  `L2_seq (L2_guard P) (op)` into one primitive: their interpretation returns
  `none` — i.e. fails, exactly as `L2_guard c ≡ liftE (guard c)` does
  (L2Defs.thy:21) — when `P` is violated, and the abstracted result otherwise.

  The fusion is forced by Zag being pure: an *unbound* guard emitted as a
  separate `let` is never forced (Zag has no `>>=` to sequence it), so a
  free-standing guard would not bite. Sequencing it monadically, as AC does,
  needs `bindK`. Consequence: an overflowing add now *fails* rather than
  silently returning a `Nat` answer the concrete program never produces. Tree-level `Corres` is still open —
  the leaf laws below are the load-bearing content.
-/

namespace Lang.Simple.Lift.WA

open Zag
open Zag.Lang.SSA
open Lang.Simple.ABI

/-- AC `UWORD_MAX TYPE('a) ≡ (2 ^ len_of 'a) - 1` — WordAbstract.thy:16. -/
def uwordMax : Nat := 2 ^ wordWidth - 1

/-- AC WordAbstract.thy:31 — `UWORD_MAX TYPE(32) = 2 ^ 32 - 1`. -/
theorem uwordMax_eq : uwordMax = 2 ^ 32 - 1 := rfl

/-- One past `UWORD_MAX`; `a + b ≤ UWORD_MAX` ↔ `a + b < overflowBound`. -/
def overflowBound : Nat := 2 ^ wordWidth

theorem le_uwordMax_iff_lt_bound (n : Nat) : n ≤ uwordMax ↔ n < overflowBound := by
  unfold uwordMax overflowBound wordWidth
  omega

/--
  AC `abstract_binop P f X X'` — WordAbstract.thy:113–117:
  `∀a b. P (f a) (f b) ⟶ (f (X' a b) = X (f a) (f b))`.
-/
def AbstractBinop {C A : Type} (P : A → A → Prop) (f : C → A)
    (X : A → A → A) (X' : C → C → C) : Prop :=
  ∀ a b, P (f a) (f b) → f (X' a b) = X (f a) (f b)

/--
  AC `abstract_bool_binop P f X X'` — WordAbstract.thy:106–110:
  `∀a b. P (f a) (f b) ⟶ (X' a b = X (f a) (f b))`.
-/
def AbstractBoolBinop {C A : Type} (P : A → A → Prop) (f : C → A)
    (X : A → A → Bool) (X' : C → C → Bool) : Prop :=
  ∀ a b, P (f a) (f b) → X' a b = X (f a) (f b)

/-- AC `abstract_val P a f b ≡ P ⟶ (a = f b)` — WordAbstract.thy:120. -/
def AbstractVal {C A : Type} (P : Prop) (a : A) (f : C → A) (b : C) : Prop :=
  P → a = f b

/-- Core WA leaf law (unsigned): no overflow ⇒ bitvector add = nat add. -/
theorem toNat_add_of_lt (x y : Word)
    (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hadd : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := BitVec.toNat_add x y
  rw [hadd]
  exact Nat.mod_eq_of_lt h

/-- Specialization using `overflowBound`. -/
theorem toNat_add_of_lt' (x y : Word)
    (h : x.toNat + y.toNat < overflowBound) :
    (x + y).toNat = x.toNat + y.toNat := by
  have : overflowBound = 2 ^ 32 := rfl
  exact toNat_add_of_lt x y (by simpa [this] using h)

/-- WA leaf: no wrap-underflow ⇒ bitvector sub = nat sub (unsigned). -/
theorem toNat_sub_of_le (x y : Word) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le h

/-!
  ### `unat_abstract_binops` / `unat_abstract_bool_binops`

  The three ported entries of AC WordAbstract.thy:165–170 and :153–156,
  stated in AC's own `abstract_binop` / `abstract_bool_binop` form with
  `f := Word.toNat` (AC's `unat`) and the *same* preconditions AC uses.
-/

/-- AC WordAbstract.thy:166 — `abstract_binop (λa b. a + b ≤ UWORD_MAX) unat (+) (+)`. -/
theorem unat_abstract_binop_add :
    AbstractBinop (fun a b => a + b ≤ uwordMax) Word.toNat (· + ·) (· + ·) := by
  intro a b h
  exact toNat_add_of_lt' a b ((le_uwordMax_iff_lt_bound _).mp h)

/-- AC WordAbstract.thy:168 — `abstract_binop (λa b. a ≥ b) unat (-) (-)`. -/
theorem unat_abstract_binop_sub :
    AbstractBinop (fun a b => b ≤ a) Word.toNat (· - ·) (· - ·) := by
  intro a b h
  exact toNat_sub_of_le a b h

/-- AC WordAbstract.thy:154 — `abstract_bool_binop (λ_ _. True) unat (<) (<)`. -/
theorem unat_abstract_bool_binop_lt :
    AbstractBoolBinop (fun _ _ => True) Word.toNat
      (fun a b => decide (a < b)) (fun a b => decide (BitVec.ult a b)) := by
  intro a b _
  simp [BitVec.ult, Word.toNat]

abbrev Rewrite (A : Ctx) :=
  List (SSAValue A.primCtx) →
    StateM (List (String × SSAValue A.primCtx)) (SSAValue A.primCtx)

/--
  `word.add` → `add`. Sound by `unat_abstract_binop_add`, i.e. AC
  `unat_abstract_binops(1)` — WordAbstract.thy:166, **provided** its
  precondition `a + b ≤ UWORD_MAX` holds. AC emits that as an `L2_guard`;
  this rewrite drops it (see module header).
-/
def rewriteAdd (A : Ctx) : Rewrite A := fun args =>
  pure (.call (.primFunc "wa.guard.add") args)

/--
  `word.sub` → `sub`. Sound by `unat_abstract_binop_sub`, i.e. AC
  `unat_abstract_binops(3)` — WordAbstract.thy:168 (precondition `a ≥ b`).
-/
def rewriteSub (A : Ctx) : Rewrite A := fun args =>
  pure (.call (.primFunc "wa.guard.sub") args)

/--
  Word op → Nat op table. Entries correspond to AC's `unat_abstract_binops`
  (WordAbstract.thy:165–170) and `unat_abstract_bool_binops` (:153–156);
  `word.lt` is unconditional there, hence no side condition here.
-/
def defaultFuncMap (A : Ctx) : String → Option (Rewrite A)
  | "word.add" => some (rewriteAdd A)
  | "word.sub" => some (rewriteSub A)
  | "word.lt"  => some fun args => pure (.op "lt" args)
  | _ => none

/--
  Type-level abstraction `word → nat`. AC builds this from
  `mk_word_abs_rule` (word_abstract.ML:40–48, `atype = nat`, `abs_fn = unat`)
  and reads it via `get_abs_type` (word_abstract.ML:84).
  NB AC's *default* is signed word → `int` via `sint` (`mk_sword_abs_rule`,
  word_abstract.ML:54–63); the unsigned/`nat` path applies only to functions
  in the `unsigned_abs` set (word_abstract.ML:208). Zag ports only unsigned.
-/
def tyMapWord : Ty → Ty
  | .prim "Word" => .prim "Nat"
  | .struct ts => .struct (ts.map tyMapWord)
  | .func as r => .func (as.map tyMapWord) (tyMapWord r)
  | .m t => .m (tyMapWord t)
  | .option t => .option (tyMapWord t)
  | .union ts => .union (ts.map tyMapWord)
  | t => t

mutual

partial def transportValue (A : Ctx) [Peano.Types A.primCtx]
    (funcMap : String → Option (Rewrite A)) :
    SSAValue primitiveCtx →
      StateM (List (String × SSAValue A.primCtx)) (Option (SSAValue A.primCtx))
  | .raw (.prim (.prim "Word") val) =>
      let w : Word := by
        simpa [WordTy, primitiveCtx, Ty.type, PrimitiveCtx.get?] using val
      pure (some (.nat (Word.toNat w)))
  | .raw (.prim (.prim "Bool") val) =>
      let b : Bool := by
        simpa [primitiveCtx, Ty.type, PrimitiveCtx.get?] using val
      pure (some (.bool b))
  | .raw (.prim (.prim "Nat") val) =>
      let n : Nat := by
        simpa [primitiveCtx, Ty.type, PrimitiveCtx.get?] using val
      pure (some (.nat n))
  | .raw (.primFunc name) => pure (some (.primFunc name))
  | .raw (.var idx) => pure (some (.raw (.var idx)))
  | .raw (.mkStruct tys) => pure (some (.raw (.mkStruct (tys.map tyMapWord))))
  | .raw (.structProj tys idx) =>
      let tys' := tys.map tyMapWord
      if h : idx.val < tys'.length then
        pure (some (.raw (.structProj tys' ⟨idx.val, h⟩)))
      else pure none
  | .raw _ => pure none
  | .var name => pure (some (.var name))
  | .call fn args => do
      let fn' ← transportValue A funcMap fn
      let args' ← transportValues A funcMap args
      match fn', args' with
      | some (.primFunc name), some as =>
          match funcMap name with
          | some rw => pure (some (← rw as))
          | none => pure (some (.call (.primFunc name) as))
      | some f, some as => pure (some (.call f as))
      | _, _ => pure none
  | .struct tys fields => do
      match ← transportValues A funcMap fields with
      | some fs => pure (some (.struct (tys.map tyMapWord) fs))
      | none => pure none
  | .field tys idx value => do
      match ← transportValue A funcMap value with
      | some v =>
          let tys' := tys.map tyMapWord
          if h : idx.val < tys'.length then pure (some (.field tys' ⟨idx.val, h⟩ v))
          else pure none
      | none => pure none
  | .op name args => do
      match ← transportValues A funcMap args with
      | some as => pure (some (.op name as))
      | none => pure none
  | .block rt body =>
      match transportExpr A funcMap body with
      | some b => pure (some (.block (tyMapWord rt) b))
      | none => pure none
  | .phi _ _ => pure none
  | .loopBody vc st init rt body => do
      match (← transportValues A funcMap init), transportExpr A funcMap body with
      | some inits, some body' =>
          let st' := st.map fun v => { v with ty := tyMapWord v.ty }
          pure (some (.loopBody vc st' inits (tyMapWord rt) body'))
      | _, _ => pure none

partial def transportValues (A : Ctx) [Peano.Types A.primCtx]
    (funcMap : String → Option (Rewrite A)) :
    List (SSAValue primitiveCtx) →
      StateM (List (String × SSAValue A.primCtx)) (Option (List (SSAValue A.primCtx)))
  | [] => pure (some [])
  | v :: vs => do
      match (← transportValue A funcMap v), (← transportValues A funcMap vs) with
      | some x, some xs => pure (some (x :: xs))
      | _, _ => pure none

partial def transportExpr (A : Ctx) [Peano.Types A.primCtx]
    (funcMap : String → Option (Rewrite A)) :
    SSAExpr primitiveCtx → Option (SSAExpr A.primCtx)
  | .ret v =>
      let (r, bs) := StateT.run (transportValue A funcMap v) []
      match r with
      | some v => some (bs.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.ret v))
      | none => none
  | .let_ n v next =>
      let (r, bs) := StateT.run (transportValue A funcMap v) []
      match r, transportExpr A funcMap next with
      | some v, some n' =>
          some (bs.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.let_ n v n'))
      | _, _ => none
  | .seq a b =>
      match transportExpr A funcMap a, transportExpr A funcMap b with
      | some x, some y => some (.seq x y)
      | _, _ => none
  | .ite c t e =>
      let (r, bs) := StateT.run (transportValue A funcMap c) []
      match r, transportExpr A funcMap t, transportExpr A funcMap e with
      | some c', some t', some e' =>
          some (bs.reverse.foldr (fun b body => .let_ b.1 b.2 body) (.ite c' t' e'))
      | _, _, _ => none
  | .yield vs =>
      let (r, bs) := StateT.run (transportValues A funcMap vs) []
      match r with
      | some vs' => some (bs.reverse.foldr (fun b e => .let_ b.1 b.2 e) (.yield vs'))
      | none => none

end

/-- AC `WordAbstract.translate` — word_abstract.ML:184 (whole-body transport). -/
def applyTo (A : Ctx) [Peano.Types A.primCtx]
    (funcMap : String → Option (Rewrite A))
    (e : SSAExpr primitiveCtx) : Option (SSAExpr A.primCtx) :=
  transportExpr A funcMap e

/--
  Pointwise value relation for unsigned WA: AC's abstraction function `unat`
  read as a relation. This is `abstract_val True n Word.toNat w`
  — WordAbstract.thy:120.
-/
def wordNatRel (w : Word) (n : Nat) : Prop :=
  w.toNat = n

theorem wordNatRel_iff_abstractVal (w : Word) (n : Nat) :
    wordNatRel w n ↔ AbstractVal True n Word.toNat w := by
  constructor
  · intro h _; exact h.symm
  · intro h; exact (h trivial).symm

end Lang.Simple.Lift.WA
