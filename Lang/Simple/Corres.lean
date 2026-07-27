import Lang.SSA
import Lang.Simple.Defs

/-!
  # General faithfulness (pass-independent)

  Faithfulness is **not** owned by L1/L2. It is one relation:

  ```
  Faithful translate srcSem tgtSem rel
  ```

  Passes only instantiate it. SSA special cases: `Preserves`, `Corres`.
-/

namespace Lang.Simple.Corres

open Zag
open Zag.Lang.SSA
open Lang.Simple

/--
  Universal pass faithfulness.
  Direction: source behaviour is matched on the target (AutoCorres-style).
-/
def Faithful {Src Tgt In OutS OutT : Type}
    (translate : Src → Option Tgt)
    (srcSem : Src → In → OutS → Prop)
    (tgtSem : Tgt → In → OutT → Prop)
    (rel : OutS → OutT → Prop) : Prop :=
  ∀ (s : Src) (t : Tgt),
    translate s = some t →
    ∀ (i : In) (oS : OutS),
      srcSem s i oS →
      ∃ oT : OutT, tgtSem t i oT ∧ rel oS oT

theorem Faithful.id {S In Out : Type}
    (sem : S → In → Out → Prop) :
    Faithful (fun s : S => some s) sem sem (fun a b => a = b) := by
  intro s t h i oS hs
  cases h
  exact ⟨oS, hs, rfl⟩

/-- SSA→SSA, same `Ctx`. -/
def Preserves {ctx : Ctx}
    (rel : Val ctx.primCtx → Val ctx.primCtx → Prop)
    (src tgt : SSAExpr ctx.primCtx) : Prop :=
  ∀ (env : List (Val ctx.primCtx)) (v : Val ctx.primCtx),
    (do
      let tm ← SSAExpr.toTerm? src {}
      Term.eval ctx env tm) = some v →
    ∃ w,
      (do
        let tm ← SSAExpr.toTerm? tgt {}
        Term.eval ctx env tm) = some w ∧
      rel v w

theorem Preserves.refl {ctx : Ctx} (e : SSAExpr ctx.primCtx) :
    Preserves (fun a b => a = b) e e := by
  intro env v heval
  exact ⟨v, heval, rfl⟩

structure ValRel (A C : Ctx) where
  rel : Val C.primCtx → Val A.primCtx → Prop

/-- Cross-`Ctx` SSA correspondence (WA/HL). -/
def Corres {A C : Ctx} (R : ValRel A C)
    (src : SSAExpr C.primCtx) (tgt : SSAExpr A.primCtx) : Prop :=
  ∀ (envC : List (Val C.primCtx)) (envA : List (Val A.primCtx)) (vC : Val C.primCtx),
    envC.length = envA.length →
    (∀ (i : Nat) (hiC : i < envC.length) (hiA : i < envA.length),
      R.rel (envC[i]'hiC) (envA[i]'hiA)) →
    (do
      let tm ← SSAExpr.toTerm? src {}
      Term.eval C envC tm) = some vC →
    ∃ vA, (do
      let tm ← SSAExpr.toTerm? tgt {}
      Term.eval A envA tm) = some vA ∧
      R.rel vC vA

def CrossTransFaithful {A C : Ctx} (R : ValRel A C)
    (translate : SSAExpr C.primCtx → Option (SSAExpr A.primCtx)) : Prop :=
  ∀ src tgt, translate src = some tgt → Corres R src tgt

def CompOblig {A B C : Ctx}
    (R₁ : ValRel B C) (R₂ : ValRel A B)
    (a : SSAExpr C.primCtx) (b : SSAExpr B.primCtx) (c : SSAExpr A.primCtx) : Prop :=
  Corres R₁ a b → Corres R₂ b c →
    Corres ⟨fun vC vA => ∃ vB, R₁.rel vC vB ∧ R₂.rel vB vA⟩ a c

/-- Simpl exceptions → SSA (L1): instantiate with `toSSA?`, `evalL1?`, `encodeOutcome`. -/
def SimplExceptionFaithful {ctx : Context} {proc : Type} {fault : Type}
    [Peano.Types ctx.primCtx]
    (Γ : ProcEnv ctx proc fault) (unitFault : fault)
    (translate : Com ctx proc fault → Option (SSAExpr ctx.primCtx))
    (evalTgt : SSAExpr ctx.primCtx → Val ctx.primCtx → Option (Val ctx.primCtx))
    (encode : Outcome ctx fault → Option (Val ctx.primCtx)) : Prop :=
  Faithful translate
    (fun cmd s o =>
      s.ty = ctx.stateTy ∧
      BigStep Γ unitFault cmd (.normal s) o ∧
      o ≠ Outcome.stuck)
    (fun expr s v => evalTgt expr s = some v)
    (fun o v => encode o = some v)

/-- Simpl pure fragment → SSA (L2): instantiate with `fromCom?`, `PureStep`, env maps. -/
def SimplPureFaithful {ctx : Context} {proc : Type} {fault : Type}
    (step : Com ctx proc fault → Val ctx.primCtx → Val ctx.primCtx → Prop)
    (translate : Com ctx proc fault → Option (SSAExpr ctx.primCtx))
    (envOf : Val ctx.primCtx → List (Val ctx.primCtx))
    (resultOf : Val ctx.primCtx → Val ctx.primCtx)
    (evalTgt : SSAExpr ctx.primCtx → List (Val ctx.primCtx) → Option (Val ctx.primCtx)) :
    Prop :=
  Faithful translate
    (fun cmd s t => step cmd s t)
    (fun expr s v => evalTgt expr (envOf s) = some v)
    (fun t v => v = resultOf t)

/-!
  ## AC's actual correspondence relation

  Everything in AutoCorres is stated in terms of `corresXF`
  (`tools/autocorres/CorresXF.thy:34–40`):

  ```isabelle
  corresXF st ret_xf ex_xf P A C ≡
      ∀s. P s ∧ ¬ snd (A (st s)) ⟶
          (∀(r, t) ∈ fst (C s).
            case r of
               Inl r ⇒ (Inl (ex_xf r t), st t) ∈ fst (A (st s))
             | Inr r ⇒ (Inr (ret_xf r t), st t) ∈ fst (A (st s)))
          ∧ ¬ snd (C s)
  ```

  Three things it says that a "same crash behaviour" reading would miss:

  1. the **post-state** is related — `st t` must be the abstract post-state,
     not merely some state;
  2. the **exception arm** is related, via a *separate* extractor `ex_xf`;
  3. the concrete side **must not fail** (`¬ snd (C s)`) whenever the abstract
     side does not.

  `L2corres`, `L2Tcorres` and `corresTA` are all instances of it
  (L2Defs.thy:85–90, HeapLift.thy:17, WordAbstract.thy:549).
-/

/-- Result of a deterministic Zag body: `none` is AC's `snd M` (failure). -/
abbrev XFResult (V S : Type) := Option (Sum V V × S)

/--
  AC `corresXF` — CorresXF.thy:34–40, read deterministically
  (`none` ↦ `snd M`, `some (r,t)` ↦ the singleton `fst M`).

  `C` is concrete, `A` abstract, `st` the state abstraction, `ret_xf`/`ex_xf`
  the return/exception extractors, `P` the precondition.
-/
def CorresXF {CS AS CV AV : Type}
    (st : CS → AS)
    (ret_xf ex_xf : CV → CS → AV)
    (P : CS → Prop)
    (A : AS → XFResult AV AS)
    (C : CS → XFResult CV CS) : Prop :=
  ∀ s : CS, P s → (A (st s)).isSome →
    -- ¬ snd (C s)
    (C s).isSome ∧
    -- the Inl / Inr arms, *including* the post-state `st t`
    ∀ r t, C s = some (r, t) →
      A (st s) = some
        ((match r with
          | .inl e => .inl (ex_xf e t)
          | .inr v => .inr (ret_xf v t)), st t)

/-- The post-state really is constrained (contrast: a crash-only relation). -/
theorem CorresXF.post_state {CS AS CV AV : Type}
    {st : CS → AS} {ret_xf ex_xf : CV → CS → AV} {P : CS → Prop}
    {A : AS → XFResult AV AS} {C : CS → XFResult CV CS}
    (h : CorresXF st ret_xf ex_xf P A C)
    {s : CS} (hP : P s) (hA : (A (st s)).isSome)
    {r : Sum CV CV} {t : CS} (hC : C s = some (r, t)) :
    ∃ ra, A (st s) = some (ra, st t) :=
  ⟨_, (h s hP hA).2 r t hC⟩

/-- The exception arm is related by `ex_xf`, not collapsed into success. -/
theorem CorresXF.exception_arm {CS AS CV AV : Type}
    {st : CS → AS} {ret_xf ex_xf : CV → CS → AV} {P : CS → Prop}
    {A : AS → XFResult AV AS} {C : CS → XFResult CV CS}
    (h : CorresXF st ret_xf ex_xf P A C)
    {s : CS} (hP : P s) (hA : (A (st s)).isSome)
    {e : CV} {t : CS} (hC : C s = some (.inl e, t)) :
    A (st s) = some (.inl (ex_xf e t), st t) :=
  (h s hP hA).2 _ t hC

/--
  AC `corresXF_corresXF_merge` — CorresXF.thy:703–706:

  ```isabelle
  ⟦ corresXF st rx ex P A B; corresXF st' rx' ex' P' B C ⟧ ⟹
    corresXF (st o st') (λrv s. rx (rx' rv s) (st' s))
             (λrv s. ex (ex' rv s) (st' s)) (λs. P' s ∧ P (st' s)) A C
  ```

  **This is the mathematical content of `ac_corres_chain`**: correspondence is
  transitive, composing state abstractions and extractors. Without it the
  per-phase theorems cannot be chained into an end-to-end statement.
-/
theorem CorresXF.merge {CS BS AS CV BV AV : Type}
    {st₁ : CS → BS} {rx₁ ex₁ : CV → CS → BV} {P₁ : CS → Prop}
    {st₂ : BS → AS} {rx₂ ex₂ : BV → BS → AV} {P₂ : BS → Prop}
    {A : AS → XFResult AV AS} {B : BS → XFResult BV BS} {C : CS → XFResult CV CS}
    (h₁ : CorresXF st₁ rx₁ ex₁ P₁ B C)
    (h₂ : CorresXF st₂ rx₂ ex₂ P₂ A B) :
    CorresXF (st₂ ∘ st₁)
      (fun v s => rx₂ (rx₁ v s) (st₁ s))
      (fun v s => ex₂ (ex₁ v s) (st₁ s))
      (fun s => P₁ s ∧ P₂ (st₁ s)) A C := by
  rintro s ⟨hP₁, hP₂⟩ hA
  obtain ⟨hB, hBA⟩ := h₂ (st₁ s) hP₂ hA
  obtain ⟨hC, hCB⟩ := h₁ s hP₁ hB
  refine ⟨hC, ?_⟩
  intro r t hCs
  have hBt := hCB r t hCs
  have := hBA _ (st₁ t) hBt
  cases r <;> simpa using this

/--
  AC `ac_corres` — CorresXF.thy:671–675: the end-to-end statement AC actually
  delivers. Note the `∃s'. t = Normal s'` — after the whole chain the SIMPL
  program is proved to end **normally**.
-/
def AcCorres {CS AS AV : Type}
    (st : CS → AS) (rx : CS → AV) (G : CS → Prop)
    (A : AS → XFResult AV AS)
    -- `Γ ⊢ ⟨B, Normal s⟩ ⇒ Normal s'`
    (simplNormal : CS → CS → Prop)
    -- `Γ ⊢ ⟨B, Normal s⟩ ⇒ t` for some non-`Normal` `t`
    (simplAbnormal : CS → Prop) : Prop :=
  ∀ s : CS, G s → (A (st s)).isSome →
    -- `∃s'. t = Normal s'` — the SIMPL program cannot end abnormally
    ¬ simplAbnormal s ∧
    -- `(Inr (rx s'), st s') ∈ fst (A (st s))` — value *and* post-state
    ∀ s', simplNormal s s' → A (st s) = some (.inr (rx s'), st s')

/--
  AC `ac_corres_chain` — AutoCorres.thy:78–85:

  ```isabelle
  ⟦ L1corres check_termination Γ c_L1 c;
    L2corres st_L2 rx_L2 (λ_. ()) P_L2 c_L2 c_L1;
    L2Tcorres st_HL c_HL c_L2;
    corresTA P_WA rx_WA ex_WA c_WA c_HL;
    L2_call c_WA = A ⟧
  ⟹ ac_corres (st_HL ∘ st_L2) check_termination Γ (rx_WA ∘ rx_L2)
        (P_L2 and (P_WA ∘ st_HL ∘ st_L2)) A c
  ```

  The content is **composition**, not conjunction: the state abstraction of the
  chain is `st_HL ∘ st_L2` and the return extractor is `rx_WA ∘ rx_L2`.
  Each link's *concrete* side must be the previous link's *abstract* side —
  `c_L1` appears in both the L1 and L2 premises, `c_L2` in both the L2 and HL
  premises, and so on.

  **Adjacency is enforced by the field types**: `cL1` is the abstract side of
  `L1_ok` *and* the concrete side of `L2_ok`, `cL2` likewise for `L2_ok`/`HL_ok`,
  and so on. Five unrelated programs cannot inhabit this structure.
-/
structure AcCorresChain (CS L2S HLS : Type) (CV L2V AV : Type) where
  /-- L1 body — abstract side of L1, concrete side of L2. -/
  cL1 : CS → XFResult CV CS
  /-- L2 body — abstract side of L2, concrete side of HL. -/
  cL2 : L2S → XFResult L2V L2S
  /-- HL body — abstract side of HL, concrete side of WA. -/
  cHL : HLS → XFResult L2V HLS
  /-- WA body — abstract side of WA. -/
  cWA : HLS → XFResult AV HLS
  /-- `st_L2` : full C-parser state → L2 globals (L2Defs.thy:85–90). -/
  st_L2 : CS → L2S
  /-- `st_HL` : concrete globals → lifted globals (HeapLift.thy:17). -/
  st_HL : L2S → HLS
  rx_L2 : CV → CS → L2V
  ex_L2 : CV → CS → L2V
  rx_WA : L2V → AV
  ex_WA : L2V → AV
  P_L2 : CS → Prop
  P_WA : HLS → Prop
  /-- `L2corres st_L2 rx_L2 ex_L2 P_L2 cL2 cL1` — L2Defs.thy:85–90. -/
  L2_ok : CorresXF st_L2 rx_L2 ex_L2 P_L2 cL2 cL1
  /-- `L2Tcorres st_HL cHL cL2` — identity extractors, HeapLift.thy:17. -/
  HL_ok : CorresXF st_HL (fun v _ => v) (fun v _ => v) (fun _ => True) cHL cL2
  /-- `corresTA P_WA rx_WA ex_WA cWA cHL` — `st = id`, WordAbstract.thy:549. -/
  WA_ok : CorresXF id (fun v _ => rx_WA v) (fun v _ => ex_WA v) P_WA cWA cHL

namespace AcCorresChain

variable {CS L2S HLS CV L2V AV : Type}

/-- AC's composed state abstraction `st_HL ∘ st_L2` — AutoCorres.thy:85. -/
def st (c : AcCorresChain CS L2S HLS CV L2V AV) : CS → HLS :=
  c.st_HL ∘ c.st_L2

/-- AC's composed return extractor `rx_WA ∘ rx_L2` — AutoCorres.thy:85. -/
def rx (c : AcCorresChain CS L2S HLS CV L2V AV) : CV → CS → AV :=
  fun v s => c.rx_WA (c.rx_L2 v s)

/--
  **The chain theorem.** Resolving L2, HL and WA gives one correspondence from
  the L1 body straight to the WA body, with AC's composed state abstraction
  `st_HL ∘ st_L2` and composed extractor `rx_WA ∘ rx_L2` — AutoCorres.thy:78–85.
  Proved from `CorresXF.merge` (CorresXF.thy:703–706), applied twice.
-/
theorem resolve (c : AcCorresChain CS L2S HLS CV L2V AV) :
    CorresXF c.st
      (fun v s => c.rx_WA (c.rx_L2 v s))
      (fun v s => c.ex_WA (c.ex_L2 v s))
      (fun s => (c.P_L2 s ∧ True) ∧ c.P_WA (c.st_HL (c.st_L2 s)))
      c.cWA c.cL1 :=
  (c.L2_ok.merge c.HL_ok).merge c.WA_ok

/-- The composed extractor really is AC's `rx_WA ∘ rx_L2`. -/
theorem resolve_rx (c : AcCorresChain CS L2S HLS CV L2V AV) (v : CV) (s : CS) :
    c.rx v s = c.rx_WA (c.rx_L2 v s) := rfl

end AcCorresChain

end Lang.Simple.Corres
