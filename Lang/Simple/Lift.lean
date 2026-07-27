import Lang.Simple.Lift.L1
import Lang.Simple.Lift.L2
import Lang.Simple.Lift.WA
import Lang.Simple.Lift.TS
import Lang.Simple.Lift.HL
import Lang.Simple.ABI
import Lang.Simple.Dialect

/-!
  # AutoCorres pass chain

  Upstream: <https://github.com/seL4/l4v/tree/master/tools/autocorres>.
  The chain below mirrors `autocorres.ML:586–625`:

  ```
  SIMPL (C parser)
    → SimplConv.translate         -- autocorres.ML:586   (L1)
    → LocalVarExtract.translate   -- autocorres.ML:592   (L2)
    → HeapLift.translate          -- autocorres.ML:605   (HL, skippable :596)
    → WordAbstract.translate      -- autocorres.ML:617   (WA, skippable :615)
    → TypeStrengthen.translate    -- autocorres.ML:625   (TS)
    → ac_corres_chain [l1,l2,hl,wa,ts]                   -- autocorres.ML:660
  ```

  | pass | AC source | Zag status |
  | --- | --- | --- |
  | L1 | L1Defs.thy, simpl_conv.ML | flags+FullState; exec ladder proved; ∀-Faithful open |
  | L2 | L2Defs.thy, local_var_extract.ML | pure fromCom? + fromL1? unpack; L2corres shape |
  | HL | HeapLift.thy, heap_lift.ML | leaf rewrite; skippable, as in AC |
  | WA | WordAbstract.thy, word_abstract.ML | `unat_abstract_binops` leaves + rewrite |
  | TS | TypeStrengthen.thy, type_strengthen.ML | id at the `pure` tier (§5.0 reduced TS) |

  Live `M := Id`, state explicit (§5.0). Dialects: `Dialect.*`.
  Honest grade: **PARTIAL** pipeline — not full AC until proved corres + real extract.
-/

namespace Lang.Simple.Lift

open Zag
open Zag.Lang.SSA
open Lang.Simple
open Lang.Simple.ABI
open Lang.Simple.Dialect

/--
  AC pipeline options — autocorres.ML:35,44 (`skip_heap_abs`, `skip_word_abs`).
  When a phase is skipped AC substitutes a trivial corres theorem rather than
  dropping the phase from the chain (autocorres.ML:652,655).
-/
structure Options where
  /-- AC `skip_heap_abs` — autocorres.ML:35, read at :596. -/
  skipHeapAbs : Bool := false
  /-- AC `skip_word_abs` — autocorres.ML:44, read at :338/:615. -/
  skipWordAbs : Bool := false
  deriving Repr

/-- Pure path: Simpl → L2 SSA (named locals). AC LocalVarExtract fused. -/
def pureChain? {ctx : Context} {proc : Type u} {fault : Type v}
    (locals : L2.LocalContext) (cmd : Com ctx proc fault) :
    Option (SSAExpr ctx.primCtx) :=
  L2.fromCom? locals cmd

/-- Exception path: Simpl → L1 flagged SSA. AC `SimplConv.translate` — :586. -/
def exnChain? {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] (cmd : Com ctx proc fault) :
    Option (SSAExpr ctx.primCtx) :=
  L1.toSSA? cmd

/--
  `SimplConv.translate` then `LocalVarExtract.translate`
  — autocorres.ML:586 then :592.
-/
def l1l2Chain? {ctx : Context} {proc : Type u} {fault : Type v}
    [Peano.Types ctx.primCtx] (locals : L2.LocalContext)
    (cmd : Com ctx proc fault) : Option (SSAExpr ctx.primCtx) := do
  let l1 ← L1.toSSA? cmd
  L2.fromL1? locals l1

def abstractNatPrimCtx : PrimitiveCtx := waPrimCtx

instance : Peano.Types abstractNatPrimCtx where
  natType := by rfl
  boolType := by rfl

def abstractNatCtx : Ctx := waZagCtx

instance : Peano.Types abstractNatCtx.primCtx where
  natType := by rfl
  boolType := by rfl

def waFuncMap : String → Option (WA.Rewrite abstractNatCtx) :=
  WA.defaultFuncMap abstractNatCtx

/-- `WordAbstract.translate` — autocorres.ML:617, word_abstract.ML:184. -/
def chainWA? (_arity : Nat) (e : SSAExpr primitiveCtx) :
    Option (SSAExpr abstractNatCtx.primCtx) :=
  WA.applyTo abstractNatCtx waFuncMap e

def heapConcreteCtx : Ctx := hlZagCtx

/-- `HeapLift.translate` — autocorres.ML:605, heap_lift.ML:617. -/
def chainHL? {p : PrimitiveCtx} (e : SSAExpr p) : Option (SSAExpr p) :=
  HL.apply e

/-- `TypeStrengthen.translate` — autocorres.ML:625, type_strengthen.ML:559. -/
def chainTS? (ctx : Ctx) (e : SSAExpr ctx.primCtx) : Option (SSAExpr ctx.primCtx) :=
  TS.apply ctx e

/--
  HL slot. When `skip_heap_abs` holds AC does not drop the phase: it fills the
  `hl_thm` slot with `L2Tcorres_trivial_from_local_var_extract OF [l2_thm]`
  — autocorres.ML:652 — so the body carries through unchanged.
-/
def chainHLOrSkip? {p : PrimitiveCtx} (opts : Options) (e : SSAExpr p) :
    Option (SSAExpr p) :=
  if opts.skipHeapAbs then some e else chainHL? e

/--
  WA slot. When `skip_word_abs` holds AC fills the `wa_thm` slot with
  `corresTA_trivial_from_heap_lift OF [hl_thm]` — autocorres.ML:655.
  Since Zag's WA also changes `primCtx`, the skipped path stays in
  `primitiveCtx` (the concrete-word branch).
-/
def chainWAOrSkip? (opts : Options) (arity : Nat) (e : SSAExpr primitiveCtx) :
    Option (Sum (SSAExpr primitiveCtx) (SSAExpr abstractNatCtx.primCtx)) :=
  if opts.skipWordAbs then some (.inl e)
  else (chainWA? arity e).map Sum.inr

/-- Pure pipeline: L2 → HL → WA → TS (AC order, autocorres.ML:586–625). -/
def fullPureChain? {proc : Type u} {fault : Type v}
    (arity : Nat) (locals : L2.LocalContext)
    (cmd : Com (wordStateContext arity) proc fault) :
    Option (SSAExpr abstractNatCtx.primCtx) := do
  let l2 ← pureChain? locals cmd
  let hl ← chainHLOrSkip? {} l2
  let wa ← chainWA? arity hl
  chainTS? abstractNatCtx wa

/-- Exception pipeline: L1 → L2 → HL → WA → TS (AC order). -/
def fullExnChain? {proc : Type u} {fault : Type v}
    (arity : Nat) (locals : L2.LocalContext)
    (cmd : Com (wordStateContext arity) proc fault) :
    Option (SSAExpr abstractNatCtx.primCtx) := do
  let l2 ← l1l2Chain? (ctx := wordStateContext arity) locals cmd
  let hl ← chainHLOrSkip? {} l2
  let wa ← chainWA? arity hl
  chainTS? abstractNatCtx wa

/--
  Full chain with AC's options honoured, including a live HL pass.
  `skip_word_abs` stops in `primitiveCtx` (AC keeps the L2/HL body);
  otherwise the result is in the abstract `Nat` ctx.
-/
def fullChain? {proc : Type u} {fault : Type v}
    (opts : Options) (arity : Nat) (locals : L2.LocalContext)
    (cmd : Com (wordStateContext arity) proc fault) :
    Option (Sum (SSAExpr primitiveCtx) (SSAExpr abstractNatCtx.primCtx)) := do
  let l2 ← l1l2Chain? (ctx := wordStateContext arity) locals cmd
  let hl ← chainHLOrSkip? opts l2
  match ← chainWAOrSkip? opts arity hl with
  | .inl e => (chainTS? (wordStateContext arity).zagCtx e).map Sum.inl
  | .inr e => (chainTS? abstractNatCtx e).map Sum.inr

/-- Skipping HL leaves the body untouched (AC `hl_thm` placeholder, :652). -/
theorem chainHLOrSkip_skip {p : PrimitiveCtx} (e : SSAExpr p) :
    chainHLOrSkip? { skipHeapAbs := true } e = some e := rfl

/-- Skipping WA keeps the concrete-word body (AC `wa_thm` placeholder, :655). -/
theorem chainWAOrSkip_skip (arity : Nat) (e : SSAExpr primitiveCtx) :
    chainWAOrSkip? { skipWordAbs := true } arity e = some (.inl e) := rfl

end Lang.Simple.Lift
