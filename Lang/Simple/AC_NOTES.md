# AutoCorres source-of-truth notes

**Canonical:** <https://github.com/seL4/l4v/tree/master/tools/autocorres>  
**Docs:** <https://trustworthy.systems/projects/OLD/autocorres/>  
**Paper:** <https://trustworthy.systems/publications/nicta_full_text/8758.pdf>  
**Not canonical:** repo-root `AutoCorres.md` (Zag design scratch; ignore when it conflicts).

All line numbers in this file and in `Lang/Simple/Lift/*.lean` were checked
against l4v `master` by fetching the raw sources; see the anchor table at the
end. Re-verify with:

```
curl -sSL https://raw.githubusercontent.com/seL4/l4v/master/tools/autocorres/<file>
```

### Recursion / loops (Zag)

- **No fuel parameters** for program semantics or lifts.
- Use `partial_fixpoint` (as `Term.evalGo` / SSA `loopBody` already do) or
  `termination_by` on a well-founded measure.
- AC uses `recguard`/`measure_call` for *generated recursive functions*; that is
  AC’s termination device, not a license to fuel-step BigStep/eval in Zag.
  Prefer structural induction on `Com` and fixpoint induction on eval.

Paths below are relative to `tools/autocorres/`.

---

## Pipeline (`autocorres.ML` ~lines 580–620)

```
SIMPL (C parser)
  → SimplConv.translate          -- L1
  → LocalVarExtract.translate    -- L2
  → HeapLift.translate           -- HL  (optional skip_heap_abs)
  → WordAbstract.translate       -- WA  (optional skip_word_abs)
  → TypeStrengthen.translate     -- TS
  → ac_corres_chain [l1,l2,hl,wa,ts]
```

Each phase stores `function_info` with `corres_thm`. Final thm:
`ac_corres_chain OF [l1_thm, l2_thm, hl_thm, wa_thm, ts_thm]`  
(`autocorres.ML` prove_ac_corres). HL/WA missing → placeholder thms
`L2Tcorres_trivial_from_local_var_extract` / `corresTA_trivial_from_heap_lift`.

Phases enum: `FunctionInfo.CP | L1 | L2 | HL | WA | TS`.

---

## L1 — SimplConv (`L1Defs.thy`, `simpl_conv.ML`)

```isabelle
type_synonym 's L1_monad = "('s, unit + unit) nondet_monad"   -- L1Defs.thy:16
```

| combinator | def line (approx) | SIMPL |
| --- | --- | --- |
| `L1_skip` | returnOk () | Skip |
| `L1_modify m` | liftE (modify m) | Basic m |
| `L1_seq` | >>=E | Seq |
| `L1_condition` | condition | Cond |
| `L1_catch` | handle | Catch |
| `L1_while` | whileLoopE | While |
| `L1_throw` | throwError () | Throw |
| `L1_guard c` | liftE (guard c) | Guard (seq'd before body) |
| `L1_fail` | fail | missing body / Fault |

**State `'s`:** full C-parser SIMPL record (locals + globals + heap fields).  
Lookup/update = record getters/setters / `modify`, not free lists.

**L1corres** (L1Defs.thy:54–65):  
`¬snd (A s) → (Normal s' ↦ (Inr (), s') ∈ fst (A s)) ∧ (Abrupt s' ↦ (Inl (), s') ∈ fst (A s)) ∧ ¬Fault/Stuck`.

Guard fail = monadic **fail** (snd), not Inl.

---

## L2 — LocalVarExtract (`L2Defs.thy`, `local_var_extract.ML`)

```isabelle
type_synonym ('s,'a,'e) L2_monad = "('s, 'e + 'a) nondet_monad"  -- L2Defs.thy:11
```

| combinator | role |
| --- | --- |
| `L2_gets f names` | locals as pure monadic values |
| `L2_seq` | >>=E |
| `L2_modify m` | modify residual globals |
| `L2_guard` / `L2_throw` / `L2_while` | as named |

**Ambient `'s` after extract = globals only** (heap + C globals). Locals are **not** in state.

```isabelle
L2corres st ret_xf ex_xf P A C ≡ corresXF st (λ_. ret_xf) (λ_. ex_xf) P A C
-- L2Defs.thy:85–91
-- st : full_state → globals   (Zag: ABI.projectGlobals / L2.stOfFull?)
```

### Open: `fromL1?` is run-then-gets, not a real extract

`Lift/L2.fromL1?` wraps the whole L1 body in a block and reads locals out of the
resulting state with `state.get.i`. AC's LocalVarExtract instead *removes* the
locals from the state (local_var_extract.ML:836/856 emit `L2_gets`/`L2_modify`
and the local's modify is dropped).

Consequence, pinned by `Test/AutoCorres.add_chain_word_abs_blocked_by_run_then_gets`:
for a body containing `Basic`, the L1 route cannot reach WA, because the raw
Simpl terms (`state.set.i`) survive into the WA input and `waPrimCtx` has no
`State` prim. The **pure** route (`fromCom?`) *is* a real extract and does reach
WA (`add_pure_chain_reaches_wa`). Closing this means rewriting the L1 flagged
body into named locals rather than post-hoc reading them.

---

## HL — HeapLift (`HeapLift.thy`, `heap_lift.ML`)

- Concrete: C-parser byte/`t_hrs` heap in globals.
- Abstract: `lifted_globals` with typed heaps per type + validity.
- **Changes state type** (new globals record). Not a prim whitelist tweak.
- Optional (`skip_heap_abs`).

---

## WA — WordAbstract (`WordAbstract.thy`, `word_abstract.ML`)

- Machine words → `nat` / `int` with overflow/guards.
- Optional (`skip_word_abs`).
- Builds on HL output (or L2 if HL skipped) — i.e. on a *post-extract* body.

```isabelle
UWORD_MAX x        ≡ (2 ^ len_of x) - 1                              -- :16
abstract_binop P f X X' ≡ ∀a b. P (f a) (f b) ⟶ f (X' a b) = X (f a) (f b)  -- :113–117
abstract_bool_binop P f X X' ≡ ∀a b. P (f a) (f b) ⟶ X' a b = X (f a) (f b) -- :106–110
abstract_val P a f b    ≡ P ⟶ (a = f b)                              -- :120
corresTA P rx ex A C    ≡ corresXF (λs. s) (λr s. rx r) (λr s. ex r) P A C  -- :549
```

Ported leaves (`f := unat`, Zag `Word.toNat`), with AC's own preconditions:

| AC | precondition | Zag |
| --- | --- | --- |
| `unat_abstract_binops(1)` :166 | `a + b ≤ UWORD_MAX` | `unat_abstract_binop_add` |
| `unat_abstract_binops(3)` :168 | `a ≥ b` | `unat_abstract_binop_sub` |
| `unat_abstract_bool_binops(1)` :154 | `True` | `unat_abstract_bool_binop_lt` |

---

## TS — TypeStrengthen (`TypeStrengthen.thy`, `monad_types.ML`)

Rules (README): `pure` | `option` | `gets` | `nondet`.  
Strengthens monadic type to the weakest that still models the program.

`Monad_Types.new_monad_type` registrations, with lifting heads:

| name | head | line |
| --- | --- | --- |
| `pure` | `TS_return` (`≡ liftE (return x)`, :63) | :81 |
| `gets` | `TS_gets` (`≡ liftE (gets x)`, :134) | :145 |
| `option` | `gets_theE` | :231 |
| `nondet` | `liftE` (default) | :323 |

Entry point `TypeStrengthen.translate` — type_strengthen.ML:559.

---

## Zag mapping (implementation targets)

| AC | Zag target |
| --- | --- |
| SIMPL com + BigStep | `Lang.Simple.Com` / `BigStep` |
| `'s` full record | `ABI.FullState` = locals + `Globals` |
| L1_monad / L1corres | flags `[fault,abrupt,FullState]` + `toSSA?` / `evalL1?` until monadic bindK; prove match to BigStep |
| L2_monad / L2corres | named SSA locals + `projectGlobals`; real extract not run-then-gets |
| HL state change | separate `primCtx` (HeapW); `CtxRefine` |
| WA Word→Nat | separate `primCtx`; leaf laws + tree Corres |
| TS ladder | drop/strengthen; pure tier first |
| ac_corres_chain | compose phase corres Props |

**Zag constraint:** no `bindK` → L1/L2 may use explicit SSA + flags as *encoding* of AC monads, but must cite AC and prove same observations.

---

---

## Verified anchor table

Checked against l4v `master`. Every citation in `Lang/Simple/Lift/*.lean`,
`Dialect.lean` and `Lift.lean` resolves to a row here.

| file | line | anchor |
| --- | --- | --- |
| L1Defs.thy | 16 | `type_synonym 's L1_monad` |
| L1Defs.thy | 17–26 | `L1_seq`,`L1_skip`,`L1_modify`,`L1_condition`,`L1_catch`,`L1_while`,`L1_throw`,`L1_spec`,`L1_guard`,`L1_init` |
| L1Defs.thy | 27 | `L1_call` |
| L1Defs.thy | 37–40 | `L1_fail`,`L1_recguard`,`L1_set_to_pred`,`recguard_dec` |
| L1Defs.thy | 54–65 | `L1corres` |
| L1Defs.thy | 94/107/119/128/136/147/156/166 | `L1corres_skip/throw/seq/modify/condition/catch/while/guard` |
| simpl_conv.ML | 118–150 | SIMPL→L1 case table |
| simpl_conv.ML | 437 / 541 | `convert` / `translate` |
| L2Defs.thy | 11 | `type_synonym ('s,'a,'e) L2_monad` |
| L2Defs.thy | 12–24 | `L2_unknown`,`L2_seq`,`L2_modify`,`L2_gets`,`L2_condition`,`L2_catch`,`L2_while`,`L2_throw`,`L2_spec`,`L2_guard`,`L2_fail`,`L2_call`,`L2_recguard` |
| L2Defs.thy | 26 | `L2_skip` |
| L2Defs.thy | 85–91 | `L2corres` |
| local_var_extract.ML | 836 / 856 / 1607 | `L2_gets` emit / `L2_modify` emit / `translate` |
| HeapLift.thy | 17 | `L2Tcorres` |
| HeapLift.thy | 30/31/32 | `abs_guard` / `abs_expr` / `abs_modifies` |
| HeapLift.thy | 39–41 | `struct_rewrite_guard/expr/modifies` |
| heap_lift.ML | 617 | `translate` |
| WordAbstract.thy | 14/16/31 | `WORD_MAX` / `UWORD_MAX` / `UWORD_MAX TYPE(32)` |
| WordAbstract.thy | 106–110 / 113–117 / 120 | `abstract_bool_binop` / `abstract_binop` / `abstract_val` |
| WordAbstract.thy | 153–156 / 165–170 | `unat_abstract_bool_binops` / `unat_abstract_binops` |
| WordAbstract.thy | 549 | `corresTA` |
| word_abstract.ML | 184 | `translate` |
| TypeStrengthen.thy | 63/81/134/145/231/323 | `TS_return`,`pure`,`TS_gets`,`gets`,`option`,`nondet` |
| type_strengthen.ML | 559 | `translate` |
| function_info.ML | 135/136/142 | `datatype phase`, `string_of_phase`, `encode_phase` |
| autocorres.ML | 35/44 | `skip_heap_abs` / `skip_word_abs` option refs |
| autocorres.ML | 586/592/605/617/625 | the five `*.translate` calls |
| autocorres.ML | 652 | `hl_thm` placeholder `L2Tcorres_trivial_from_local_var_extract` (HL skipped) |
| autocorres.ML | 655 | `wa_thm` placeholder `corresTA_trivial_from_heap_lift` (WA skipped) |
| autocorres.ML | 660 | `ac_corres_chain OF [l1,l2,hl,wa,ts]` |

---

## Stage 1 — the deep embedding vs real SIMPL

Ground truth: `tools/c-parser/Simpl/Language.thy` (`com` datatype) and
`Simpl/Semantic.thy` (`xstate` at :16, `inductive exec` at :58–127).

```isabelle
datatype ('s,'f) xstate = Normal 's | Abrupt 's | Fault 'f | Stuck   -- Semantic.thy:16
datatype ('s,'p,'f) com = Skip | Basic "'s ⇒ 's" | Spec "('s×'s) set"
  | Seq | Cond "'s bexp" | While "'s bexp" | Call 'p | DynCom "'s ⇒ com"
  | Guard 'f "'s bexp" com | Throw | Catch                          -- Language.thy
```

Rule-by-rule, `Lang/Simple/Defs.lean`'s `BigStep` matches SIMPL's `exec` for
Skip, Guard, Seq, Cond, While, Call/CallUndefined, Throw, Catch and the three
propagation rules — Zag splits SIMPL's single `Seq`/`WhileTrue`/`CatchMiss`
rules into per-outcome cases, which is a derived form, not a divergence
(`fromNonNormal` is exactly FaultProp + StuckProp + AbruptProp).

**Real divergences, all currently undocumented in the code:**

| # | SIMPL | Zag | consequence |
| --- | --- | --- | --- |
| D1 | `GuardFault: s∉g ⟹ … ⇒ Fault f` — `Fault` carries **only** the fault name (Semantic.thy:16,68) | `Outcome.fault (f) (s)` carries a **state** | Zag observes a post-fault state SIMPL does not have. `L1.encodeOutcome (.fault f s)` packs that state into the flagged struct — an observation with no SIMPL counterpart. |
| D2 | `Basic "'s ⇒ 's"` is **total** (Language.thy); `Basic: ⟨Basic f,Normal s⟩ ⇒ Normal (f s)` | `Basic` is a partial Zag term; extra `basicStuck` rule | Conservative (maps into SIMPL's `Stuck`), but `L1.toSSA?`'s `.Basic` arm emits `basicUpdate` with **no failure path**, so the translation silently assumes totality. |
| D3 | `Cond`/`While`/`Guard` test `s ∈ b` on a **set** — total | `evalBExp?` partial; extra `condStuck`/`whileStuck`/`guardStuck` | Same shape as D2: sound extension, unhandled by the L1 translation. |
| D4 | `Guard 'f g c` carries a fault **name** | one global `unitFault` | C's distinct undefined-behaviour classes collapse to one fault. |
| D5 | `Spec`, `DynCom` | absent | Proper subset — fine, but `Lift/L1.lean`'s case table says it mirrors simpl_conv.ML "one-for-one", which is false (also missing `lvar_nondet_init ↦ L1_init`, `Spec ↦ L1_spec`, and `L1_fail`). |
| D6 | — | `BigStep.skip` is stated for an arbitrary outcome `o`, overlapping `fromNonNormal` | Redundant derivations; harmless but should be `Normal`-only to match Semantic.thy:63. |

D1 and D4 are genuine semantic differences and must be fixed before any
`L1corres` proof means what it says. D2/D3 are forced by Zag terms being
partial; they are sound, but the L1 translation must handle them.

---

## Where the port has cheated its definitions

AC is **not** mostly metaprograms. It is mostly *theorems*, with a couple of
metaprograms that apply them repeatedly. Counting `lemma`/`lemmas` blocks in
l4v `master`:

| file | lemma blocks | of which corres rules |
| --- | --- | --- |
| CorresXF.thy | 52 | `corresXF_*` 45 |
| L1Defs.thy | 49 | `L1corres_*` 24 |
| L2Defs.thy | 63 | `L2corres_*` 29 |
| HeapLift.thy | 127 | `L2Tcorres_*` 23, `[heap_abs]` 65 |
| WordAbstract.thy | 126 | `corresTA_*` 57 |
| TypeStrengthen.thy | 55 | — |
| **total** | **472** | |

Zag has the *relations* but almost none of the *rules*, and that is the whole
gap. Concretely:

1. **The translators are not proof-carrying.** `L1.toSSA?`, `L2.fromCom?`,
   `L2.fromL1?`, `WA.applyTo`, `HL.apply` all have type `… → Option (SSAExpr …)`.
   AC's `simpl_conv.ML` `prove_term` (:96–98) *builds a proof at every node*
   from `L1corres_skip`/`L1corres_seq`/… — if the node cannot be proved, no
   term is emitted. Zag emits terms unconditionally. The type should be
   `Option (Σ e, L1corres … e cmd)` so the obligation cannot be skipped.
   **This is the single reason the proofs are short: there aren't any.**
2. **`SimplExceptionFaithful` is never established for the real translator.**
   Only `faithful_exnCore_of`, for a Skip/Throw-only translator, and that is
   conditional on `ExnCoreEvalOk`, which is *assumed*.
3. **`L2corres` was weaker than `corresXF`** — no post-state conjunct, no
   exception arm, plus an invented `(st s).isSome` condition AC does not have.
   `Corres.CorresXF` now states CorresXF.thy:34–40 properly; `L2.L2corres`
   still needs to be rebuilt on it.
4. **`fromL1?` drops the exception flags.** It keeps only field 2 (the state),
   so after L1→L2 an abrupt program is indistinguishable from a normal one
   (`Test/AutoCorres.throw_l1l2_eval_still_unpacks`). AC's `ex_xf` exists
   precisely to stop that.
5. **WA drops `abstract_binop`'s precondition** instead of emitting a guard
   (AC: `corresTA_L2_seq`, WordAbstract.thy:597–601). The leaf laws are proved;
   the rewrite that uses them is not sound without the guard.
6. **HL does no state-type abstraction** — `chainHL?` keeps `primCtx` fixed,
   so there is no `lifted_globals` analogue.

Rule of thumb going forward: **every piece of AC proof material must have a
counterpart here, or a named gap saying it doesn't.** A pass that type-checks
without its corres rules has cheated its definition.

---

## Faithfulness checklist (review loop)

1. [~] L1: Skip/Throw/Catch/Guard/Cond/While/**Basic(C0)** exec; BigStep↔L1 pins on Word2; ∀-Faithful open
2. [~] L2: pure fromCom?+eval is a real extract; **fromL1? is run-then-gets** (see gap above)
3. [~] L2corres Prop has st+ret_rel; `stOfFull?` total + projects globals (proved ∀s)
4. [~] HL: load+store rewrite; separate ctx; `L2Tcorres` shape; no valRel; struct_rewrite unported
5. [x] WA: `unat_abstract_binops` +/− and `unat_abstract_bool_binops` < in AC's own `abstract_binop` form; tree Corres open
6. [~] TS: AC monad-type ladder named; `apply` id at the `pure` tier (honest reduced)
7. [~] AcCorresChain shape + Word2 holds
8. [x] PrimCtx: shared only CP/L1/L2; HL and WA distinct
9. [x] No fuel; loopBody→recurse/partial_fixpoint (L1 While base fix)
10. [x] Phase enum CP|L1|L2|HL|WA|TS with `dialectOf` total (function_info.ML:135)
11. [x] `skip_heap_abs` / `skip_word_abs` options + trivial-corres slots (autocorres.ML:652,655)
