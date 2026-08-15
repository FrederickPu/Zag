# Handoff: Zag block-IR refactor

## Where things stand

`lake build Zag Lib Meta Test` is **green**. `Lang/` and `Comparator/` are gone (SSA moved into
Zag core; AutoCorres was deleted before this work started).

### The new core

`Ty` is three constructors, `Term` is five ([Zag/Data.lean](Zag/Data.lean)):

```lean
inductive Ty where
| var  : String → Ty
| prim : String → List Ty → Ty      -- parametric type application
| func : List Ty → Ty → Ty

inductive Term (primCtx : PrimitiveCtx) where
| prim (ty : Ty) : Ty.type primCtx ty → Term primCtx
| var  : String → Term primCtx
| app  : Term primCtx → List (Term primCtx) → Term primCtx
| op   : String → List (Term primCtx) → Term primCtx    -- semantics from the context
| call : String → List (Term primCtx) → Term primCtx    -- semantics from the program
```

Gone, and what replaced each:

| removed | replacement |
| --- | --- |
| `Term.primFunc`, `PrimFunc`, `PrimFuncCtx`, `Ctx.primFuncCtx` | `Op.ofVals argTys outTy interp` — a primitive function is just an op |
| `Ty.option`, `Ty.union`, `Ty.struct`, `Ty.m` | `Primitive` gained `arity` + `type : List Type → Type`; all four are ordinary context-supplied constructors |
| `PrimitiveCtx.M` / `monad`, built-in `Op.pure` / `Op.bind` in `OpCtx.get?` | user-declared `m` primitive + user-registered ops (see [Test/Monad.lean](Test/Monad.lean)) |
| `Term.mkStruct`, `Term.structProj` | ops, or avoided entirely — blocks take several named params, so loop state needs no product |
| `Term.recurse` | a block calling itself |
| `TermAbbrev*`, `TypeAbbrev*`, `Ty.abbrev` | blocks (term side); parametric prims (type side) |
| de Bruijn indices everywhere | `Scope α = List (String × α)`, lookup = **last** binding wins (`Scope.get?`) |

### The block IR

```lean
structure Instr (primCtx) where          -- an instruction is just a named term
  name : String
  value : Term primCtx

structure Block (primCtx) where
  params : VarCtx                        -- named binders (SSA `phi`)
  instrs : List (Instr primCtx)
  outTy  : Ty                            -- declared, so recursive calls type without inference
  result : Term primCtx
```

`BlockCtx.Valid` = names unique ∧ every `call` names a declared block. Self- and
forward-reference are *allowed* — that is the recursion.

**The one subtle rule:** instructions evaluate eagerly, in order; an op picks which operands to
evaluate (`Op.Body.next`). A recursive `call` in instruction position loops forever, so it must
sit inside a lazy operand (e.g. `ite`'s branch). This is the `evalTag`-continuation story and is
documented at the top of [Test/Block.lean](Test/Block.lean).

### Non-local exit

`Term.exit blockName value` unwinds to the **nearest enclosing call** of `blockName` and makes
`value` that call's result. Naming the current block is an early return (later instructions and
the block's `ret` term are skipped); naming an enclosing block breaks out of it — what the old
recursor stack allowed by calling an outer motive from an inner loop body.

Evaluation threads an `Outcome primCtx α = ok α | exit String (Val primCtx)`, which is the
`retBlock` continuation list reified as data. The recursive core is `Term.evalOutcome` /
`evalBlock` / `evalInstrs` / `evalListOutcome` / `evalBodyOutcome`; `Term.evalGo`, `evalList` and
`evalBody` are **value-level views** (`.bind Outcome.ok?`) so an escaped unwind reads as stuck
and every pre-existing value-level equation still holds unchanged. Use the `@[simp]` lemmas
`Term.evalGo_prim` / `_var` / `_op` / `_exit` where proofs used to `rw [Term.evalGo.eq_def]`.

Typing: `Term.hasType.exit` gives an exit **any** type (it never returns normally); its payload
must match the target block's declared `outTy`. Consequence for `UnifyType`: `inferType?` returns
`none` for `.exit`, so an exit in operand position can't be inferred — it can only be *checked*
against an expected type.

Worked examples: [Test/Exit.lean](Test/Exit.lean).

### Typing

`Term.hasType` has cases `prim | var | op | call | app`. `Block.instrsHaveType` threads the scope
through instructions; `Block.WellTyped` and `Ctx.WellTyped` sit on top. `Term.eq` now quantifies
over every `env` with `Env.Models varCtx` (was: `env.length = varCtx.length`).

### Induction ([Meta/Induction.lean](Meta/Induction.lean), rewritten, green)

The rule never mentioned `recurse` and still does not mention `call`:

```
P(0)   ∀ x y : Nat, succ x = y → P(x) → P(y)
--------------------------------------------
              ∀ n : Nat, P(n)
```

`natInductionChain` / `natInductionWithPredicate` are proved (axioms: `propext`,
`Classical.choice`, `Quot.sound` only). Because variables are named, the entire de Bruijn
`weakenTermAt` / `weaken` / `interp_weaken_*` layer is **deleted** and replaced by three
substitution lemmas plus a freshness side condition:

- `interp_instantiate` — binding `(name, t)` ≡ substituting `name := t`
- `interp_shadowed` — a binding for an unmentioned name is invisible
- `interp_instantiate_rename` — renaming the hole to a fresh `yName` and binding it ≡ instantiating

`SuccSpec` is now stated against `Term.op succName [t]` (not `Term.app (.primFunc ...)`) and is
generalised over `env` (needed because `Term.eq` quantifies over all models).

## What is left

### 1. `Meta/UnifyType.lean` — NOT ported (still the old de Bruijn version, does not compile)

This is the `has_type` tactic. It should get **simpler**, not harder:

- `Ty.primitiveNames` / `Term.primitiveNames`: mechanical, and `Ty.prim` now carries args.
- `inferType?`: drop `primFunc` / `mkStruct` / `structProj` / `recurse` cases; add
  ```lean
  | .call name args => (ctx.blockCtx.get? name).map Block.outTy
  ```
  (no operand inference needed for the result type — `outTy` is declared).
- `primFuncMatch?` — **delete**, primitive functions are ops now and go through `OpCtx.outTy?`.
- `varMatch?` — collapses to a `Scope.get? varCtx name = some ty` decidable check; all the
  index-shifting lemmas (`varMatch?_eq_none` etc.) shrink accordingly.
- `Ty.subst_nil` mutual block: three cases now (`var` / `prim` / `func`).
- The `recurse` case of `unifyTypeHasTypeGoals` and its soundness/completeness branches — delete;
  add a `call` case that checks `args` against `block.params` types.
- `reduce_unify_type`'s simp set references `Lib.Peano.natFuncCtx`, `natBinaryFunc`, `succFunc`,
  `PrimFunc.ty`, `PrimFunc.outTy` — all gone. Replace with `Lib.Peano.natOpCtx`, `Peano.opCtx`,
  `Op.natBinary`, `Op.natUnary`, `Op.ofVals`.

Also add a **block well-typedness checker** alongside it (the user asked for this explicitly):
a decision procedure producing `Block.WellTyped` / `Ctx.WellTyped` for a whole `BlockCtx`, so
programs don't need the hand-written derivations currently in `Test/Block.lean` and
`Test/Gauss.lean`.

### 2. Finish the induction tactic

`Meta/Induction.lean` currently stops at `natInductionWithPredicate` (the rule). The *tactic*
wrapper that finds `P` is not written yet. Plan (replaces old `findRecurseInPr` /
`abstractInitInPr` / `simpleInduction`):

```lean
-- Term has no DecidableEq (a `prim` carries an opaque Lean value), so compare only the
-- shapes an induction target can take. The old code did the same via `sameKnownTerm?`.
def sameTarget [Peano.Types primCtx] (a b : Term primCtx) : Bool  -- nat literals / vars
theorem sameTarget_eq : sameTarget a b = true → a = b

def Term.abstract (name : String) (target : Term primCtx) : Term primCtx → Term primCtx
def abstract (name) (target) : Pr (Term primCtx) → Pr (Term primCtx)
theorem instantiate_abstract :
  name ∉ varNames p → instantiate name target (abstract name target p) = p

def findCallArg? (blockName : String) : Pr (Term primCtx) → Option (Term primCtx)
def blockInduction (blockName succName) (hspec) : Tactic? ...
```

`findCallArg?` walks the goal for `.call blockName args` and returns `args.head?` — that is the
induction target, in place of the old "initial state of the `recurse` node".

### 3. Test files

`Test/Gauss/Rec.lean`, `Test/Gauss/SSA.lean`, `Test/Gauss/Simple.lean`, `Test/Peano.lean`,
`Lib/Peano.lean` are **still on disk, unported, and not in the lakefile**. They were left rather
than deleted because they hold real proof content (`Test/Gauss/Rec.lean` is the ~365-line Gauss
correctness proof by induction). Port them once UnifyType and the induction tactic are back:

- The Gauss *program* is already ported to blocks in [Test/Gauss.lean](Test/Gauss.lean) with
  typing derivations and `#guard` evaluation checks against `sumTo` and `n*(n+1)/2`. What is
  missing is the **inductive correctness proof**, which needs the tactic from (2).
- `Lib/Peano.lean` supplies the `SuccSpec` instance. Rewrite `succ_spec` against the new
  `SuccSpec` shape (op, env-generalised). The `succ` op already exists as
  `Op.natUnary Nat.succ` in `Peano.opCtx`.
- `Test/Gauss/SSA.lean` is subsumed: its struct-state loop is exactly `Test/Gauss.lean`'s
  `loop(i, acc)`. Delete rather than port, once you're satisfied nothing is lost.
- `Test/Gauss/Simple.lean` imports a `Lang.Simple` that never existed in this tree — it was dead
  before the refactor.

## Landmines

- **`ret` is a keyword token** (block syntax), so it cannot be used as a Lean structure-field name
  or bare identifier in any file importing `Zag.Syntax`. That is why `Block.result` is not called
  `Block.ret`. Same care applies to any new DSL keyword.
- Antiquotations can't be named after tokens: `$ret` fails to parse. Watch for this when
  extending [Zag/Syntax.lean](Zag/Syntax.lean).
- `Ty.type` is WF-recursive and `Type`-valued, so it does **not** reduce definitionally. Use
  `Ty.type_var` / `Ty.type_prim` / `Ty.type_func` / `Ty.type_prim_of_find` / `Ty.type_ground`.
  Anything whose *type* mentions it (e.g. a `Term.prim` holding a Lean function) is
  `noncomputable`, so it can't be `#eval`ed — prove instead.
- `Term.evalGo` is `partial_fixpoint`: `#eval` / `#guard` work, `decide` / `rfl` do not.
- `BlockCtx.Valid` by `by decide` gets stuck on `Block.callNames`. The working idiom is
  ```lean
  ⟨blocks, by refine ⟨by decide, ?_⟩
              simp [blocks, Block.callNames, Term.callNames, Term.nat, Term.ite]⟩
  ```
- Declare context-carrying definitions as `abbrev`, not `def`, or instance search fails on
  `ctx.primCtx` (e.g. `Peano.Types sumToCtx.primCtx`).
- Prefer `#guard` over `native_decide` — `AGENTS.md` forbids adding axioms, and `native_decide`
  pulls in `ofReduceBool`.

## Pre-existing breakage (not caused by this refactor)

`Meta/Induction.lean` and `Meta/UnifyType.lean` were **already stale at HEAD** (missing `.abbrev`
cases from commit `17dbad1`), and `Lib/Peano/Defs.lean` used `zagTerm` syntax without importing
`Zag.Syntax` — that import was added.

---

The small-step migration that supersedes the evaluator described above is planned in
[SMALLSTEP.md](SMALLSTEP.md).
