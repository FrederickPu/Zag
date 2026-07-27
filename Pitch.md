# why program verification

Program verification is a much stronger alternative to testing. When you test a piece of code you sample from a distribution of expected inputs and check correctness on those samples. But many programs have arbitrary or even non-deterministic behavior (multithreading, for instance), and others take inputs of unbounded size, where no sampling distribution is obviously the right one — what *is* the correct probability distribution over lists? Testing can only ever cover the cases you thought to sample. Formal verification instead proves correctness for *all* inputs at once, and its cost is paid once up front rather than growing with the space of behaviors you are trying to cover.

# tldr

Zag lets you take a low-level program — C, LLVM IR, Zig — embed its language once, write programs and propositions in it, and prove them in Lean. The distinctive part is *what you have to trust*. Every proof step is represented by a `Refinement`: proof automation packaged with a machine-checked certificate that its subgoals imply its goal. An unsound refinement does not typecheck. The hand-written trust boundary is the target language's semantic specification: its primitive types and operations, and its lowering to Zag's core language. Everything above that boundary is checked by Lean.

```
┌───────────────────────────────────────────────────────────┐
│                  what you trust by hand                   │
│                                                           │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ PrimitiveCtx │  │ PrimFuncCtx  │  │   toTerm?    │     │
│  │              │  │              │  │              │     │
│  │ types and    │  │ operations   │  │ source AST → │     │
│  │ their Lean   │  │ and how they │  │ Zag's core   │     │
│  │ meaning      │  │ evaluate     │  │ Term type    │     │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘     │
│         │                 │                 │             │
│         └────────┬────────┘                 │             │
│                  │                          │             │
│          semantic spec              structural rule       │
│       (what the language            (source→Term,         │
│        means in Lean)                one clause per       │
│                                      constructor)         │
└──────────────────────┬────────────────────────────────────┘
                       │
                       ▼
          ┌────────────────────────┐
          │   Zag's shared kernel  │
          │                        │
          │  • Term.eval           │  ← one evaluator for everything
          │  • Term.hasType        │
          │  • Pr.interp           │  ← propositions are data
          │  • Refinement          │  ← automations certify themselves
          └────────────────────────┘
                       │
                       ▼
              every proof is checked
```

# why lean

Lean is a dependently-typed programming language and proof assistant: you write ordinary programs and mathematical proofs in the same language, and the compiler checks the proofs. It has one of the fastest-growing formal mathematics libraries, and — because of recent "AI for math" efforts — a large amount of pretraining and RL has been directed at Lean code, making it ergonomic for both humans and AI agents to write proofs in.

# why not the existing approaches

To prove properties about programs, existing tools generally do one of two things:

1. **Transpile the source language into Lean** with an unverified translator (e.g. [Aeneas](https://github.com/AeneasVerif/aeneas)). This is convenient, but the translator itself is trusted code — a bug in it silently invalidates every proof built on its output.

```
source language             Lean
┌──────────┐    ┌───────────┐    ┌──────────┐
│  program │───>│translator │───>│  program │───> proofs
└──────────┘    └───────────┘    └──────────┘
                      ▲
                 trusted: a bug here
                 silently invalidates
                 every proof
```

2. **Embed the program faithfully and use proof automation** to break goals into subgoals. This keeps the trusted base small, and Lean's kernel checks every finished proof, so no tactic can ever establish a false statement. But the automation *itself* has no guarantees: a tactic can loop forever, fail outright, or reduce your goal to subgoals that don't actually suffice — and extending it without quietly breaking those reductions is hard (cf. [AutoCorres](https://isa-afp.org/entries/AutoCorres2.html)).

```
source language                Lean
┌──────────┐   ┌───────────┐   ┌─────────────────┐
│  program │──>│ embed into│──>│proof automation │──> proofs
└──────────┘   │ Lean      │   └─────────────────┘
               └───────────┘           ▲
                                 unverified: can
                                 loop, fail, or
                                 emit subgoals
                                 that don't suffice
```

Zag avoids both failure modes. Against #1, lowering is part of the language specification rather than an opaque external translation step: primitive semantics and structural lowering into Zag's core `Term` are stated explicitly, and Zag supplies the shared evaluator used by every proof. Against #2, the trust base stays small, but every automation is *total and self-certifying*. Propositions are reified as `Pr` values and proof reductions as `Refinement` values ([`Zag/Meta.lean`](Zag/Meta.lean)) carrying a proof that their subgoals suffice:

```
source language          ┌──────────────────────────────────────┐
┌──────────┐             │            Zag                       │
│  program │──toTerm?──> │                                      │
└──────────┘             │  ┌────────────┐  ┌───────────────┐   │
                         │  │ Term.eval  │  │ Refinement    │   │
                         │  │            │  │               │   │
                         │  │ one shared │  │ total, self-  │   │
                         │  │ evaluator  │  │ certifying:   │   │
                         │  │ for every  │  │ prove is a    │   │
                         │  │ proof      │  │ checked proof │   │
                         │  └────────────┘  └───────────────┘   │
                         │         ▲                 ▲          │
                         │    language spec    automation layer │
                         │   (trusted once)   (trusted never)   │
                         └──────────────────────────────────────┘
                                   │
                                   ▼
                          Lean checks every proof
                          (no false theorems, ever)
```

## Certified tactics (the point)

Usual tactics can spit out subgoals that do not actually imply the goal. Zag packages every automation step as a **`Refinement`**: "here are the subgoals, plus a *checked* proof that they suffice."

```lean
structure Refinement ... (goal : Pr E) where
  goals : List (Pr E)   -- what is left to prove
  prove : (all goals provable) → goal provable   -- Lean checks this
```

A **`Tactic`** is just a function `goal → Refinement goal`. It may close the goal (`goals = []`), split it, or get stuck. Because `prove` is typed, an unsound split does not compile.

Tactics compose like a proof tree. One step turns a goal into subgoals; the next step works on each of those:

```
        G                         -- original goal
     /  |  \
   t₁  t₂  t₃                     -- after tactic step
   |        |
  t₁₁      t₃₁  t₃₂               -- after another step
   ✓        ✓    ✓                -- leaves closed
```

When every leaf is closed, the `prove` certificates compose upward into a single proof of `G` (`toProvable` in [`Zag/Meta.lean`](Zag/Meta.lean)). Bounded `iterate` is the usual "apply this tactic up to *n* times" driver — same idea as a tactic script, but every edge of the tree is certified.

# embedding a language


Zag is a *deep embedding*: programs and types are **data** — values of inductive `Term` and `Ty` types, syntax trees rather than Lean code ([`Zag/Data.lean`](Zag/Data.lean)):

```lean
inductive Ty where
  | prim   : String → Ty        -- "Nat", "Bool", ...
  | struct : List Ty → Ty       -- tuples / records
  | func   : List Ty → Ty → Ty  -- function types
  -- also: var, option, union

inductive Term (primCtx : PrimitiveCtx) where
  | prim (ty : Ty) : Ty.type primCtx ty → Term primCtx  -- literal value
  | var : Nat → Term primCtx                            -- de Bruijn variable
  | app : Term primCtx → List (Term primCtx) → Term primCtx
  | ite : Term → Term → Term → Term
  | recurse (resultTy : Ty) (initState body : Term) : Term  -- bounded loop
  -- also: primFunc, primEq/primLt/primGt, mkStruct, structProj
```

Because a program is inert data, we can write Lean functions that take it apart — an evaluator `Term.eval` ([`Zag/Theory.lean`](Zag/Theory.lean)), a typing relation `hasType` ([`Zag/Data.lean`](Zag/Data.lean)), and automations that pattern-match on its structure. (In a *shallow* embedding the program dissolves into Lean and you can only reason about its translation, never about the program itself.)

To bring in a new language you supply three things. Take a small SSA language (similar to LLVM IR), in [`Lang/SSA.lean`](Lang/SSA.lean):

**1. The raw syntax** — the AST (`SSAExpr`/`SSAValue`) with `let_`, `ite`, loops and `yield`:

```lean
mutual
inductive SSAExpr primCtx where
  | ret (value : SSAValue primCtx)
  | let_ (name : String) (value : SSAValue primCtx) (next : SSAExpr primCtx)
  | ite (cond : SSAValue primCtx) (thenExpr elseExpr : SSAExpr primCtx)
  | yield (next : List (SSAValue primCtx))
end
```

**2. The primitive semantics** — the built-in types ([`PrimitiveCtx`](Zag/Data.lean)) and how operations evaluate ([`PrimFuncCtx`](Zag/Data.lean)):

```lean
abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add), ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul), ("div", natBinaryFunc Nat.div) ]
```
([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean))

**3. A `Language` instance** ([`Zag/Meta/Language.lean`](Zag/Meta/Language.lean)) — `toTerm?` lowers the AST into Zag's core `Term`. Most clauses are direct: a source `ite` becomes a `Term.ite`, while the interesting clauses encode control flow: a loop lowers to `Term.recurse`, a `let_` extends the variable context, and a `yield` becomes a recursive call to the enclosing loop's motive. The result is an `Option`, so malformed control flow is rejected rather than assigned an arbitrary core meaning. A reflecting language also supplies `ofTerm`, allowing core tactic subgoals to be quoted back into source propositions:

```lean
instance : Language.Reflects natCtx (SSAExpr natCtx) where
  toTerm? expr := SSAExpr.toTerm? expr {}
  ofTerm term := .ret (.raw term)
  toTerm?_ofTerm _ := rfl
```

Programs can then be written with the custom `ssa%` syntax while retaining their SSA type:

```lean
def lhsSSA (n : Nat) : SSAExpr natCtx :=
  ssa% {
    zero := prim(0 : Nat);
    one := prim(1 : Nat);
    start := prim(n : Nat);
    acc0 := prim(0 : Nat);
    loop (i : Nat := start, acc : Nat := acc0) : Nat {
      cond := gt i zero;
      if cond {
        nextI := call sub [i, one];
        nextAcc := call add [acc, i];
        yield nextI, nextAcc
      } else {
        acc
      }
    }
  }

theorem lhsSSA_lowers (n : Nat) :
    Language.toTerm? (lhsSSA n) = some (loopTerm n 0) := rfl
```
([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean))

The `ssa%` block remains surface syntax until `toTerm?` succeeds. For symbolic `n`, the resulting core term is the following, writing `NatTy` for `.prim "Nat"`, `stateTys` for the loop-state type `[NatTy, NatTy]`, and `Term.nat k` for a `Nat` literal:

```lean
.recurse NatTy
  (.app (.mkStruct stateTys) [Term.nat n, Term.nat 0])                 -- init state (i := n, acc := 0)
  (.ite (.primGt (.app (.structProj stateTys 0) [.var 0]) (Term.nat 0)) -- cond: i > 0
    (.app (.var 1)                                                      -- yield: recurse on new state
      [.app (.mkStruct stateTys)
        [ .app (.primFunc "sub") [.app (.structProj stateTys 0) [.var 0], Term.nat 1]   -- i - 1
        , .app (.primFunc "add") [.app (.structProj stateTys 1) [.var 0],                -- acc + i
                                  .app (.structProj stateTys 0) [.var 0]] ]])
    (.app (.structProj stateTys 1) [.var 0]))                           -- else: acc
```

The whole loop is one `recurse` over a struct-packed state `(i, acc)`; `.var 0` is the current state, `.var 1` the recursive continuation (the loop's motive), and `structProj 0`/`1` project out `i`/`acc`. The comfortable surface syntax and this inert tree are *the same object* — which is exactly what lets Zag evaluate it and prove things about it.

# propositions, and what it means to prove one

A goal in Zag is not a free-form Lean `Prop`. It is a small piece of **data** (`Pr`) that says something about programs — usually “these two programs are equal at this type.” That restriction is what lets tactics pattern-match on goals and rewrite them safely.

## Write programs with macros, state goals as equalities

Programs are written with surface macros, not raw constructors ([`Test/Gauss/Rec.lean`](Test/Gauss/Rec.lean)):

```lean
-- recursive sum:  n + (n-1) + … + 1
def lhsProgram (n : Nat) : Term natCtx :=
  term% { recurse Nat from nat(n) { raw(bodyTerm) } }

-- closed form:  n * (n + 1) / 2
def rhsTerm (n : Nat) : Term natCtx :=
  term% {
    call func(div) [
      call func(mul) [nat(n), call func(add) [nat(n), nat(1)]],
      nat(2)
    ]
  }
```

The claim we want is ordinary English:

> For every `n`, the loop and the closed form compute the same `Nat`.

In Zag that is one equality goal:

```lean
def gaussStatement (n : Nat) : Pr (Term natCtx) :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)
  --   ^^ empty binder context
  --      ^^^^^ both sides have type Nat
  --            ^^^^^^^^^^^^^^^^^^^^^^^^^^ the two programs
```

Read `.eq [] NatTy lhs rhs` as: **`lhs = rhs` at type `Nat`**.

You can state the same goal over **SSA** surface syntax ([`Test/Gauss/SSA.lean`](Test/Gauss/SSA.lean)):

```lean
def lhsSSA (n : Nat) : SSAExpr natCtx :=
  ssa% {
    zero := prim(0 : Nat);
    one  := prim(1 : Nat);
    start := prim(n : Nat);
    acc0 := prim(0 : Nat);
    loop (i : Nat := start, acc : Nat := acc0) : Nat {
      cond := gt i zero;
      if cond {
        nextI   := call sub [i, one];
        nextAcc := call add [acc, i];
        yield nextI, nextAcc
      } else {
        acc
      }
    }
  }

def gaussGoalSSA (n : Nat) : Pr (SSAExpr natCtx) :=
  .eq [] NatTy (lhsSSA n) (.ret (.raw (rhsTerm n)))
```

Lowering the SSA goal recovers the core one:

```lean
theorem gaussGoalSSA_toTerm (n : Nat) :
    (gaussGoalSSA n).toTerm? = some (gaussStatement n) := rfl
```

So: **write in `ssa%` / `term%`, prove an equality, transport along lowering.**

## What “proved” means

A `Pr` is only syntax. Its **meaning** is a real Lean proposition (`Pr.interp`):

| goal shape | means |
| --- | --- |
| `.eq … ty lhs rhs` | both sides type at `ty` and evaluate to the same value |
| `.hasType … e ty` | expression `e` has type `ty` |
| `.and p q` | both `p` and `q` |
| `.forallTerm p` | `p` holds for every term (bound as a variable) |

`Pr.Provable p` means: we have a Lean proof of that meaning. Nothing more exotic — refinements only break a checked goal into smaller checked goals.

For Gauss, `.eq [] NatTy (lhsProgram n) (rhsTerm n)` therefore asks for:

1. both programs are well-typed at `Nat`, and  
2. they evaluate to the same number.

(1) is mostly structural; Zag’s `unifyType` tactic decomposes typing goals. (2) is the real math (induction on `n`).

## Typing automation (sketch)

```lean
-- “bodyTerm has type Nat” → subgoals for the if-condition and both branches
let refinement := Tactic.iterate 20
  (Pr.TypeUnification.unifyType (ctx := peanoCtx) …)
  (.hasType bodyCtx bodyTerm NatTy)
```

```
hasType body : Nat
        │ unifyType
   ┌────┼────┐
cond:Bool  then:Nat  else:Nat
   │         │         │
  …        …         ok
```

When every leaf closes, `Refinement.toProvable` collapses the tree into one proof.

## How the Gauss proof is structured

We prove `gaussStatement n` by **induction on `n`**:

```
gaussStatement n          -- loop(n) = n*(n+1)/2
        │
   ┌────┴────┐
 base      step
   │         │
 n = 0    assume k, prove k+1
 both sides    one loop iteration
 evaluate to 0   matches closed form
```

- **Base:** loop from `0` never enters the body; closed form is `0`.
- **Step:** one unfold of the loop body turns the IH for `k` into the claim for `k+1`.

Mechanically this is packaged as a `Refinement` tree ([`Meta/Induction.lean`](Meta/Induction.lean), [`Test/Gauss/Rec.lean`](Test/Gauss/Rec.lean)): each node carries a checked `prove` certificate; when the leaves close, the tree collapses to `Pr.Provable … (gaussStatement n)`.

A reusable form is a *predicate* with a hole for the input (same equality, `n` as `var(0)`):

```lean
-- P[n]  ≜  loop(n) = n*(n+1)/2
def gaussPredicate : Pr (Term natCtx) :=
  .eq [] NatTy
    (term% { recurse Nat from var(0) { raw(bodyTerm) } })
    (term% {
      call func(div) [
        call func(mul) [var(0), call func(add) [var(0), nat(1)]],
        nat(2)]
    })

-- gaussStatement n  =  P with var(0) := nat(n)
```

## Under the hood (optional)

`Pr` is a fixed inductive type ([`Zag/Data.lean`](Zag/Data.lean)): equality, typing, connectives, quantifiers. Core goals use `Pr (Term …)`; surface languages use `Pr (SSAExpr …)`. Finite grammar ⇒ tactics can case-split; arbitrary Lean `Prop` cannot. `Language.Provable` = successful lowering + `Pr.Provable` on the core goal.

# what you trust

The trust base is the language specification: types, primitive ops, and lowering into core `Term`. The `Refinement` layer (including `unifyType` and induction) is total and self-certifying — a broken reduction is a type error. Lean’s kernel rules out false theorems; what remains for humans is the mathematical content about the real program semantics.

# example: AutoCorres-style pipeline

Zag can host a full **lift-then-abstract** chain in the spirit of [AutoCorres](https://trustworthy.systems/projects/OLD/autocorres/): embed a small imperative language, lower control flow to SSA, then rewrite leaves (words, heaps) while composing correspondence proofs.

```
imperative source          SSA (locals)           abstract SSA
┌────────────────┐        ┌──────────────┐       ┌──────────────┐
│  x = x + y;    │ ─lift─▶│  named x, y  │ ─WA──▶│  Nat arithmetic│
│  if (x < y) …  │        │  word ops    │       │  (+ guards)   │
└────────────────┘        └──────┬───────┘       └──────────────┘
                                 │
                                 ▼ eval
                            concrete check
                         e.g. (3,4) ↦ (7,4)
```

Passes in the chain (each is a plain translation plus a separate correctness theorem):

| stage | role |
| --- | --- |
| L1 | exceptions → flagged control flow |
| L2 | packed state → named locals |
| HL | byte heap → typed heaps + validity |
| WA | machine words → `Nat` / `Int` |
| TS | drop residual failure where impossible |

End-to-end sketches live under [`Lang/Simple/`](Lang/Simple/) and [`Test/AutoCorres.lean`](Test/AutoCorres.lean). The pitch point is the same as everywhere else: one shared evaluator, surface goals as data, and every automation step a checked `Refinement` — including the composed pipeline proof.
