# why program verification

Program verification is a much stronger alternative to testing. When you test a piece of code you sample from a distribution of expected inputs and check correctness on those samples. But many programs have arbitrary or even non-deterministic behavior (multithreading, for instance), and others take inputs of unbounded size, where no sampling distribution is obviously the right one — what *is* the correct probability distribution over lists? Testing can only ever cover the cases you thought to sample. Formal verification instead proves correctness for *all* inputs at once, and its cost is paid once up front rather than growing with the space of behaviors you are trying to cover.

# tldr

Zag lets you take a low-level program — C, LLVM IR, Zig — embed its language once, write programs in it, and prove properties about those programs in Lean. The distinctive part is *what you have to trust*. Every proof step is carried out by a `MetaProgram`: a piece of proof automation that comes packaged with a machine-checked proof of its own soundness. An unsound automation simply does not typecheck. So the only thing you trust by hand is the semantic specification of your target language — the meaning of its primitive types and operations. Everything built on top of that is checked by Lean.

```
┌───────────────────────────────────────────────────────────┐
│                  what you trust by hand                   │
│                                                           │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ PrimitiveCtx │  │ PrimFuncCtx  │  │   toTerm     │     │
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
          │  • MetaProgram         │  ← automations certify themselves
          └────────────────────────┘
                       │
                       ▼
              every proof is checked
```

# why lean

Lean is a dependently-typed programming language and proof assistant: you write ordinary programs and mathematical proofs in the same language, and the compiler checks the proofs. It has one of the fastest-growing formal mathematics libraries, and — because of recent "AI for math" efforts — a large amount of pretraining and RL has been directed at Lean code, making it ergonomic for both humans and AI agents to write proofs in.

# why not the existing approaches

To prove properties about programs, existing tools generally do one of two things:

1. **Transpile the source language into Lean** with an unverified translator (e.g. Aeneas). This is convenient, but the translator itself is trusted code — a bug in it silently invalidates every proof built on its output.

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

2. **Embed the program faithfully and use proof automation** to break goals into subgoals. This keeps the trusted base small, and Lean's kernel checks every finished proof, so no tactic can ever establish a false statement. But the automation *itself* has no guarantees: a tactic can loop forever, fail outright, or reduce your goal to subgoals that don't actually suffice — and extending it without quietly breaking those reductions is hard.

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

Zag avoids both failure modes. Against #1, you never hand-write a translator at all: you *declaratively specify* your language's semantics — its primitive types and operations, plus a structural lowering into Zag's core `Term` — and Zag supplies the single, shared evaluator that every proof runs against. There is no bespoke transpiler to get wrong, because the semantics *is* the specification. Against #2, the trust base stays just as small, but every automation is *total and self-certifying*. Instead of open-ended metacode, we reify propositions as a datatype `Pr` and automations as values of a type `MetaProgram` that carries, in its type, a proof that its reduction is valid:

```
source language          ┌──────────────────────────────────────┐
┌──────────┐             │            Zag                       │
│  program │───toTerm──> │                                      │
└──────────┘             │  ┌────────────┐  ┌───────────────┐   │
                         │  │ Term.eval  │  │ MetaProgram   │   │
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

```lean
structure MetaProgram primCtx primFuncCtx ctxTy ctxTerm goal where
  goals : List (Pr primCtx)
  prove : (∀ subgoal, subgoal ∈ goals →
    Pr.Provable ... subgoal) → Pr.Provable ... goal
```

A `MetaProgram` for a `goal` produces a list of sub`goals` together with `prove`: a proof that provability of all the subgoals implies provability of the goal. (`primCtx`/`primFuncCtx` are the language's primitive types and operations; `ctxTy`/`ctxTerm` are the ambient variable context.) Because `prove` is a *checked proof* the automation carries with it, you cannot construct a `MetaProgram` whose subgoals fail to imply its goal — it would not typecheck — and, being a plain total function, it always terminates. Lean's kernel already stops any tactic from proving something false; what `MetaProgram` adds is that every reduction is valid *by construction* and every automation is total, so the layer composes and extends without anyone re-auditing it by hand.

`MetaProgram`s compose. Given a program that emits subgoals, `refine` replaces each subgoal with another `MetaProgram`, and `iterate` applies a step under bounded fuel — building a tree whose leaves are closed by hand-written Lean proofs, with the soundness certificate threaded through automatically. Concretely, `iterate n step goal` unfolds as:

```
iterate n step goal  =
  if n = 0 then  step goal                          -- emit subgoals as-is
  else           (step goal).refine                 -- replace each subgoal:
                   fun g _ => iterate (n-1) step g  --   recurse with less fuel
```

So for `n = 3`, expanding one branch:

```
                  iterate 3 step goal
                          |
                     step goal
                   goals: [g₁, g₂, g₃]
                          |
              refine: replace each subgoal with iterate 2
                 /                   |                   \
        iterate 2 step g₁      (closed)           iterate 2 step g₃
         goals: [g₁₁]          goals: []           goals: [g₃₁, g₃₂]
              |                                       /              \
        refine g₁₁                              refine g₃₁       refine g₃₂
              |                                     |                |
      iterate 1 step g₁₁                   iterate 1 step g₃₁  iterate 1 step g₃₂
        goals: [g₁₁₁]                       goals: []           goals: []
              |                                 |                  |
           refine                            (leaf)             (leaf)
              |
      iterate 0 step g₁₁₁
        goals: []  ← fuel exhausted, leaf
```

After all branches close, the final program's `.goals` is `[] ++ [] ++ [] = []`. Then `toProvable program hempty` (where `hempty : program.goals = []`) collapses the tree:

```
toProvable program hempty :
  (∀ subgoal ∈ program.goals, Provable subgoal) → Provable goal
     ↑                                ↑
  trivially true               each leaf's prove
  (no subgoals)                threads upward through
                               refine's composition
```

Each `refine` composes the `prove` fields: the outer program's `prove` says "if my subgoals hold, I hold," and each inner program's `prove` says the same for its own subgoals. The fuel bound `n` guarantees termination — after `n` steps, remaining goals are emitted as-is — and `toProvable` checks the list is empty, converting the whole tree into a single proof.

# embedding a language

Zag is a *deep embedding*: programs and types are **data** — values of inductive `Term` and `Ty` types, syntax trees rather than Lean code:

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

Because a program is inert data, we can write Lean functions that take it apart — an evaluator `Term.eval`, a typing relation `hasType`, and automations that pattern-match on its structure. (In a *shallow* embedding the program dissolves into Lean and you can only reason about its translation, never about the program itself.)

To bring in a new language you supply three things. Take a small SSA language (similar to LLVM IR), in `Lang/SSA.lean`:

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

**2. The primitive semantics** — the built-in types and how operations evaluate:

```lean
abbrev natCtx : PrimitiveCtx := [("Nat", Nat), ("Bool", Bool)]
abbrev natFuncCtx : PrimFuncCtx natCtx :=
  [ ("add", natBinaryFunc Nat.add), ("sub", natBinaryFunc Nat.sub)
  , ("mul", natBinaryFunc Nat.mul), ("div", natBinaryFunc Nat.div) ]
```

**3. `toTerm`** — lower the AST into Zag's core `Term`, one clause per constructor. Most are direct: a source `ite` becomes a `Term.ite`, while the interesting clauses encode control flow: a loop lowers to `Term.recurse`, a `let_` extends the variable context, and a `yield` becomes a recursive call to the enclosing loop's motive. Programs can then be written with a custom `ssa%` syntax:

```lean
def lhsProgram (n : Nat) : Term natCtx :=
  (ssa% {
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
  } : SSAExpr natCtx).toTerm
```

The `ssa%` block is only sugar — `toTerm` erases it entirely, leaving a plain `Term` value. You can see the result directly (`#eval lhsProgram 3` prints the raw AST). For symbolic `n` it is the following, writing `NatTy` for `.prim "Nat"`, `stateTys` for the loop-state type `[NatTy, NatTy]`, and `Term.nat k` for a `Nat` literal:

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

So far `Pr` has just been "the type of propositions." Its design deserves a closer look, because it is what makes automation possible at all.

`Pr` is an *inductive datatype* of propositions — not an arbitrary Lean `Prop`, but a small fixed grammar:

```lean
inductive Pr (primCtx : PrimitiveCtx) where
  | eq (ctx : List Ty) (ty : Ty) : Term primCtx → Term primCtx → Pr primCtx  -- two terms equal at a type
  | hasType (ctx : List Ty) : Term primCtx → Ty → Pr primCtx                 -- a term has a type
  | and : Pr primCtx → Pr primCtx → Pr primCtx                               -- (also: or, implies)
  | forallTy   : Pr primCtx → Pr primCtx                                     -- ∀ over types
  | forallTerm : Pr primCtx → Pr primCtx                                     -- ∀ over terms
```

Because a `Pr` is *data* with finitely many shapes, a `MetaProgram` can pattern-match on it and take it apart — turn a `hasType` of an `ite` into three smaller `hasType`s, peel a `forallTerm`, split an `and`. You cannot case-analyse an arbitrary Lean `Prop` like that. Restricting propositions to this grammar is exactly the price that buys the ability to automate reasoning over them.

A `Pr` is only syntax. Its *meaning* is a genuine Lean proposition, assigned by `Pr.interp`, which just reads each shape off as the corresponding logical connective:

```lean
Pr.interp ... (.eq ctx ty x y)  =  «x and y are typed-equal at ty»
Pr.interp ... (.and p q)        =  Pr.interp ... p ∧ Pr.interp ... q
Pr.interp ... (.forallTerm p)   =  ∀ x, Pr.interp ... p
```

And `Pr.Provable p` is nothing more than *holding a Lean proof of `Pr.interp p`*:

```lean
inductive Pr.Provable ... (p : Pr primCtx) : Prop
  | ofProof (proof : Pr.interp ... p)
```

That is the honest bottom line. Proving a `Pr` is *just* proving its interpretation as an ordinary Lean proposition. A `MetaProgram` never proves anything you could not have proved by hand — it only lightens the burden, rewriting one `Pr` into smaller `Pr`s whose interpretations are easier to establish, until the leaves are plain Lean proofs.

**The Gauss example.** The theorem "the loop summing `1 + 2 + ... + n` returns `n * (n + 1) / 2`" is the `Pr` that equates two programs — the loop `lhsProgram n` and the closed form `rhsTerm n`, at type `Nat`:

```lean
def gaussStatement (n : Nat) : Pr natCtx :=
  .eq [] NatTy (lhsProgram n) (rhsTerm n)
```

Its interpretation `Pr.interp ... (gaussStatement n)` unfolds to two familiar demands: that both programs are well-typed, and that they evaluate to the same `Nat`. The typing demand is handled by `unifyType` — a `MetaProgram` that decomposes `hasType` goals by the structure of the term (e.g. `hasType ctx (ite c t e) ty` splits into `c : Bool`, `t : ty`, `e : ty`):

```lean
theorem bodyTerm_hasType : Term.hasType natCtx natFuncCtx bodyCtx bodyTerm NatTy := by
  let program := iterate 20 (fun g => unifyType g) (.hasType bodyCtx bodyTerm NatTy)
  have hclosed : program.goals = [] := by native_decide
  have hprov := toProvable program hclosed
  ...
```

Here is the goal tree that `iterate` builds for `bodyTerm` — the loop body, an `ite` on a comparison:

```
            hasType bodyCtx bodyTerm NatTy
                        |
                   unifyType
                        |
          ┌─────────────┼─────────────┐
          |             |             |
  hasType cond    hasType yield   hasType acc
   : Bool          : NatTy         : NatTy
          |             |             |
       unifyType     unifyType     unifyType
          |             |             |
    ┌─────┴─────┐  (app recurse)  (app structProj)
    |           |       |             |
  hasType    hasType   ...           ...
  lhs :Nat  rhs :Nat
    |           |
 (app proj)  (nat 0)
    |           |
  ┌─┴──┐       ok
  |    |
hasType hasType
var 0  structProj
 :Σ    :Nat→Σ
  |      |
  ok      ok
```

Each leaf marked ok is resolved by `unifyType` matching against `primFuncMatch?`, `varMatch?`, or a known constructor type. After 20 fuel steps `native_decide` confirms the goal list is empty, and `toProvable` collapses the tree into a single proof. The evaluation demand is the real mathematics — an ordinary Lean proof that the loop computes the closed form — and, crucially, it is a proof about the loop's *real executable semantics*, not about some unverified tool's translation of it.

Under the hood, `gaussStatement n` is obtained by instantiating a *predicate* — a `Pr` with a hole for the input:

```lean
def gaussPredicate : Pr natCtx :=
  .eq [] NatTy
    (.recurse NatTy (.var 0) bodyTerm)           -- loop with input as var 0
    (.app (.primFunc "div")                       -- closed form with var 0
      [(.app (.primFunc "mul")
        [(.var 0), (.app (.primFunc "add") [(.var 0), Term.nat 1])]),
       Term.nat 2])

-- gaussStatement n = substitute nat(n) for var 0:
theorem gaussStatement_eq (n : Nat) :
    gaussStatement n = Pr.MetaProgram.instantiateTermAt 0 gaussPredicate (Term.nat n)
```

So `gaussStatement n` is literally `gaussPredicate` with `Term.nat n` plugged in for `var 0`. The proof proceeds by *natural-number induction on the predicate itself*: first prove the predicate holds at `0`, then prove it lifts from any `k` to `k + 1`. The full proof tree:

```
 gaussStatement n
 = .eq [] NatTy (lhsProgram n) (rhsTerm n)
      which is:  instantiateTermAt 0 gaussPredicate (nat n)
           |
 gaussInductionProgram n                    ← natInductionWithPredicate
           |                                    instantiates at (nat n)
      ┌────┴────────────────────────────────┐
      |                                     |
 BASE: gaussStatement 0               STEP: natStepGoal 0 gaussPredicate
 = .eq [] NatTy                          = .forallNat 0 (.forallNat 1
     (lhsProgram 0)                          (.implies (isSuccPr 0)
     (rhsTerm 0))                              (.implies P[1] P[0])))
      |                                     |
      |  Pr.interp gives:                 Pr.interp gives:
      |  1. hasType (lhsProgram 0) NatTy    ∀ x y : Nat,
      |  2. hasType (rhsTerm 0) NatTy       isSuccPr(x,y) →
      |  3. lhsProgram 0 ⟶ Val.nat 0        P[x] → P[y]
      |     rhsTerm 0 ⟶ Val.nat 0           where P[k] = gaussPredicate[k]
      |                                     |
      |  (loop with init=0 never enters     natStepGoal_of_literal_step
      |   the body; closed form 0*1/2=0)         |
      |                                     ┌────┴────────────┐
      ok                                    |                 |
                                    for each literal k:   gaussPredicate_congr
                                    gaussStatement k →    (swap well-typed term
                                    gaussStatement(k+1)   for the literal it
                                         |                evaluates to)
                                    gaussLiteralStep            |
                                      [unfold loop body   term.eval = k → P[k]
                                       one iteration,     term.eval = k+1 → P[k+1]
                                       show it matches         |
                                        the closed form]       ok  ok
                                         |
                                         ok
```

At the base, both sides of `.eq` evaluate to `Val.nat 0` — the loop with `init=0` never enters the body (the condition `0 > 0` is false), and the closed form `0 * 1 / 2 = 0`. At each induction step, `gaussLiteralStep` unfolds exactly one loop iteration: given that `lhsProgram k` evaluates to `k*(k+1)/2` (extracted from the inductive hypothesis via `rhsTerm_eval_rhs`), it shows that `lhsProgram (k+1)` evaluates to `(k+1)*(k+2)/2` by chaining `cond_eval_succ` (the condition is true when `i = k+1`) and `step_eval_succ` (the body adds `k+1` to the accumulator). `gaussPredicate_congr` handles the bookkeeping of swapping a well-typed term `t` for the concrete `nat k` it evaluates to, so the step proved at the literal level lifts back to the term-quantified `natStepGoal`. Every edge carries a `prove` certificate; the whole tree collapses into a single `Pr.Provable natCtx natFuncCtx [] [] (gaussStatement n)`.

# what you trust

That closes the loop on the opening promise. The trust base is exactly the language specification — `PrimitiveCtx` and `PrimFuncCtx`, the meaning of the primitives. The `MetaProgram` layer above it, `unifyType` today and more automation as the framework grows, is *total and self-certifying*: its `prove` field is a reduction Lean checks, so a broken automation is a compile-time type error rather than an unreliable tactic you debug at proof time. (Soundness — no false theorems — is guaranteed for everything by Lean's kernel regardless; what this layer adds is automation you can trust to actually work.) What is left for a human is only the genuine mathematical content — and even there, the surrounding framework guarantees you are proving something about the actual program.
