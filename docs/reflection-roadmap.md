# Verified Reflection Roadmap

The upstream-facing tests should resemble their Isabelle theories while all
generated phase artifacts remain kernel checked. These are the consolidated
infrastructure gaps exposed by the current ports.

## Generic Infrastructure

1. **Installed-file and AutoCorres commands**
   - Surface: `install_c_file simple from .arm files "simple.c"` followed by
     `autocorres [ts_force pure := max, ts_force nondet := gcd,
     unsigned_word_abs := gcd] simple`.
   - Output: source provenance, analyzed program, stable typed declarations,
     per-function phase certificates, metadata, adjacent `ChainCertificate`,
     final target, and `ac_corres` theorem.
   - User input: per-function phase policy and proofs for unsupported local
     rules. Fixture success should normally be discharged by computation.
   - Unlocks: concise `Plus`, `Struct`, `SkipHeapAbs`, and Chapter 2 setup.

2. **Indexed support and evidence elaboration**
   - Surface: `derive_autocorres_support`, with typed extension attributes for
     HeapLift expressions and updates.
   - Output: existing indexed SimplConv, LVE, HeapLift, WordAbstract, and
     TypeStrengthen support values. The elaborator must construct evidence, not
     inspect arbitrary functions and assume abstraction laws.
   - User input: unresolved abstraction, validity, state-map, and layout laws.
   - Include public identity builders for structural expression/update rewrites
     and constant guards.

3. **Loop, call, and SCC certificates**
   - Extend support synthesis to generated loops and direct calls, with callee
     certificates indexed by the exact predecessor endpoint.
   - Ordinary loops require test/body abstraction evidence. Recursive SCCs also
     require a measure or recursive certificate family.
   - Unlocks generated chains for `plus2`, `MultByAdd`, and `Simple.gcd`.

4. **Typed endpoint reification and phase policy**
   - Reify the actual HeapLift target as WordAbstract source syntax, then make
     TypeStrengthen consume the exact generated WordAbstract target.
   - Emit explicit translated, identity, or skipped artifacts per phase.
   - Honor per-function pure/nondeterministic, signed/unsigned abstraction, and
     skipped-HeapLift options in the generated chain rather than metadata only.

5. **Total-correctness weakest preconditions**
   - Surface: `wp (inv := invariant) (measure := measure)`.
   - Output: total Hoare/no-failure certificate.
   - User obligations: initialization, preservation, strict decrease, exit
     postcondition, and generated guard safety. The tactic must not replace the
     loop by its expected result.

6. **Nondeterministic monad extensionality**
   - Surface: `monad_eq using validity, empty_fail`.
   - Output: equality to `pure` or `gets` from exact functional validity,
     existence, no-failure, and state-preservation proofs.
   - Unlocks the remaining `Simple` `monad_to_gets` objective.

7. **Generated-target observation lemmas**
   - Add reusable `results` and `failed` lemmas for guarded sequencing, loops,
     calls, and catch. Expose expression evidence already produced inside
     WordAbstract transformation.
   - This removes low-level set-membership proofs from HeapLift and WordAbstract
     tests without weakening their behavior checks.

## Binary Search Track

1. **Faithful short-circuit lowering**
   - Add certified `&&` and `||` lowering with left-to-right evaluation,
     conditional right evaluation, integer `0`/`1` normalization, exact fault
     behavior, and source-region diagnostics.

2. **Pointer-array region contracts**
   - Represent caller-owned pointer spans with provenance, element layout,
     length, bounds, and non-overflowing address arithmetic.
   - Generate certified parameter-pointer indexing without pretending it is a
     statically allocated global array.

3. **Typed array HeapLift and unsigned abstraction**
   - Lift byte-memory reads to a typed read-only array view with validity guards.
   - Support unsigned casts, pointer arithmetic, midpoint division, and
     nondeterministic TypeStrengthen at the exact generated endpoint.

4. **Binary-search total proof**
   - Apply generic `wp` with the excluded-prefix/suffix invariant and a measure
     based on `r - l` while `found = 0`.
   - User obligations remain sortedness, midpoint bounds, invariant
     preservation, strict decrease, arithmetic safety, and the final membership
     equivalence.

Recommended order: installed-file command, indexed support, loops/calls,
endpoint reification, `wp`, then monad extensionality. Short-circuit lowering can
proceed independently; array contracts depend on it and on the generic support
and loop infrastructure.
