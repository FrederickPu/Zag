# Comparator Verification

This challenge uses [`leanprover/comparator`](https://github.com/leanprover/comparator),
not a project-local approximation of its checks.

## Modules

- `Main.lean` imports only trusted, non-ML IR and correspondence interfaces.
- `Challenge.lean` declares the five phase definitions, both executable
  adapters, closed TypeStrengthen, and the direct unsigned translator with
  protocol `sorry` bodies. Its theorems check phase correctness, adapter and
  TypeStrengthen exactness, direct reduction pins, and final correspondence.
- `Solution.lean` imports `Main` plus `Lang.AutoCorres.ML.autocorres`, then
  independently supplies the pass implementations and proofs.
- `config.json` lists all ten checked functions in `definition_names`, all
  twelve checked theorems in `theorem_names`, and the permitted axioms.

`Solution` must not import `Challenge`. Comparator separately builds and exports
both modules, verifies that every declaration used by each theorem statement is
identical, checks the solution's transitive axioms, and replays it in the Lean
kernel. The `sorry` values in `Challenge` therefore establish statements only;
they are not available to the independently built solution.

## Trust Boundary

The transitive imports of `Challenge`, `Main.lean`, `lakefile.toml`, and
`lean-toolchain` are trusted inputs. Evaluate a candidate in a clean checkout
where it can replace only `Solution.lean`. Do not compile adversarial solution
files before invoking Comparator in that checking environment.

The trusted closure contains no `Lang.AutoCorres.ML` module. `Main` imports the
trusted phase and pipeline interfaces, including the source-indexed adapter
support and `Pipeline.UnsignedTranslation`; that output stores generated
certificates, while its final `ChainCertificate` is derived by the trusted
pipeline interface from those artifacts, canonical maps, and canonical
preconditions. Comparator checks exact dependent types, universe parameters,
and safety levels for the phase, adapter, closed TypeStrengthen, and direct
translation definitions. It also checks the phase correctness theorems, adapter
and TypeStrengthen exactness theorems, the direct artifact and derived-chain
specification, and the final `acCorres` projection. The ML implementations and
proof-producing code are kernel inputs in the solution environment, not trusted
challenge code.

The direct unsigned signature accepts only predecessor-indexed support: SIMPL
support, LVE support for the generated SIMPL target, initial locals and state
map, HeapLift support for the selected generated LVE term, Heap-to-Word support
for the generated heap target, and Word-to-TypeStrengthen support for the
generated word target. It has no callback, selected endpoint equality, supplied
chain, arbitrary precondition, `Except`, or success premise. This is the first
closed unsigned guarded-read path only.

Comparator's definition-hole guarantee does not prove that a semantically valid
implementation is the intended algorithm. In particular, failure-conditional
relations can admit degenerate failing targets. Production evaluation must also
review or behaviorally test definition-hole outputs, as Comparator's own
definition-hole documentation requires.

Comparator requires compatible `landrun` and `lean4export` binaries in `PATH`.
Run it as an unprivileged user on Linux with the sandbox invocation recommended
by Comparator's README. Optionally enable nanoda in `config.json` and provide
`nanoda_bin` to replay with a second kernel.

From the repository root, after installing compatible tools:

```text
lake env comparator Comparator/AutoCorres/config.json
```

This Windows development workspace can build both modules independently, but it
cannot run Comparator's Linux `landrun` sandbox.
