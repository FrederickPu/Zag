# Comparator Verification

This challenge uses [`leanprover/comparator`](https://github.com/leanprover/comparator),
not a project-local approximation of its checks.

## Modules

- `Main.lean` imports only trusted, non-ML IR and correspondence interfaces.
- `Challenge.lean` declares five dependent pass definitions and their correctness
  theorems with `sorry` bodies.
- `Solution.lean` imports `Main` plus `Lang.AutoCorres.ML.autocorres`, then
  independently supplies the pass implementations and proofs.
- `config.json` lists pass functions in `definition_names`, correctness results
  in `theorem_names`, and the permitted axioms.

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

The trusted closure contains no `Lang.AutoCorres.ML` module. Comparator checks
the exact dependent types, universe parameters, and safety levels of the five
solution definitions, then checks the dependent correctness theorems against
those solution definitions. The ML implementations and proof-producing code are
therefore kernel inputs in the solution environment, not trusted challenge code.

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
