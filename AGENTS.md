# Agent Guidelines

## Preserve Meaning

- Never make a downstream target pass by replacing its program, statement, semantics, or proof with a trivial equivalent.
- Keep examples and tests substantive. In particular, do not replace an algorithm with its expected result or turn a correctness theorem into reflexivity.
- A green build is not sufficient if behavior, proof strength, or test coverage has been weakened.
- When an architectural change conflicts with an existing semantic requirement, stop and explain the conflict to the user before changing downstream code.
- Escalate blockers and design tradeoffs. Do not silently choose a shortcut that changes what the repository specifies.

## Verification

- Compare substantial downstream edits against the previous implementation and confirm that the same behavior is still exercised.
- Treat unexpectedly large proof or test deletions as a regression unless the user explicitly approved them.
- Run `lake build Zag Lang Test Lib Meta` after repository-wide changes.
- Report any target that could not be preserved faithfully.

## Editing

- Prefer the smallest sound change.
- Preserve unrelated user changes.
- Follow the existing concise comment style.
- Do not add `sorry`, `admit`, or axioms to make proofs pass.
