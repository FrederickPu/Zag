import Lib.PeanoHeap
import Meta.Peano.Eval
import Meta.Induction
import Meta.UnifyType

/-!
Prelude for the AutoCorres example analogues.

Each module below mirrors one upstream `tools/autocorres/tests/examples/*.thy` theory with a
small block-IR program over `PeanoHeap` and a checked typing context. Everything they use is
general purpose and lives outside `Test/`: `mkCtx` and `valid_blocks` in `Lib/PeanoHeap.lean`,
`evaluates` in `Meta/Eval.lean`, Peano control-flow tactics in `Meta/Peano/Eval.lean`,
`typecheck_ctx` in `Meta/UnifyType.lean`, and the reflected induction rule in
`Meta/Induction.lean`.
-/
