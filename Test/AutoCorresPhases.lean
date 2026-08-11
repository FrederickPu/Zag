import Test.AutoCorres.Upstream.Manifest
import Test.AutoCorres.Upstream.BinarySearch
import Test.AutoCorres.Upstream.Plus
import Test.AutoCorres.Upstream.Simple
import Test.AutoCorres.Upstream.MultByAdd
import Test.AutoCorres.Upstream.SkipHeapAbs
import Test.AutoCorres.Upstream.Struct
import Test.AutoCorres.Upstream.Chapter2_HoareHeap
import Test.AutoCorres.Kernel.HeapLift
import Test.AutoCorres.Kernel.WordAbstract
import Test.AutoCorres.Kernel.WordAbstractOperations
import Test.AutoCorres.Kernel.SimplConvRecursion
import Test.AutoCorres.UnsignedPipeline
import Test.AutoCorres.CParser.Lexer
import Test.AutoCorres.CParser.Preprocessor
import Test.AutoCorres.CParser.ParserActions
import Test.AutoCorres.CParser.ProgramAnalysis
import Test.AutoCorres.CParser.CallGraph
import Test.AutoCorres.CParser.MemoryLayout
import Test.AutoCorres.CParser.MemoryModel
import Test.AutoCorres.CParser.ScalarSimpl
import Test.AutoCorres.CParser.PhasePipeline.Basic
import Test.AutoCorres.Prog
import Test.AutoCorres.CParser.FixtureSmoke

/-!
# AutoCorres test root

This target follows the pinned upstream test-suite layout documented in
[`tools/autocorres/tests/README`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests/README).

The C parser smoke targets consume a compile-time embedded 68-file corpus with
67 C entries, so test execution does not depend on the working directory.
`Test.AutoCorres.Upstream.Manifest` distinguishes the 64-theory core regression
suite from three documentation theories, one whole-seL4 integration theory,
two excluded known failures, and the framework build target. Its Lean theorems
check counts and uniqueness; remote Git-tree equality remains a review-time
check. Fragments are never promoted to complete upstream coverage without the
original generated pipeline and theorem objective.
-/
