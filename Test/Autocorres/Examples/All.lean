import Test.Autocorres.Examples.ACRename
import Test.Autocorres.Examples.Alloc
import Test.Autocorres.Examples.BinarySearch
import Test.Autocorres.Examples.CList
import Test.Autocorres.Examples.ConditionGuard
import Test.Autocorres.Examples.FactorialTest
import Test.Autocorres.Examples.FibProof
import Test.Autocorres.Examples.FunctionInfoDemo
import Test.Autocorres.Examples.HeapWrap
import Test.Autocorres.Examples.Incremental
import Test.Autocorres.Examples.IsPrime
import Test.Autocorres.Examples.Kmalloc
import Test.Autocorres.Examples.ListRev
import Test.Autocorres.Examples.Memcpy
import Test.Autocorres.Examples.Memset
import Test.Autocorres.Examples.MultByAdd
import Test.Autocorres.Examples.Plus
import Test.Autocorres.Examples.Quicksort
import Test.Autocorres.Examples.SchorrWaite
import Test.Autocorres.Examples.Simple
import Test.Autocorres.Examples.Str2Long
import Test.Autocorres.Examples.Suzuki
import Test.Autocorres.Examples.Swap
import Test.Autocorres.Examples.TraceDemo
import Test.Autocorres.Examples.WordAbs
import Test.Autocorres.Examples.TypeStrengthenTricks

namespace Zag.Test.Autocorres.Examples

open Zag.Lib.PeanoHeap

abbrev autocorresBlocks : BlockCtx.Raw heapCtx :=
  plusBlocks ++ multByAddBlocks ++ factorialBlocks ++ fibBlocks ++ simpleBlocks ++
  isPrimeBlocks ++ binarySearchBlocks ++ memcpyBlocks ++ memsetBlocks ++ quicksortBlocks ++
  swapBlocks ++ allocBlocks ++ kmallocBlocks ++ listBlocks ++ listRevBlocks ++ schorrWaiteBlocks ++
  heapWrapBlocks ++ conditionGuardBlocks ++ suzukiBlocks ++ traceDemoBlocks ++ str2longBlocks ++
  renameBlocks ++ functionInfoBlocks ++ typeStrengthenBlocks ++ wordAbsBlocks

theorem autocorresBlocksValid : BlockCtx.Valid autocorresBlocks := by
  valid_blocks [autocorresBlocks, plusBlocks, multByAddBlocks, factorialBlocks, fibBlocks,
    simpleBlocks, isPrimeBlocks, binarySearchBlocks, memcpyBlocks, memsetBlocks, quicksortBlocks,
    swapBlocks, allocBlocks, kmallocBlocks, listBlocks, listRevBlocks, schorrWaiteBlocks,
    heapWrapBlocks, conditionGuardBlocks, suzukiBlocks, traceDemoBlocks, str2longBlocks,
    renameBlocks, functionInfoBlocks, typeStrengthenBlocks, wordAbsBlocks]

abbrev autocorresCtx : Ctx := mkCtx autocorresBlocks autocorresBlocksValid

theorem autocorresCtx_wellTyped : Ctx.WellTyped autocorresCtx := by
  typecheck_ctx

end Zag.Test.Autocorres.Examples
