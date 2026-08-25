import Test.Autocorres.Examples.ACRename
import Test.Autocorres.Examples.Alloc
import Test.Autocorres.Examples.CList
import Test.Autocorres.Examples.ConditionGuard
import Test.Autocorres.Examples.FunctionInfoDemo
import Test.Autocorres.Examples.HeapWrap
import Test.Autocorres.Examples.Incremental
import Test.Autocorres.Examples.Kmalloc
import Test.Autocorres.Examples.ListRev
import Test.Autocorres.Examples.SchorrWaite
import Test.Autocorres.Examples.Str2Long
import Test.Autocorres.Examples.Suzuki
import Test.Autocorres.Examples.Swap
import Test.Autocorres.Examples.TraceDemo
import Test.Autocorres.Examples.WordAbs
import Test.Autocorres.Examples.TypeStrengthenTricks

namespace Zag.Test.Autocorres.Examples

open Zag.Lib.PeanoHeap

abbrev autocorresBlocksSecondFirst : BlockCtx.Raw heapCtx :=
  swapBlocks ++ allocBlocks ++ kmallocBlocks ++ listBlocks ++ listRevBlocks ++ schorrWaiteBlocks ++
  heapWrapBlocks ++ conditionGuardBlocks

abbrev autocorresBlocksSecondLast : BlockCtx.Raw heapCtx :=
  suzukiBlocks ++ traceDemoBlocks ++ str2longBlocks ++ renameBlocks ++ functionInfoBlocks ++
  typeStrengthenBlocks ++ incrementalBlocks ++ wordAbsBlocks

abbrev autocorresBlocksSecond : BlockCtx.Raw heapCtx :=
  autocorresBlocksSecondFirst ++ autocorresBlocksSecondLast

set_option maxRecDepth 100000 in
theorem autocorresBlocksSecondValid : BlockCtx.Valid autocorresBlocksSecond := by
  valid_blocks [autocorresBlocksSecond, autocorresBlocksSecondFirst, autocorresBlocksSecondLast,
    swapBlocks, allocBlocks, kmallocBlocks, listBlocks, listRevBlocks, schorrWaiteBlocks,
    heapWrapBlocks, conditionGuardBlocks, suzukiBlocks, traceDemoBlocks, str2longBlocks,
    renameBlocks, functionInfoBlocks, typeStrengthenBlocks, incrementalBlocks, wordAbsBlocks]
  all_goals simp [termUnit, Term.callNames]

end Zag.Test.Autocorres.Examples
