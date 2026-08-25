import Test.Autocorres.Examples.BinarySearch
import Test.Autocorres.Examples.FactorialTest
import Test.Autocorres.Examples.FibProof
import Test.Autocorres.Examples.IsPrime
import Test.Autocorres.Examples.Memcpy
import Test.Autocorres.Examples.Memset
import Test.Autocorres.Examples.MultByAdd
import Test.Autocorres.Examples.Plus
import Test.Autocorres.Examples.QuicksortProgram
import Test.Autocorres.Examples.Simple

namespace Zag.Test.Autocorres.Examples

open Zag.Lib.PeanoHeap

abbrev autocorresBlocksFirst : BlockCtx.Raw heapCtx :=
  plusBlocks ++ multByAddBlocks ++ factorialBlocks ++ fibBlocks ++ simpleBlocks ++
  isPrimeBlocks ++ binarySearchBlocks ++ memcpyBlocks ++ memsetBlocks ++ quicksortBlocks

set_option maxRecDepth 100000 in
theorem autocorresBlocksFirstValid : BlockCtx.Valid autocorresBlocksFirst := by
  valid_blocks [autocorresBlocksFirst, termUnit, plusBlocks, multByAddBlocks, factorialBlocks,
    fibBlocks, simpleBlocks, isPrimeBlocks, binarySearchBlocks, memcpyBlocks, memsetBlocks,
    quicksortBlocks]

end Zag.Test.Autocorres.Examples
