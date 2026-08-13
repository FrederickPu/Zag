import Lib.PeanoHeap
import Meta.UnifyType

/-!
Shared support for the AutoCorres example analogues.

Each module below mirrors one upstream `tools/autocorres/tests/examples/*.thy` theory with a
small block-IR program over `PeanoHeap` and a checked typing context.
-/

namespace Zag.Test.Autocorres.Examples

open Zag Zag.Lib.PeanoHeap

abbrev ctx : Ctx := peanoHeapCtx

abbrev mkCtx (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) : Ctx where
  primCtx := heapCtx
  opCtx := heapOpCtx
  blockCtx := { val := blocks, isValid := h }

instance (blocks : BlockCtx.Raw heapCtx) (h : BlockCtx.Valid blocks) :
    Peano.Model (mkCtx blocks h) where
  natType := by rfl
  boolType := by rfl
  eqOp := by rfl
  ltOp := by rfl
  gtOp := by rfl
  iteOp := by rfl

end Zag.Test.Autocorres.Examples
