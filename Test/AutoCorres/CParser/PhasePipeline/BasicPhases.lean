import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline

/-- The ordinary production AutoCorres entry reaches every phase. -/
theorem ordinary_autocorres_succeeds :
    translation.metadata.phases =
      [{ phase := .simplConv, mode := .translated },
       { phase := .localVarExtract, mode := .translated },
       { phase := .heapLift, mode := .exactIdentity },
       { phase := .wordAbstract, mode := .exactIdentity },
       { phase := .typeStrengthen, mode := .exactIdentity }] := by
  rfl

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
