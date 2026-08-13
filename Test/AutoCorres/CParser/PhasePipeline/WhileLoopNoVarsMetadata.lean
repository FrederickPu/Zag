import Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVarsCertificates

/-! # Certificate-derived metadata for parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem metadata_is_certificate_derived :
    prepared.translation.metadata.symbolId =
        prepared.certified.certificate.functionInfo.symbolId ∧
      prepared.translation.metadata.sourceName = prepared.certified.function.name :=
  prepared.metadataOrigin

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
