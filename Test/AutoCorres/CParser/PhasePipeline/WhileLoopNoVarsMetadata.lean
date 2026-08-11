import Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVarsCertificates

/-! # Certificate-derived metadata for parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem metadata_is_certificate_derived :
    translation.metadata.symbolId =
        certified.certificate.functionInfo.symbolId ∧
      translation.metadata.sourceName = certified.function.name :=
  translateMetadataOrigin certified support

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
