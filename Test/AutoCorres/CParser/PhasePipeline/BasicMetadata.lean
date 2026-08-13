import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem metadata_is_certificate_derived :
    prepared.translation.metadata.symbolId =
        prepared.certified.certificate.functionInfo.symbolId ∧
      prepared.translation.metadata.sourceName = prepared.certified.function.name :=
  prepared.metadataOrigin

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
