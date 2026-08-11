import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem metadata_is_certificate_derived :
    (translate certified support).metadata.symbolId =
        certified.certificate.functionInfo.symbolId ∧
      (translate certified support).metadata.sourceName = certified.function.name :=
  translateMetadataOrigin certified support

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
