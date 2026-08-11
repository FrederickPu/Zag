import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

/-- The generated scalar operation has an actual WA-to-TS adjacent chain. -/
theorem adjacent_chain_is_packaged :
    ScalarStrengthenArtifact.AdjacentCertificates
      translation.wordStrengthen :=
  translation.wordStrengthen.adjacentCertificates

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
