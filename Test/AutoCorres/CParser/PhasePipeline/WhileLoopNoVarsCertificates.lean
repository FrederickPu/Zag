import Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVarsPipeline

/-! # Adjacent generated certificates for parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem adjacent_chain_is_packaged :
    ScalarStrengthenArtifact.AdjacentCertificates
      translation.wordStrengthen :=
  translation.wordStrengthen.adjacentCertificates

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
