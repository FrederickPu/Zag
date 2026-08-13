import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem final_correspondence :
    ac_corres id false emptyEnvironment
      (readWord prepared.supported) (fun _ => True)
      prepared.translation.strengthen.target prepared.certified.function.command :=
  prepared.finalCorres

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
