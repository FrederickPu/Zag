import Test.AutoCorres.CParser.PhasePipeline.BasicTranslation

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

theorem final_correspondence :
    ac_corres id false emptyEnvironment
      (readWord support) (fun _ => True)
      translation.strengthen.target certified.function.command :=
  translation.finalCorres

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
