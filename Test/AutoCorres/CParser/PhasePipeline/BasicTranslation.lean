import Test.AutoCorres.CParser.PhasePipeline.BasicFixture

/-! # Production translation for generated parse test `basic` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.Basic

open Zag.Lang.AutoCorres.CParser

noncomputable def translation :=
  Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar.translate certified support

end Zag.Test.AutoCorres.CParser.PhasePipeline.Basic
