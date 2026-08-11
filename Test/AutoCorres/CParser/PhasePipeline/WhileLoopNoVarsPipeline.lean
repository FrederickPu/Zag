import Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVarsBehavior

/-! # Production pipeline for generated parse test `while_loop_no_vars` -/

namespace Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars

open Zag.Lang.AutoCorres
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open Zag.Lang.AutoCorres.CParser.PhasePipeline
open Zag.Lang.AutoCorres.CParser.PhasePipeline.Scalar

noncomputable def translation := Scalar.translate certified support

theorem ordinary_autocorres_succeeds :
    translation.metadata.phases =
      [{ phase := .simplConv, mode := .translated },
       { phase := .localVarExtract, mode := .translated },
       { phase := .heapLift, mode := .exactIdentity },
       { phase := .wordAbstract, mode := .exactIdentity },
       { phase := .typeStrengthen, mode := .exactIdentity }] := by
  rfl

theorem final_correspondence :
    ac_corres id false emptyEnvironment
      (readWord support) (fun _ => True)
      translation.strengthen.target certified.function.command :=
  translation.finalCorres

end Zag.Test.AutoCorres.CParser.PhasePipeline.WhileLoopNoVars
