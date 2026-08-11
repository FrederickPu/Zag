import Test.AutoCorres.CParser.ScalarSimpl.SelfInitializerArtifacts

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
theorem self_initializer_resolved_is_undefined :
    selfInitFunction.Exec selfInitInitial (.fault .undefinedBehavior) := by
  apply Function.Exec.fault
  rw [self_initializer_exact_resolution]
  apply Stmt.Exec.seqFault
  apply Stmt.Exec.seqFault
  apply Stmt.Exec.seqFault
  apply Stmt.Exec.initFault
  decide

theorem self_initializer_simpl_is_undefined :
    Zag.Lang.AutoCorres.Simpl.Exec emptyEnvironment selfInitFunction.command
      (.normal selfInitInitial) (.fault .undefinedBehavior) :=
  selfInitFunction.command_correct _ _ self_initializer_resolved_is_undefined

theorem self_initializer_raw_is_undefined :
    Raw.FunctionExec selfInitProgram "f" selfInitInfo selfInitRawBody
      selfInitFunction.returnType selfInitInitial .undefinedBehavior :=
  (selfInitCertificate.finite_iff selfInitInitial .undefinedBehavior).2
    self_initializer_simpl_is_undefined

end Zag.Test.AutoCorres.CParser.ScalarSimpl
