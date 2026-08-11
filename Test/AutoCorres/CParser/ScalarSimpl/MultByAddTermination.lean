import Test.AutoCorres.CParser.ScalarSimpl.MultByAddCorrectness

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser.ScalarSimpl

theorem mult_by_add_no_failure (a b : MultByAddWord32) :
    ¬Raw.FunctionExec multByAddCertificate.program "mult_by_add"
      multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
      (multByAddInitial a b) .undefinedBehavior := by
  intro failed
  have resolvedFailure := multByAddCertificate.resolution.rawToResolved
    (multByAddInitial a b) .undefinedBehavior failed
  have equality := function_exec_deterministic multByAdd
    (mult_by_add_resolved_executes a b) resolvedFailure
  cases equality

/-- Every pair of u32 inputs terminates successfully and has no C failure execution. -/
theorem mult_by_add_total_no_failure (a b : MultByAddWord32) :
    Raw.FunctionExec multByAddCertificate.program "mult_by_add"
        multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
        (multByAddInitial a b) (.success (multByAddResult a b)) ∧
      ¬Raw.FunctionExec multByAddCertificate.program "mult_by_add"
        multByAddCertificate.functionInfo multByAddCertificate.rawBody multByAdd.returnType
        (multByAddInitial a b) .undefinedBehavior :=
  ⟨mult_by_add_raw_fixture_executes a b, mult_by_add_no_failure a b⟩

end Zag.Test.AutoCorres.CParser.ScalarSimpl
