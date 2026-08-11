import Test.AutoCorres.CParser.ScalarSimpl.SelfInitializerCertified

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl
open FixtureHelpers

def selfInitFunction : Function := selfInitCertified.function

def selfInitCertificate : Certificate .arm selfInitFiles "self-init.c" "f"
    selfInitFunction :=
  selfInitCertified.certificate

def selfInitProgram : ProgramAnalysis.Program := selfInitCertificate.program

def selfInitInfo : ProgramAnalysis.FunctionInfo :=
  selfInitCertificate.functionInfo

def selfInitRawBody : Body := selfInitCertificate.rawBody

set_option maxRecDepth 100000 in
def selfInitInitial : State :=
  (selfInitFunction.enter [7]).toOption.get (by native_decide)

def expectedSelfInitFunction : Function :=
  { name := "f"
    returnType := s32
    parameters := [(1, s32)]
    locals := [2]
    body := .seq
      (.seq
        (.seq (.declare 2 s32 (some (.variable s32 2)))
          (.seq (.return s32 (.variable s32 2)) .skip))
        .skip)
      .skip }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem self_initializer_exact_resolution : selfInitFunction = expectedSelfInitFunction := by
  native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
