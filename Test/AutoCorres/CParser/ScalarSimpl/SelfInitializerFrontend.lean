import Test.AutoCorres.CParser.ScalarSimpl.Common

namespace Zag.Test.AutoCorres.CParser.ScalarSimpl

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ScalarSimpl

def selfInitSource : String := "
  int f(int x) { { int x = x; return x; } }"

def selfInitFiles : Preprocessor.FileMap :=
  [{ name := "self-init.c", source := selfInitSource }]

opaque selfInitCertifiedResult :
    Except Zag.Lang.AutoCorres.CParser.ScalarSimpl.Error
      (Certified .arm selfInitFiles "self-init.c" "f") :=
  certifyFrontend .arm selfInitFiles "self-init.c" "f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem selfInitFixtureCertifies : selfInitCertifiedResult.isOk := by
  native_decide

end Zag.Test.AutoCorres.CParser.ScalarSimpl
