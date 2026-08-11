import Lang.AutoCorres.CParser.Preprocessor

namespace Zag.Test.AutoCorres.CParser.Preprocessor

open Zag.Lang.AutoCorres.CParser.Preprocessor

set_option warningAsError true

private def preprocessSource (source : String) : Result :=
  preprocess [{ name := "input.c", source }] "input.c"

private def selfRecursive := preprocessSource "#define A A\nA\n"

#guard selfRecursive.diagnostics.isEmpty
#guard selfRecursive.output.endsWith "A\n"

private def mutualRecursive := preprocessSource "#define A B\n#define B A\nA\n"

#guard mutualRecursive.diagnostics.isEmpty
#guard mutualRecursive.output.endsWith "A\n" || mutualRecursive.output.endsWith "B\n"

private def nestedFunction := preprocessSource <|
  "#define DOUBLE(x) ((x) + (x))\n" ++
  "#define APPLY(f, x) f(x)\n" ++
  "APPLY(DOUBLE, 3)\n"

#guard nestedFunction.diagnostics.isEmpty
#guard !nestedFunction.output.contains "APPLY"
#guard !nestedFunction.output.contains "DOUBLE"
#guard nestedFunction.output.contains "3"

end Zag.Test.AutoCorres.CParser.Preprocessor
