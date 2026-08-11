import Lang.AutoCorres.ML.prog

namespace Zag.Test.AutoCorres.Prog

open Zag.Lang.AutoCorres.ML.Prog

set_option warningAsError true

private abbrev Expression := Unit × Finset String × Unit

private def expression (reads : List String) : Expression :=
  ((), makeSet reads, ())

private def loopProgram : Prog Unit Expression (Option String) Unit :=
  .while () (expression ["condition"])
    (.seq ()
      (.modify () (expression ["input"]) (some "accumulator"))
      (.guard () (expression ["accumulator"])))

private def live := calcLiveVars loopProgram (makeSet ["result"])

#guard live.isSome
#guard match live with
  | some program =>
      let root := getNodeData program
      root.contains "condition" && root.contains "input" && root.contains "result"
  | none => false

end Zag.Test.AutoCorres.Prog
