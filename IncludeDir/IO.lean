import IncludeDir.Basic

/-! Build a `FileTree` from the OS outside elaboration (e.g. `#eval`). -/

namespace IncludeDir

partial def FileTree.readOS (path : System.FilePath) (nodeName : String := "") : IO FileTree := do
  let nodeName := if nodeName = "" then path.fileName.getD path.toString else nodeName
  if ← path.isDir then
    let entries ← path.readDir
    let mut children : List FileTree := []
    let names := (entries.map (·.fileName)).qsort (· < ·)
    for n in names do
      if n == ".git" || n == ".lake" || n == "_target" then
        continue
      children := children ++ [← FileTree.readOS (path.join n) n]
    pure (.dir nodeName children)
  else
    pure (.file nodeName (← IO.FS.readFile path))

end IncludeDir
