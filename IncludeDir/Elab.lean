import Lean
import IncludeDir.Basic

/-!
`include_dir "path"` elaborates a directory into a pure `FileTree` term.
The result is ordinary Lean data — `native_decide` handles lookups.
-/

namespace IncludeDir.Elab
open Lean Elab Term
open IncludeDir

/-- Recursively read `path` into a `FileTree` (directories expand to all descendants). -/
partial def readFileTree (path : System.FilePath) (nodeName : String) : IO FileTree := do
  if ← path.isDir then
    let entries ← path.readDir
    let mut children : List FileTree := []
    let names := (entries.map (·.fileName)).qsort (· < ·)
    for n in names do
      if n == ".git" || n == ".lake" || n == "_target" then
        continue
      -- recursive: subdirectories are fully expanded
      children := children ++ [← readFileTree (path.join n) n]
    pure (.dir nodeName children)
  else
    pure (.file nodeName (← IO.FS.readFile path))

partial def fileTreeToExpr : FileTree → Expr
  | .file n c =>
      mkApp2 (Lean.mkConst ``FileTree.file) (toExpr n) (toExpr c)
  | .dir n cs =>
      let ft := Lean.mkConst ``FileTree
      let nilE := mkApp (Lean.mkConst ``List.nil [0]) ft
      let consN := Lean.mkConst ``List.cons [0]
      let csE := cs.foldr
        (fun child acc => mkApp3 consN ft (fileTreeToExpr child) acc)
        nilE
      mkApp2 (Lean.mkConst ``FileTree.dir) (toExpr n) csE

def includeDir (path : System.FilePath) : TermElabM Expr := do
  unless ← path.pathExists do
    throwError "IncludeDir: path not found: {path}"
  let nodeName := path.fileName.getD path.toString
  let tree ← readFileTree path nodeName
  pure (fileTreeToExpr tree)

/-- `include_dir "path"` → `FileTree` -/
elab "include_dir " p:str : term => do
  includeDir (System.FilePath.mk p.getString)

/-- `include_file "path"` → `FileTree.file name content` -/
elab "include_file " p:str : term => do
  let path := System.FilePath.mk p.getString
  unless ← path.pathExists do
    throwError "IncludeDir: file not found: {path}"
  if ← path.isDir then
    throwError "IncludeDir: expected a file, got directory: {path}"
  let nodeName := path.fileName.getD path.toString
  let content ← IO.FS.readFile path
  pure (fileTreeToExpr (.file nodeName content))

/-- `#include_dir "path"` — log tree summary. -/
elab "#include_dir " p:str : command => do
  let path := System.FilePath.mk p.getString
  unless ← path.pathExists do
    throwError "IncludeDir: path not found: {path}"
  let nodeName := path.fileName.getD path.toString
  let tree ← readFileTree path nodeName
  let paths := tree.filePaths.map (·.toString)
  logInfo m!"FileTree {tree.name}: {tree.fileCount} files\n{String.intercalate "\n" paths}"

end IncludeDir.Elab
