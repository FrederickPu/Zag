/-!
# IncludeDir.Basic

A directory reflected as a pure `FileTree`: each node is a file (name + contents)
or a directory (name + children). Paths use `System.FilePath` (`"a" / "b" / "c.txt"`).
Lookups reduce with `native_decide` — no custom reflection axioms.
-/

namespace IncludeDir

export System (FilePath)

/-- Allows `"womp" / "womp" / "blah.txt"` as a `FilePath`. -/
instance : HDiv String String FilePath where
  hDiv a b := (⟨a⟩ : FilePath) / b

/--
Pure snapshot of a filesystem subtree.

* `file name content` — regular file
* `dir name children` — directory
-/
inductive FileTree where
  | file (name : String) (content : String)
  | dir  (name : String) (children : List FileTree)
  deriving Repr, Inhabited, BEq

namespace FileTree

def name : FileTree → String
  | .file n _ => n
  | .dir  n _ => n

def isFile : FileTree → Bool
  | .file _ _ => true
  | .dir  _ _ => false

def isDir : FileTree → Bool
  | .file _ _ => false
  | .dir  _ _ => true

def content? : FileTree → Option String
  | .file _ c => some c
  | .dir  _ _ => none

def children : FileTree → List FileTree
  | .file _ _ => []
  | .dir  _ cs => cs

/-- Immediate child with the given name, if any. -/
def child? (t : FileTree) (n : String) : Option FileTree :=
  t.children.find? (fun c => c.name == n)

/-- Path components with `.` and empty segments dropped. -/
def components (path : FilePath) : List String :=
  path.components.filter fun s => decide (s ≠ "") && decide (s ≠ ".")

/-- Lookup by path component list under this tree. -/
def lookup : FileTree → List String → Option FileTree
  | t, [] => some t
  | .file _ _, _ :: _ => none
  | t@(.dir _ _), p :: ps =>
      match t.child? p with
      | none => none
      | some c => c.lookup ps

/-- Relative `FilePath` lookup from this tree root (root dir name omitted). -/
def lookupPath (t : FileTree) (path : FilePath) : Option FileTree :=
  t.lookup (components path)

/-- File contents at a relative `FilePath`, if that path names a file. -/
def lookupContent (t : FileTree) (path : FilePath) : Option String :=
  match t.lookupPath path with
  | some (.file _ c) => some c
  | _ => none

/-- Flatten to `(relPath, content)` pairs for every file under this node. -/
partial def filesAt (t : FileTree) (pre : FilePath) : List (FilePath × String) :=
  match t with
  | .file n c => [(pre / n, c)]
  | .dir _ cs =>
      cs.flatMap fun c =>
        match c with
        | .file n content => [(pre / n, content)]
        | .dir n _ => filesAt c (pre / n)

/-- All files with paths relative to this tree's root (root dir name omitted). -/
def allFiles (t : FileTree) : List (FilePath × String) :=
  match t with
  | .file n c => [(⟨n⟩, c)]
  | .dir _ cs =>
      cs.flatMap fun c =>
        match c with
        | .file n content => [(⟨n⟩, content)]
        | .dir n _ => filesAt c ⟨n⟩

/-- Number of file nodes (recursive). -/
partial def fileCount : FileTree → Nat
  | .file _ _ => 1
  | .dir _ cs => cs.foldl (fun acc c => acc + c.fileCount) 0

def filePaths (t : FileTree) : List FilePath :=
  t.allFiles.map (·.1)

/-- Resolve `rel` against the directory containing `fromPath`. -/
def resolveFrom (fromPath rel : FilePath) : FilePath :=
  if rel.isAbsolute then
    rel
  else
    let dirParts := (components fromPath).dropLast
    let rec join (acc : List String) : List String → List String
      | [] => acc
      | ".." :: rest => join acc.dropLast rest
      | p :: rest => join (acc ++ [p]) rest
    System.mkFilePath (join dirParts (components rel))

end FileTree

/-- Toy `#import "path"` lines; paths are resolved relative to the importer. -/
def parseHashImports (fromPath : FilePath) (src : String) : List FilePath :=
  src.splitOn "\n" |>.filterMap fun line =>
    let t := line.trimAscii.copy
    let pref := "#import \""
    if t.startsWith pref && t.endsWith "\"" then
      let rel : FilePath := ⟨(t.drop pref.length |>.dropEnd 1).copy⟩
      some (FileTree.resolveFrom fromPath rel)
    else
      none

private def pathEq (a b : FilePath) : Bool :=
  a.toString == b.toString

private def appendNew (acc : List (FilePath × String)) (more : List (FilePath × String)) :
    List (FilePath × String) :=
  more.foldl (init := acc) fun acc pair =>
    if acc.any (fun p => pathEq p.1 pair.1) then acc else acc ++ [pair]

private def seenHas (seen : List FilePath) (p : FilePath) : Bool :=
  seen.any (pathEq · p)

/--
Walk `#import` edges inside a pure `FileTree`, starting at `root`.
Returns loaded `(path, content)` pairs; each path at most once.
-/
partial def loadClosure (tree : FileTree) (root : FilePath) :
    Except String (List (FilePath × String)) :=
  go root []
where
  go (path : FilePath) (seen : List FilePath) : Except String (List (FilePath × String)) :=
    if seenHas seen path then
      .ok []
    else
      match tree.lookupContent path with
      | none => .error s!"IncludeDir: file not found in tree: {path}"
      | some content =>
        let deps := parseHashImports path content
        deps.foldl (init := .ok [(path, content)]) fun acc d =>
          match acc with
          | .error e => .error e
          | .ok ms =>
            match go d (path :: seen) with
            | .error e => .error e
            | .ok sub => .ok (appendNew ms sub)

end IncludeDir
