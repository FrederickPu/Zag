import IncludeDir

namespace IncludeDir.Test

open IncludeDir
open System (FilePath)

/-- Entire fixture directory as one pure tree (recursive). -/
def fixtures : FileTree := include_dir "Test/IncludeDir/Fixtures"

example : fixtures.isDir = true := by native_decide

example : fixtures.fileCount = 4 := by native_decide

/-- Top-level file: relative path is just the file name. -/
example : fixtures.lookupContent ⟨"main.txt"⟩ ==
    some "#import \"lib.txt\"\n#import \"nested/deep.txt\"\nmain body\n" := by
  native_decide

example : fixtures.lookupContent ⟨"lib.txt"⟩ ==
    some "#import \"util.txt\"\nlib body\n" := by
  native_decide

example : fixtures.lookupContent ⟨"util.txt"⟩ == some "util body\n" := by
  native_decide

/-- Nested file via `FilePath` joins (`"nested" / "deep.txt"`). -/
example : fixtures.lookupContent ("nested" / "deep.txt") == some "deep body\n" := by
  native_decide

example : fixtures.lookupPath ("nested" / "deep.txt") ==
    some (.file "deep.txt" "deep body\n") := by
  native_decide

example : (fixtures.filePaths.map (·.toString)).any (· == "nested/deep.txt") = true := by
  native_decide

/-- Missing paths. -/
example : (fixtures.lookupContent ("nope" / "missing.txt")).isNone = true := by
  native_decide

/-- Dependency walk uses the same relative `FilePath`s. -/
def mainClosure : Except String (List (FilePath × String)) :=
  loadClosure fixtures ⟨"main.txt"⟩

example : mainClosure.isOk = true := by native_decide

example :
    (match mainClosure with
      | .ok ms => ms.map (·.1.toString)
      | .error _ => []) ==
    ["main.txt", "lib.txt", "util.txt", "nested/deep.txt"] := by
  native_decide

/-- Nested import is present in the closure. -/
example :
    (match mainClosure with
      | .ok ms => (ms.map (·.1.toString)).any (· == "nested/deep.txt")
      | .error _ => false) = true := by
  native_decide

/-- Single-file include. -/
def utilFile : FileTree := include_file "Test/IncludeDir/Fixtures/util.txt"

example : utilFile == .file "util.txt" "util body\n" := by native_decide

/-- Hand-built tree with nested dir — same relative-path API. -/
def hand : FileTree :=
  .dir "root" [
    .file "a.txt" "#import \"sub/b.txt\"\na\n",
    .dir "sub" [
      .file "b.txt" "b\n"
    ]
  ]

example : hand.lookupContent ("sub" / "b.txt") == some "b\n" := by native_decide

example : FileTree.resolveFrom ⟨"sub/a.txt"⟩ ⟨"../top.txt"⟩ == ⟨"top.txt"⟩ := by
  native_decide

example :
    (match loadClosure hand ⟨"a.txt"⟩ with
      | .ok ms => ms.map (fun p => (p.1.toString, p.2))
      | .error _ => []) ==
    [("a.txt", "#import \"sub/b.txt\"\na\n"), ("sub/b.txt", "b\n")] := by
  native_decide

end IncludeDir.Test
