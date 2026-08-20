import IncludeDir.Basic
import IncludeDir.IO
import IncludeDir.Elab

/-!
# IncludeDir

Embed a directory as a pure `FileTree` and reason about multi-file programs as
ordinary Lean values.

```lean
def proj : FileTree := include_dir "src"
def mainSrc := proj.lookupContent ⟨"main.txt"⟩
def deep := proj.lookupContent ("nested" / "deep.txt")
def deps := loadClosure proj ⟨"main.txt"⟩
```

Paths are `System.FilePath` (use `/` to join). Lookups reduce with `native_decide`.
-/
