/-!
# StrictC source locations and diagnostics

Pure counterparts of `SourcePos.ML`, `SourceFile.ML`, and `Region.ML` from the
pinned l4v StrictC frontend.
-/

namespace Zag.Lang.AutoCorres.CParser

structure SourcePos where
  file : String
  line : Int
  column : Int
  offset : Nat
deriving Repr, DecidableEq, Inhabited

structure Region where
  left : SourcePos
  right : SourcePos
  isBogus : Bool := false
deriving Repr, DecidableEq, Inhabited

inductive Severity where
  | warning
  | error
deriving Repr, DecidableEq, Inhabited

structure Diagnostic where
  severity : Severity
  region : Region
  message : String
deriving Repr, DecidableEq, Inhabited

structure Located (α : Type u) where
  value : α
  region : Region
deriving Repr, DecidableEq, Inhabited

namespace SourcePos

def bogus : SourcePos :=
  { file := "<bogus>", line := -1, column := -1, offset := 0 }

end SourcePos

namespace Region

def point (position : SourcePos) : Region :=
  { left := position, right := position }

def append (first second : Region) : Region :=
  if first.isBogus then second
  else if second.isBogus then first
  else { left := first.left, right := second.right }

def bogus : Region := { left := SourcePos.bogus, right := SourcePos.bogus, isBogus := true }

end Region

structure SourceMap where
  file : String
  line : Nat := 1
  lineStart : Nat := 0
deriving Repr, DecidableEq, Inhabited

namespace SourceMap

def position (source : SourceMap) (offset : Nat) : SourcePos :=
  { file := source.file
    line := Int.ofNat source.line
    column := Int.ofNat (offset - source.lineStart)
    offset }

def newline (source : SourceMap) (nextOffset : Nat) : SourceMap :=
  { source with line := source.line + 1, lineStart := nextOffset }

def lineDirective (source : SourceMap) (file : Option String)
    (line lineStart : Nat) : SourceMap :=
  { file := file.getD source.file, line, lineStart }

end SourceMap

end Zag.Lang.AutoCorres.CParser
