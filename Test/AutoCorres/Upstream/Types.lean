/-!
# AutoCorres upstream test inventory types

The inventory is pinned to
[`tools/autocorres/tests`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/tests)
and its generating
[`Makefile`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/Makefile).
-/

namespace Zag.Test.AutoCorres.Upstream

/-- A resolved declaration name; unlike a name literal, this fails for unknown declarations. -/
macro "nameof " declaration:ident : term => `(``$declaration)

def pinnedCommit : String :=
  "bc2599a59c43e673dca021b10b9841e9b8da4430"

structure SourceFile where
  relativePath : String
  underTests : Bool := true
  deriving DecidableEq, Repr

def SourceFile.url (source : SourceFile) : String :=
  let pathPrefix :=
    if source.underTests then "tools/autocorres/tests/" else "tools/autocorres/"
  s!"https://github.com/seL4/l4v/blob/{pinnedCommit}/{pathPrefix}{source.relativePath}"

def sourceFile (relativePath : String) : SourceFile := { relativePath }
def autocorresFile (relativePath : String) : SourceFile := ⟨relativePath, false⟩

private def theoryEntry (relativePath : String) : String :=
  (relativePath.dropEnd 4).toString

/-- A local Lean module and the substantive declarations that witness its coverage. -/
structure LocalEntry where
  moduleName : String
  anchor : Lean.Name
  additionalAnchors : List Lean.Name := []
  deriving Repr

def LocalEntry.anchors (port : LocalEntry) : List Lean.Name :=
  port.anchor :: port.additionalAnchors

inductive Coverage where
  | blocked
  | fragment (port : LocalEntry)
  | complete (port : LocalEntry)
  | upstreamKnownFailing
  deriving Repr

def Coverage.localEntry : Coverage → Option LocalEntry
  | .fragment port | .complete port => some port
  | .blocked | .upstreamKnownFailing => none

def Coverage.anchors : Coverage → List Lean.Name
  | .fragment port | .complete port => port.anchors
  | .blocked | .upstreamKnownFailing => []

def Coverage.isBlocked : Coverage → Bool
  | .blocked => true
  | _ => false

def Coverage.isFragment : Coverage → Bool
  | .fragment _ => true
  | _ => false

def Coverage.isComplete : Coverage → Bool
  | .complete _ => true
  | _ => false

def Coverage.isUpstreamKnownFailing : Coverage → Bool
  | .upstreamKnownFailing => true
  | _ => false

/-- One upstream theory entry, its session spelling when active, and local fixtures. -/
structure TestCase where
  name : String
  session : String := "AutoCorresTest"
  sessionEntry : String
  upstreamEntry : SourceFile
  fixtures : List SourceFile := []
  coverage : Coverage
  reason : String
  deriving Repr

def blockedCase (name relativePath reason : String) : TestCase :=
  { name, sessionEntry := theoryEntry relativePath,
    upstreamEntry := sourceFile relativePath, coverage := .blocked, reason }

def fragmentCase (name relativePath reason leanEntry : String) (anchor : Lean.Name)
    (additionalAnchors : List Lean.Name := []) : TestCase :=
  { name, sessionEntry := theoryEntry relativePath,
    upstreamEntry := sourceFile relativePath,
    coverage := .fragment { moduleName := leanEntry, anchor, additionalAnchors }, reason }

def completeCase (name relativePath reason leanEntry : String) (anchor : Lean.Name)
    (additionalAnchors : List Lean.Name := []) : TestCase :=
  { name, sessionEntry := theoryEntry relativePath,
    upstreamEntry := sourceFile relativePath,
    coverage := .complete { moduleName := leanEntry, anchor, additionalAnchors }, reason }

def knownFailingCase (name relativePath reason : String) : TestCase :=
  { name, session := "excluded", sessionEntry := theoryEntry relativePath,
    upstreamEntry := sourceFile relativePath, coverage := .upstreamKnownFailing, reason }

def referencedFiles (tests : List TestCase) : List SourceFile :=
  (tests.flatMap fun test => test.upstreamEntry :: test.fixtures).eraseDups

def TestCase.id (test : TestCase) : String := s!"{test.session}:{test.sessionEntry}"

theorem Coverage.fragment_has_anchors (port : LocalEntry) :
    (Coverage.fragment port).anchors.isEmpty = false := by
  rfl

theorem Coverage.complete_has_anchors (port : LocalEntry) :
    (Coverage.complete port).anchors.isEmpty = false := by
  rfl

theorem Coverage.blocked_has_no_anchors : (Coverage.blocked).anchors = [] := by
  rfl

end Zag.Test.AutoCorres.Upstream
