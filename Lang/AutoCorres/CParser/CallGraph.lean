import Lang.AutoCorres.CParser.ProgramAnalysis

/-!
# Total analyzed-C call graphs

This module classifies every call recorded by `ProgramAnalysis`, including
bodyless and unresolved calls.  SCCs use only direct edges between defined
functions and are independent of the downstream scalar-call scheduler.
-/

namespace Zag.Lang.AutoCorres.CParser.CallGraph

open ProgramAnalysis

inductive Node where
  | defined (symbolId : Nat)
  | bodyless (symbolId : Nat)
deriving Repr, DecidableEq, Inhabited

namespace Node

def symbolId : Node → Nat
  | .defined symbolId | .bodyless symbolId => symbolId

end Node

inductive Edge where
  | directDefined (caller : Option Nat) (callee : Nat) (region : Region)
  | directBodyless (caller : Option Nat) (callee : Nat) (region : Region)
  | indirectOrUnresolved (caller callee : Option Nat) (region : Region)
deriving Repr, DecidableEq, Inhabited

namespace Edge

def caller : Edge → Option Nat
  | .directDefined caller _ _ | .directBodyless caller _ _ |
      .indirectOrUnresolved caller _ _ => caller

def callee : Edge → Option Nat
  | .directDefined _ callee _ | .directBodyless _ callee _ => some callee
  | .indirectOrUnresolved _ callee _ => callee

def region : Edge → Region
  | .directDefined _ _ region | .directBodyless _ _ region |
      .indirectOrUnresolved _ _ region => region

end Edge

structure SCC where
  members : List Nat
  recursive : Bool
deriving Repr, DecidableEq, Inhabited

structure Graph where
  nodes : List Node
  edges : List Edge
  sccs : List SCC
  /-- Pairs are indices into `sccs`, directed from caller to callee. -/
  condensation : List (Nat × Nat)
deriving Repr, DecidableEq, Inhabited

private def insertNat (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail else head :: insertNat value tail

private def sortNats : List Nat → List Nat
  | [] => []
  | head :: tail => insertNat head (sortNats tail)

private def insertByRank (rank : List Nat → Nat) (component : List Nat) :
    List (List Nat) → List (List Nat)
  | [] => [component]
  | head :: tail =>
      if rank component < rank head ||
          (rank component = rank head && component.head?.getD 0 < head.head?.getD 0) then
        component :: head :: tail
      else head :: insertByRank rank component tail

private def sortByRank (rank : List Nat → Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | head :: tail => insertByRank rank head (sortByRank rank tail)

private abbrev Relation := List (Nat × Nat)

private def closeAt (nodes : List Nat) (relation : Relation) (pivot : Nat) : Relation :=
  (relation ++ nodes.flatMap fun caller =>
    nodes.filterMap fun callee =>
      if relation.contains (caller, pivot) && relation.contains (pivot, callee) then
        some (caller, callee)
      else none).eraseDups

private def transitiveClosure (nodes : List Nat) (edges : Relation) : Relation :=
  nodes.foldl (closeAt nodes) (((nodes.map fun node => (node, node)) ++ edges).eraseDups)

private def componentOf (nodes : List Nat) (closure : Relation) (source : Nat) : List Nat :=
  nodes.filter fun target =>
    closure.contains (source, target) && closure.contains (target, source)

private def collectComponents (nodes : List Nat) (closure : Relation) : List (List Nat) :=
  nodes.foldl (fun components node =>
    if components.any (·.contains node) then components
    else components ++ [componentOf nodes closure node]) []

private def functionIds (program : Program) : List Nat :=
  sortNats (program.functions.map (·.symbolId)) |>.eraseDups

private def bodylessIds (program : Program) (defined : List Nat) : List Nat :=
  sortNats (program.symbols.filterMap fun symbol =>
    if symbol.kind = .function && !defined.contains symbol.id then some symbol.id else none)
    |>.eraseDups

private def classifyEdge (defined bodyless : List Nat) (call : CallInfo) : Edge :=
  match call.callee with
  | some callee =>
      if defined.contains callee then .directDefined call.caller callee call.region
      else if bodyless.contains callee then .directBodyless call.caller callee call.region
      else .indirectOrUnresolved call.caller call.callee call.region
  | none => .indirectOrUnresolved call.caller none call.region

private def definedEdges (defined : List Nat) (edges : List Edge) : Relation :=
  edges.filterMap fun edge => match edge with
    | .directDefined (some caller) callee _ =>
        if defined.contains caller then some (caller, callee) else none
    | _ => none

private def componentIndex? (sccs : List SCC) (symbolId : Nat) : Option Nat :=
  sccs.findIdx? (·.members.contains symbolId)

private def condensationEdges (sccs : List SCC) (edges : Relation) : List (Nat × Nat) :=
  edges.filterMap (fun (caller, callee) => do
    let callerIndex ← componentIndex? sccs caller
    let calleeIndex ← componentIndex? sccs callee
    if callerIndex = calleeIndex then none else some (callerIndex, calleeIndex)) |>.eraseDups

private def hasSelfLoop (edges : Relation) (component : List Nat) : Bool :=
  component.any fun symbolId => edges.contains (symbolId, symbolId)

/-- Build a deterministic graph for every `ProgramAnalysis.Program`. -/
def build (program : Program) : Graph :=
  let defined := functionIds program
  let bodyless := bodylessIds program defined
  let edges := program.calls.map (classifyEdge defined bodyless)
  let direct := definedEdges defined edges
  let closure := transitiveClosure defined direct
  let rank (component : List Nat) :=
    match component with
    | [] => 0
    | representative :: _ => defined.countP fun callee => closure.contains (representative, callee)
  let components := sortByRank rank (collectComponents defined closure)
  let sccs := components.map fun members =>
    { members, recursive := members.length > 1 || hasSelfLoop direct members }
  { nodes := defined.map .defined ++ bodyless.map .bodyless
    edges
    sccs
    condensation := condensationEdges sccs direct }

structure InvariantChecks where
  nodesUnique : Bool
  sccsNonempty : Bool
  everyDefinedExactlyOnce : Bool
  sccMembersUnique : Bool
  sccPartitionExact : Bool
  allIntraDefinedEdgesRepresented : Bool
  edgeClassificationConsistent : Bool
  condensationExact : Bool
  condensationDependenciesFirst : Bool
  recursiveClassification : Bool
deriving Repr, DecidableEq, Inhabited

namespace InvariantChecks

def all (checks : InvariantChecks) : Bool :=
  checks.nodesUnique && checks.sccsNonempty && checks.everyDefinedExactlyOnce &&
    checks.sccMembersUnique &&
    checks.sccPartitionExact && checks.allIntraDefinedEdgesRepresented &&
    checks.edgeClassificationConsistent && checks.condensationExact &&
    checks.condensationDependenciesFirst && checks.recursiveClassification

end InvariantChecks

/-- Executable checks for the SCC and condensation invariants. -/
def Graph.checkInvariants (graph : Graph) : InvariantChecks :=
  let defined := graph.nodes.filterMap fun node => match node with
    | .defined symbolId => some symbolId
    | .bodyless _ => none
  let bodyless := graph.nodes.filterMap fun node => match node with
    | .defined _ => none
    | .bodyless symbolId => some symbolId
  let members := graph.sccs.flatMap (·.members)
  let nodeIds := graph.nodes.map (·.symbolId)
  let direct := definedEdges defined graph.edges
  let closure := transitiveClosure defined direct
  let expectedCondensation := condensationEdges graph.sccs direct
  { nodesUnique := nodeIds.eraseDups.length = nodeIds.length
    sccsNonempty := graph.sccs.all fun component => !component.members.isEmpty
    everyDefinedExactlyOnce :=
      defined.all members.contains && members.all defined.contains &&
        members.length = defined.length
    sccMembersUnique := members.eraseDups.length = members.length
    sccPartitionExact := defined.all fun left => defined.all fun right =>
      let mutuallyReachable :=
        closure.contains (left, right) && closure.contains (right, left)
      let sameComponent :=
        decide (componentIndex? graph.sccs left = componentIndex? graph.sccs right)
      mutuallyReachable == sameComponent
    allIntraDefinedEdgesRepresented := direct.all fun (caller, callee) =>
      (componentIndex? graph.sccs caller).isSome &&
        (componentIndex? graph.sccs callee).isSome &&
        (componentIndex? graph.sccs caller = componentIndex? graph.sccs callee ||
          match componentIndex? graph.sccs caller, componentIndex? graph.sccs callee with
           | some callerIndex, some calleeIndex =>
               graph.condensation.contains (callerIndex, calleeIndex)
           | _, _ => false)
    edgeClassificationConsistent := graph.edges.all fun edge => match edge with
      | .directDefined caller callee _ =>
          caller.any defined.contains && defined.contains callee
      | .directBodyless caller callee _ =>
          caller.any defined.contains && bodyless.contains callee
      | .indirectOrUnresolved caller callee _ =>
          caller.any defined.contains &&
            !(callee.any fun symbolId =>
              defined.contains symbolId || bodyless.contains symbolId)
    condensationExact := graph.condensation == expectedCondensation
    condensationDependenciesFirst := graph.condensation.all fun (caller, callee) =>
      caller < graph.sccs.length && callee < graph.sccs.length && callee < caller
    recursiveClassification := graph.sccs.all fun component =>
      component.recursive =
        (component.members.length > 1 || hasSelfLoop direct component.members) }

def Graph.valid (graph : Graph) : Bool :=
  graph.checkInvariants.all

structure Certificate (program : Program) where
  graph : Graph
  graph_eq : graph = build program
  valid : graph.valid = true

def certify (program : Program) : Except InvariantChecks (Certificate program) :=
  let graph := build program
  if valid : graph.valid = true then
    .ok { graph, graph_eq := rfl, valid }
  else
    .error graph.checkInvariants

end Zag.Lang.AutoCorres.CParser.CallGraph
