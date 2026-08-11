import Lang.AutoCorres.CParser.CallGraph
import Lang.AutoCorres.CParser.Frontend
import Test.AutoCorres.CParser.EmbeddedFixtures

namespace Zag.Test.AutoCorres.CParser.CallGraph

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis
open Zag.Lang.AutoCorres.CParser.CallGraph

private def graph? (entry : String) : Option Graph :=
  (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program.map build

private def symbolName? (program : Program) (symbolId : Nat) : Option String :=
  (program.symbolById? symbolId).map (·.sourceName)

private def namedSCCs? (entry : String) : Option (List (List String × Bool)) := do
  let program ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program
  let graph := build program
  graph.sccs.mapM fun component => do
    let names ← component.members.mapM (symbolName? program)
    return (names, component.recursive)

private def namedEdges? (entry : String) : Option (List (String × Option String × String)) := do
  let program ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program
  let graph := build program
  graph.edges.mapM fun edge => do
    let caller ← edge.caller.bind (symbolName? program)
    let callee := edge.callee.bind (symbolName? program)
    let kind := match edge with
      | .directDefined .. => "defined"
      | .directBodyless .. => "bodyless"
      | .indirectOrUnresolved .. => "unresolved"
    return (caller, callee, kind)

private def namedNodes? (entry : String) : Option (List (String × String)) := do
  let program ← (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program
  (build program).nodes.mapM fun node => do
    let name ← symbolName? program node.symbolId
    return (name, match node with | .defined _ => "defined" | .bodyless _ => "bodyless")

private def valid? (entry : String) : Option Bool :=
  (graph? entry).map (·.valid)

private def certifies? (entry : String) : Option Bool :=
  (Frontend.preprocessAndAnalyze .arm EmbeddedFixtures.files entry).program.map
    fun program => (certify program).isOk

private def functionPointerGraph? : Option (Program × Graph) := do
  let program ← (Frontend.analyzeSource .arm "function_pointer.c" "
    int increment(int value) { return value + 1; }
    int apply(int (*function)(int), int value) { return function(value); }
    int call_apply(void) { return apply(increment, 3); }").program
  return (program, build program)

private def functionPointerSCCs? : Option (List (List String × Bool)) := do
  let (program, graph) ← functionPointerGraph?
  graph.sccs.mapM fun component => do
    let names ← component.members.mapM (symbolName? program)
    return (names, component.recursive)

private def functionPointerEdges? : Option (List (String × Option String × String)) := do
  let (program, graph) ← functionPointerGraph?
  graph.edges.mapM fun edge => do
    let caller ← edge.caller.bind (symbolName? program)
    let callee := edge.callee.bind (symbolName? program)
    let kind := match edge with
      | .directDefined .. => "defined"
      | .directBodyless .. => "bodyless"
      | .indirectOrUnresolved .. => "unresolved"
    return (caller, callee, kind)

example : namedSCCs? "parse-tests/basic_recursion.c" = some [
    (["r"], true), (["fact"], true), (["fact_unsigned"], true),
    (["call_recursive"], false), (["call_recursive2"], false)] := by
  native_decide

example : namedSCCs? "parse-tests/mutual_recursion.c" = some [
    (["y", "x"], true), (["call_recursive"], false)] := by
  native_decide

example : namedSCCs? "parse-tests/mutual_recursion2.c" = some [
    (["fib"], true), (["rev"], true), (["ff"], true),
    (["b", "c", "a"], true)] := by
  native_decide

example : namedSCCs? "parse-tests/bodyless_function.c" =
    some [(["call_bodyless"], false)] := by
  native_decide

example : namedNodes? "parse-tests/bodyless_function.c" = some [
    ("call_bodyless", "defined"), ("bodyless", "bodyless")] := by
  native_decide

example : namedEdges? "parse-tests/bodyless_function.c" =
    some [("call_bodyless", some "bodyless", "bodyless")] := by
  native_decide

example : functionPointerSCCs? = some [
    (["increment"], false), (["apply"], false), (["call_apply"], false)] := by
  native_decide

example : functionPointerEdges? = some [
    ("apply", none, "unresolved"),
    ("call_apply", some "apply", "defined")] := by
  native_decide

example : (Frontend.analyzeSource .arm "sizeof.c" "
    int callee(void) { return 1; }
    int caller(void) { return sizeof(callee()); }").program.map
      (fun program => (build program).edges.length) = some 0 := by
  native_decide

example : [
    "parse-tests/basic_recursion.c",
    "parse-tests/mutual_recursion.c",
    "parse-tests/mutual_recursion2.c",
    "parse-tests/bodyless_function.c"].all (valid? · == some true) &&
      functionPointerGraph?.any (fun (_, graph) => graph.valid) := by
  native_decide

example : [
    "parse-tests/basic_recursion.c",
    "parse-tests/mutual_recursion.c",
    "parse-tests/mutual_recursion2.c",
    "parse-tests/bodyless_function.c"].all (certifies? · == some true) &&
      functionPointerGraph?.any (fun (program, _) => (certify program).isOk) := by
  native_decide

private def unrelatedMerged : Graph :=
  { nodes := [.defined 1, .defined 2]
    edges := []
    sccs := [{ members := [1, 2], recursive := true }]
    condensation := [] }

private def bogusCondensation : Graph :=
  { nodes := [.defined 1]
    edges := []
    sccs := [{ members := [1], recursive := false }]
    condensation := [(1, 0)] }

private def inconsistentEdge : Graph :=
  { nodes := [.defined 1]
    edges := [.directDefined (some 1) 2 .bogus]
    sccs := [{ members := [1], recursive := false }]
    condensation := [] }

private def misclassifiedDefinedEdge : Graph :=
  { nodes := [.defined 1, .defined 2]
    edges := [.indirectOrUnresolved (some 1) (some 2) .bogus]
    sccs := [
      { members := [1], recursive := false },
      { members := [2], recursive := false }]
    condensation := [] }

private def extraEmptyComponent : Graph :=
  { nodes := [.defined 1]
    edges := []
    sccs := [{ members := [1], recursive := false }, { members := [], recursive := false }]
    condensation := [] }

private def duplicateBodylessNode : Graph :=
  { nodes := [.bodyless 1, .bodyless 1]
    edges := []
    sccs := []
    condensation := [] }

example : unrelatedMerged.valid = false := by native_decide
example : bogusCondensation.valid = false := by native_decide
example : inconsistentEdge.valid = false := by native_decide
example : misclassifiedDefinedEdge.valid = false := by native_decide
example : extraEmptyComponent.valid = false := by native_decide
example : duplicateBodylessNode.valid = false := by native_decide

end Zag.Test.AutoCorres.CParser.CallGraph
