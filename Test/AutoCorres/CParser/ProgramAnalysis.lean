import Lang.AutoCorres.CParser.ProgramAnalysis
import Lang.AutoCorres.CParser.Frontend

/-! # StrictC program-analysis regressions -/

namespace Zag.Test.AutoCorres.CParser.ProgramAnalysis

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.ProgramAnalysis

private def analyzeSource? (source : String) : Option Program := do
  let translationUnit ← (parseSource .arm "analysis.c" source).value
  (analyze .arm translationUnit).toOption

private def analyzeResult (source : String) : Except AnalysisError Program := do
  let translationUnit ← match (parseSource .arm "analysis.c" source).value with
    | some value => pure value
    | none => throw (.nonConstantExpression .bogus)
  analyze .arm translationUnit

private def representative : Option Program := analyzeSource? "
typedef unsigned int u32;
typedef u32 word;
struct pair { word x; char y; };
word global;
word f(word p) { word local; return p; }
"

example : representative.isSome := by native_decide

example : (Frontend.analyzeSource .arm "small.c" "int f(void) { return 0; }").isSuccess := by
  native_decide

example : representative.map (fun program => program.typedefs.map Prod.fst) =
    some ["u32", "word"] := by native_decide

example : representative.bind (·.typeAbbrevs.get? "word") |>.isSome := by
  native_decide

example : (representative.bind (·.structBySourceName? "pair_C")
    |>.map (fun info =>
      (info.size, info.alignment, info.fields.map fun field => (field.sourceName, field.offset)))) =
    some (8, 4, [("x_C", 0), ("y_C", 4)]) := by native_decide

example : representative.map (fun program =>
    ((program.symbolsNamed "global").length,
      (program.symbolsNamed "f").length,
      (program.symbolsNamed "p").length,
      (program.symbolsNamed "local").length)) = some (1, 1, 1, 1) := by
  native_decide

private def scopedTypedefs : Option Program := analyzeSource? "
int f(void) {
  typedef unsigned short local_word;
  local_word x;
  { typedef unsigned char byte; byte y; }
  return 0;
}
"

example : scopedTypedefs.map (fun program =>
    ((program.symbolsNamed "x").length, (program.symbolsNamed "y").length)) =
    some (1, 1) := by native_decide

private def nominalTags : Option Program := analyzeSource? "
struct item { int outer; };
int f(void) {
  struct item { char inner; };
  struct item local;
  return 0;
}
"

example : nominalTags.map (fun program =>
    program.structs.map (fun info => (info.sourceName, info.canonicalName))) =
    some [("item_C", "item_C#0"), ("item_C", "item_C#1")] := by
  native_decide

private def nestedDefinition : Option Program := analyzeSource? "
struct outer { struct inner { int value; } field; };
"

example : nestedDefinition.map (fun program =>
    program.structs.map (fun info => (info.sourceName, info.size, info.complete))) =
    some [("outer_C", 4, true), ("inner_C", 4, true)] := by native_decide

example : (analyzeSource? "
int f(int x) {
  switch (x) { case 0: ; int y; break; default: break; }
  int y;
  return y;
}
").isSome := by native_decide

example : (analyzeSource? "
int x;
int f(void) { extern int x; return x; }
").map (fun program => (program.symbolsNamed "x").length) = some 1 := by
  native_decide

example : (analyzeSource? "
unsigned int x;
int f(void) {
  int x;
  { extern unsigned int x; return x; }
}
").map (fun program =>
    (program.symbolsNamed "x").length == 2 &&
      program.expressionTypes.map (·.type) == [.unsigned .int]) = some true := by
  native_decide

example : (analyzeSource? "
int f(int values[3]);
int f(int *values) { return values[0]; }
").isSome := by native_decide

private def isDuplicateSymbol : Except AnalysisError Program → Bool
  | .error (.duplicateSymbol _ _) => true
  | _ => false

private def isDuplicateTag : Except AnalysisError Program → Bool
  | .error (.duplicateTag _ _) => true
  | _ => false

private def isError : Except AnalysisError Program → Bool
  | .error _ => true
  | .ok _ => false

example : isDuplicateSymbol (analyzeResult "int x = 1; int x = 2;") := by
  native_decide

example : isError (analyzeResult "struct missing value;") := by native_decide

example : isDuplicateTag (analyzeResult "
struct pending { struct pending value; };
struct pending { int replacement; };
") := by native_decide

example : isError (analyzeResult "int *pointer = { 1 };") := by native_decide

example : isError (analyzeResult "int f(void); int value = f();") := by
  native_decide

private def isUndeclaredIdentifier : Except AnalysisError Program → Bool
  | .error (.undeclaredIdentifier _ "missing") => true
  | _ => false

example : isUndeclaredIdentifier (analyzeResult
    "int f(void) { return missing; }") := by native_decide

private def directCall : Option Program := analyzeSource? "
int callee(int value) { return value; }
int caller(void) { return callee(1); }
"

example : directCall.map (fun program =>
    (program.expressionTypes.length, program.calls.length)) = some (4, 1) := by
  native_decide

example : (analyzeSource? "
int invoke(int (*function)(int)) { return function(1); }
").map (fun program => program.calls.map (·.callee)) = some [none] := by
  native_decide

example : (analyzeSource? "
int callee(void) { return 1; }
int caller(void) { return sizeof(callee()); }
").map (fun program => program.calls.length) = some 0 := by native_decide

example : (analyzeSource? "int values[1 << 3];").isSome := by native_decide

example : (analyzeSource? "int values[sizeof(int)];").bind
    (fun program => (program.symbolsNamed "values").head?.map
      (fun symbol => symbol.type == .array (.signed .int) (some 4))) = some true := by
  native_decide

example : isError (analyzeResult "int values[(int *)1];") := by
  native_decide

example : isError (analyzeResult "int values[((int *)1) ? 2 : 3];") := by
  native_decide

example : isError (analyzeResult
    "unsigned long long value = 18446744073709551616;") := by
  native_decide

example : (analyzeSource? "int values[0xffffffffU + 2U];").bind
    (fun program => (program.symbolsNamed "values").head?.map
      (fun symbol => symbol.type == .array (.signed .int) (some 1))) = some true := by
  native_decide

example : isError (analyzeResult "int values[2147483647 + 1];") := by
  native_decide

example : isError (analyzeResult "int values[1U << 32];") := by
  native_decide

example : (analyzeSource? "int values[0 && (1 / 0) ? 1 : 4];").isSome := by
  native_decide

example : isError (analyzeResult "
int f(void) { int values[2], index[2]; return values[index]; }
") := by native_decide

example : isError (analyzeResult "
struct conflict { int value; };
enum conflict { conflict_value };
") := by native_decide

example : (analyzeSource? "unsigned long long value = 1LLU;").map
    (fun program => program.expressionTypes.any (·.type == .unsigned .longLong)) =
    some true := by native_decide

example : (analyzeSource? "int f(unsigned char value) { return -value; }").map
    (fun program => program.expressionTypes.any (·.type == .signed .int)) = some true := by
  native_decide

example : (analyzeSource? "int f(unsigned char value) { return ~value; }").map
    (fun program => program.expressionTypes.any (·.type == .signed .int)) = some true := by
  native_decide

example : isError (analyzeResult "
int *choose(int condition, int *pointer) { return condition ? pointer : 42; }
") := by native_decide

example : (analyzeSource? "
typedef int word;
int invoke(void *pointer) { return ((word (*)(void))pointer)(); }
").isSome := by native_decide

example : isError (analyzeResult
    "int f(void) { int *pointer; return pointer; }") := by native_decide

example : isError (analyzeResult "
int f(void) { enum { local_count = 4 }; int x[local_count]; return 0; }
int escaped[local_count];
") := by native_decide

private def invalidRecursiveValue : Except AnalysisError Program := do
  let translationUnit ← match (parseSource .arm "invalid.c"
      "struct loop { struct loop value; };").value with
    | some value => pure value
    | none => throw (.nonConstantExpression .bogus)
  analyze .arm translationUnit

private def isRecursiveValueError : Except AnalysisError Program → Bool
  | .error (.incompleteStruct _ name) => name == "loop_C"
  | _ => false

example : isRecursiveValueError invalidRecursiveValue := by native_decide

private def staticSummary (source : String) : Option (List (String × String)) := do
  let program ← analyzeSource? source
  program.staticObjects.mapM fun object => do
    let symbol ← program.symbolById? object.symbolId
    let initialization := match object.initialization with
      | .zero => "zero"
      | .explicit _ => "explicit"
    return (symbol.sourceName, initialization)

example : staticSummary "
    extern int declaration_only;
    int tentative;
    extern int defined = 3;
    static int file_static;
    int f(void) { static int local_static; return local_static; }
  " = some [
    ("tentative", "zero"),
    ("defined", "explicit"),
    ("file_static", "zero"),
    ("local_static", "zero")] := by
  native_decide

example : staticSummary "int value; int value;" =
    some [("value", "zero")] := by
  native_decide

example : staticSummary "int value; int value = 7;" =
    some [("value", "explicit")] := by
  native_decide

private def staticArraySizes (source : String) : Option (List (String × Option Int)) := do
  let program ← analyzeSource? source
  program.staticObjects.mapM fun object => do
    let symbol ← program.symbolById? object.symbolId
    let size := match symbol.type with
      | .array _ size => size
      | _ => none
    return (symbol.sourceName, size)

example : staticSummary "extern int declaration_only[];" = some [] := by
  native_decide

example : staticArraySizes "int tentative[];" =
    some [("tentative", some 1)] := by
  native_decide

example : staticArraySizes "int values[] = {1, 2, 3};" =
    some [("values", some 3)] := by
  native_decide

example : staticArraySizes "int values[] = {[2] = 4, 5};" =
    some [("values", some 4)] := by
  native_decide

example : isError (analyzeResult "int values[3] = {[3] = 1};") := by
  native_decide

example : isError (analyzeResult "int values[3] = {[2] = 1, 2};") := by
  native_decide

example : (analyzeSource? "struct S; extern struct S value;").isSome := by
  native_decide

example : isError (analyzeResult "struct S; struct S value;") := by
  native_decide

example : isError (analyzeResult "int first; static int second = first;") := by
  native_decide

example : isError (analyzeResult "_Thread_local int value;") := by
  native_decide

example : isError (analyzeResult "static extern int value;") := by
  native_decide

example : isError (analyzeResult "auto int value;") := by
  native_decide

example : isError (analyzeResult "int f(void) { _Thread_local int value; return 0; }") := by
  native_decide

example : (analyzeSource? "int *a = 1 - 1;").isSome := by
  native_decide

example : (analyzeSource? "int *b = (int)0;").isSome := by
  native_decide

example : (analyzeSource? "enum { Z }; int *c = Z;").isSome := by
  native_decide

private def deeplyNestedStructs : Option Program := analyzeSource? "
struct A { struct B { struct C { struct D { int x; } d; } c; } b; };
struct A value;
"

example : deeplyNestedStructs.map (fun program =>
    program.structs.filter (·.defined) |>.all (·.complete)) = some true := by
  native_decide

private def analyzedFunctionLinkage? (source name : String) : Option Linkage := do
  let program ← analyzeSource? source
  let symbol ← program.symbols.find? fun symbol =>
    symbol.sourceName = name && symbol.kind = .function
  symbol.linkage

example : analyzedFunctionLinkage? "static int helper(void) { return 0; }" "helper" =
    some .internal := by
  native_decide

example : analyzedFunctionLinkage?
    "static int helper(void); extern int helper(void); int helper(void) { return 0; }"
    "helper" = some .internal := by
  native_decide

example : isError (analyzeResult "int helper(void); static int helper(void) { return 0; }") := by
  native_decide

example : isError (analyzeResult "register int helper(void);") := by
  native_decide

example : (analyzeSource?
    "int compare(int *pointer) { return pointer == (1 - 1) || (int)0 != pointer; }").isSome := by
  native_decide

example : isError (analyzeResult "int compare(int *pointer) { return pointer == 1; }") := by
  native_decide

example : (analyzeSource?
    "typedef int local_int; int use_asm(int x) { asm(\"\" : : \"r\" ((local_int)x)); return x; }").isSome := by
  native_decide

example : isError (analyzeResult "int value = 1; int value = 2;") := by
  native_decide

end Zag.Test.AutoCorres.CParser.ProgramAnalysis
