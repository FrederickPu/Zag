import Std

/-!
# Program analysis

Corresponds only to [`tools/autocorres/prog.ML`](https://github.com/seL4/l4v/blob/bc2599a59c43e673dca021b10b9841e9b8da4430/tools/autocorres/prog.ML).

This is a pure port of the decorated program tree and its basic analyses. The
finite-set implementation is local because this project deliberately has no
external collection dependency.
-/

namespace Zag.Lang.AutoCorres.ML.Prog

universe u v w x y

/-- A finite set with its representation hidden from clients. -/
structure Finset (α : Type u) where
  private mk ::
  elements : List α
  deriving Repr

namespace Finset

def empty : Finset α :=
  .mk []

private def listContains [DecidableEq α] (value : α) : List α -> Bool
  | [] => false
  | head :: tail => if value = head then true else listContains value tail

def contains [DecidableEq α] (set : Finset α) (value : α) : Bool :=
  listContains value set.elements

def insert [DecidableEq α] (value : α) (set : Finset α) : Finset α :=
  if set.contains value then set else .mk (value :: set.elements)

def make [DecidableEq α] (values : List α) : Finset α :=
  values.foldl (fun set value => set.insert value) empty

def union [DecidableEq α] (left right : Finset α) : Finset α :=
  right.elements.foldl (fun set value => set.insert value) left

def unions [DecidableEq α] (sets : List (Finset α)) : Finset α :=
  sets.foldl union empty

def inter [DecidableEq α] (left right : Finset α) : Finset α :=
  .mk (left.elements.filter fun value => right.contains value)

def subtract [DecidableEq α] (removed source : Finset α) : Finset α :=
  .mk (source.elements.filter fun value => !(removed.contains value))

def subset [DecidableEq α] (left right : Finset α) : Bool :=
  left.elements.all fun value => right.contains value

/-- Extensional equality, independent of insertion order. -/
def equal [DecidableEq α] (left right : Finset α) : Bool :=
  left.subset right && right.subset left

def card (set : Finset α) : Nat :=
  set.elements.length

end Finset

/-! Convenience abbreviations for set manipulation. -/

def emptySet : Finset α :=
  Finset.empty

def makeSet [DecidableEq α] (values : List α) : Finset α :=
  Finset.make values

def unionSets [DecidableEq α] (sets : List (Finset α)) : Finset α :=
  Finset.unions sets

def inter [DecidableEq α] (left right : Finset α) : Finset α :=
  Finset.inter left right

def minus [DecidableEq α] (left right : Finset α) : Finset α :=
  Finset.subtract right left

def union [DecidableEq α] (left right : Finset α) : Finset α :=
  Finset.union left right

/-- A parsed program with independent decorations for nodes, expressions, modifications, and calls. -/
inductive Prog (Node : Type u) (Expr : Type v) (Modification : Type w) (Call : Type x) where
  | init (data : Node) (modified : Modification)
  | modify (data : Node) (expression : Expr) (modified : Modification)
  | guard (data : Node) (expression : Expr)
  | throw (data : Node)
  | call (data : Node) (arguments : List Expr) (returnExpression : Expr)
      (modified : Modification) (callData : Call)
  | spec (data : Node) (expression : Expr)
  | fail (data : Node)
  | while (data : Node) (expression : Expr) (body : Prog Node Expr Modification Call)
  | condition (data : Node) (expression : Expr)
      (thenProgram elseProgram : Prog Node Expr Modification Call)
  | seq (data : Node) (left right : Prog Node Expr Modification Call)
  | catch (data : Node) (body handler : Prog Node Expr Modification Call)
  | recGuard (data : Node) (body : Prog Node Expr Modification Call)
  deriving Repr

inductive CallType where
  | decMeasure
  | newMeasure
  deriving DecidableEq, Repr

/-- Extract the data associated with the root node. -/
def getNodeData : Prog Node Expr Modification Call -> Node
  | .init data _ => data
  | .modify data _ _ => data
  | .guard data _ => data
  | .throw data => data
  | .call data _ _ _ _ => data
  | .spec data _ => data
  | .fail data => data
  | .while data _ _ => data
  | .condition data _ _ _ => data
  | .seq data _ _ => data
  | .catch data _ _ => data
  | .recGuard data _ => data

/-- Failure corresponding to differently shaped program trees. -/
inductive ZipError where
  | structureMismatch
  deriving DecidableEq, Repr

/--
Merge the payloads of two structurally identical programs. Paired call arguments
follow upstream `Utils.zip` and truncate to the common prefix.
-/
def zipProgs {Node₁ : Type u} {Expr₁ : Type v} {Modification₁ : Type w} {Call₁ : Type x}
    {Node₂ : Type y} {Expr₂ : Type u₁} {Modification₂ : Type v₁} {Call₂ : Type w₁} :
    Prog Node₁ Expr₁ Modification₁ Call₁ -> Prog Node₂ Expr₂ Modification₂ Call₂ ->
      Except ZipError
        (Prog (Node₁ × Node₂) (Expr₁ × Expr₂) (Modification₁ × Modification₂)
          (Call₁ × Call₂))
  | .init data₁ modified₁, .init data₂ modified₂ =>
      .ok (.init (data₁, data₂) (modified₁, modified₂))
  | .modify data₁ expression₁ modified₁, .modify data₂ expression₂ modified₂ =>
      .ok (.modify (data₁, data₂) (expression₁, expression₂) (modified₁, modified₂))
  | .guard data₁ expression₁, .guard data₂ expression₂ =>
      .ok (.guard (data₁, data₂) (expression₁, expression₂))
  | .throw data₁, .throw data₂ =>
      .ok (.throw (data₁, data₂))
  | .call data₁ arguments₁ returnExpression₁ modified₁ callData₁,
      .call data₂ arguments₂ returnExpression₂ modified₂ callData₂ =>
      .ok (.call (data₁, data₂) (List.zip arguments₁ arguments₂)
        (returnExpression₁, returnExpression₂) (modified₁, modified₂) (callData₁, callData₂))
  | .spec data₁ expression₁, .spec data₂ expression₂ =>
      .ok (.spec (data₁, data₂) (expression₁, expression₂))
  | .fail data₁, .fail data₂ =>
      .ok (.fail (data₁, data₂))
  | .while data₁ expression₁ body₁, .while data₂ expression₂ body₂ => do
      let body <- zipProgs body₁ body₂
      pure (.while (data₁, data₂) (expression₁, expression₂) body)
  | .condition data₁ expression₁ thenProgram₁ elseProgram₁,
      .condition data₂ expression₂ thenProgram₂ elseProgram₂ => do
      let thenProgram <- zipProgs thenProgram₁ thenProgram₂
      let elseProgram <- zipProgs elseProgram₁ elseProgram₂
      pure (.condition (data₁, data₂) (expression₁, expression₂) thenProgram elseProgram)
  | .seq data₁ left₁ right₁, .seq data₂ left₂ right₂ => do
      let left <- zipProgs left₁ left₂
      let right <- zipProgs right₁ right₂
      pure (.seq (data₁, data₂) left right)
  | .catch data₁ body₁ handler₁, .catch data₂ body₂ handler₂ => do
      let body <- zipProgs body₁ body₂
      let handler <- zipProgs handler₁ handler₂
      pure (.catch (data₁, data₂) body handler)
  | .recGuard data₁ body₁, .recGuard data₂ body₂ => do
      let body <- zipProgs body₁ body₂
      pure (.recGuard (data₁, data₂) body)
  | _, _ => .error .structureMismatch

/-! ## `zipProgs` reduction pins -/

theorem zipProgs_call_arguments_left_longer :
    zipProgs
      (.call 1 [10, 11] 12 13 14 : Prog Nat Nat Nat Nat)
      (.call 2 [20] 22 23 24 : Prog Nat Nat Nat Nat) =
        .ok (.call (1, 2) [(10, 20)] (12, 22) (13, 23) (14, 24) :
          Prog (Nat × Nat) (Nat × Nat) (Nat × Nat) (Nat × Nat)) := by
  rfl

theorem zipProgs_call_arguments_right_longer :
    zipProgs
      (.call 1 [10] 12 13 14 : Prog Nat Nat Nat Nat)
      (.call 2 [20, 21] 22 23 24 : Prog Nat Nat Nat Nat) =
        .ok (.call (1, 2) [(10, 20)] (12, 22) (13, 23) (14, 24) :
          Prog (Nat × Nat) (Nat × Nat) (Nat × Nat) (Nat × Nat)) := by
  rfl

/-- Map each kind of decoration throughout a program. -/
def mapProg (nodeFn : Node₁ -> Node₂) (exprFn : Expr₁ -> Expr₂)
    (modFn : Modification₁ -> Modification₂) (callFn : Call₁ -> Call₂) :
    Prog Node₁ Expr₁ Modification₁ Call₁ -> Prog Node₂ Expr₂ Modification₂ Call₂
  | .init data modified => .init (nodeFn data) (modFn modified)
  | .modify data expression modified =>
      .modify (nodeFn data) (exprFn expression) (modFn modified)
  | .guard data expression => .guard (nodeFn data) (exprFn expression)
  | .throw data => .throw (nodeFn data)
  | .call data arguments returnExpression modified callData =>
      .call (nodeFn data) (arguments.map exprFn) (exprFn returnExpression)
        (modFn modified) (callFn callData)
  | .spec data expression => .spec (nodeFn data) (exprFn expression)
  | .fail data => .fail (nodeFn data)
  | .while data expression body =>
      .while (nodeFn data) (exprFn expression) (mapProg nodeFn exprFn modFn callFn body)
  | .condition data expression thenProgram elseProgram =>
      .condition (nodeFn data) (exprFn expression)
        (mapProg nodeFn exprFn modFn callFn thenProgram)
        (mapProg nodeFn exprFn modFn callFn elseProgram)
  | .seq data left right =>
      .seq (nodeFn data) (mapProg nodeFn exprFn modFn callFn left)
        (mapProg nodeFn exprFn modFn callFn right)
  | .catch data body handler =>
      .catch (nodeFn data) (mapProg nodeFn exprFn modFn callFn body)
        (mapProg nodeFn exprFn modFn callFn handler)
  | .recGuard data body =>
      .recGuard (nodeFn data) (mapProg nodeFn exprFn modFn callFn body)

/-- Fold all decorations in pre-order. -/
def foldProg (nodeFn : Node -> Accumulator -> Accumulator)
    (exprFn : Expr -> Accumulator -> Accumulator)
    (modFn : Modification -> Accumulator -> Accumulator)
    (callFn : Call -> Accumulator -> Accumulator) :
    Prog Node Expr Modification Call -> Accumulator -> Accumulator
  | .init data modified, value => modFn modified (nodeFn data value)
  | .modify data expression modified, value =>
      modFn modified (exprFn expression (nodeFn data value))
  | .guard data expression, value => exprFn expression (nodeFn data value)
  | .throw data, value => nodeFn data value
  | .call data arguments returnExpression modified callData, value =>
      callFn callData (modFn modified (exprFn returnExpression
        (arguments.foldl (fun result expression => exprFn expression result)
          (nodeFn data value))))
  | .spec data expression, value => exprFn expression (nodeFn data value)
  | .fail data, value => nodeFn data value
  | .while data expression body, value =>
      foldProg nodeFn exprFn modFn callFn body (exprFn expression (nodeFn data value))
  | .condition data expression thenProgram elseProgram, value =>
      foldProg nodeFn exprFn modFn callFn elseProgram
        (foldProg nodeFn exprFn modFn callFn thenProgram
          (exprFn expression (nodeFn data value)))
  | .seq data left right, value =>
      foldProg nodeFn exprFn modFn callFn right
        (foldProg nodeFn exprFn modFn callFn left (nodeFn data value))
  | .catch data body handler, value =>
      foldProg nodeFn exprFn modFn callFn handler
        (foldProg nodeFn exprFn modFn callFn body (nodeFn data value))
  | .recGuard data body, value =>
      foldProg nodeFn exprFn modFn callFn body (nodeFn data value)

private def setFromSome [DecidableEq Var] : Option Var -> Finset Var
  | none => emptySet
  | some item => makeSet [item]

/-- One backward liveness pass over an already read-set-decorated program. -/
def calcLiveVarsPass [DecidableEq Var] :
    Prog (Finset Var) (Finset Var) (Option Var) Call -> Finset Var -> Finset Var ->
      Prog (Finset Var) (Finset Var) (Option Var) Call
  | .init old writtenVars, succLive, _ =>
      .init (union old (minus succLive (setFromSome writtenVars))) writtenVars
  | .modify old readVars writtenVars, succLive, _ =>
      .modify (union (union old readVars) (minus succLive (setFromSome writtenVars)))
        readVars writtenVars
  | .call old readVars returnReadVars writtenVars callData, succLive, _ =>
      .call (union (union (union old (unionSets readVars)) returnReadVars)
          (minus succLive (setFromSome writtenVars)))
        readVars returnReadVars writtenVars callData
  | .guard old readVars, succLive, _ =>
      .guard (union (union old succLive) readVars) readVars
  | .throw _, _, throwLive => .throw throwLive
  | .spec old readVars, _, _ => .spec (union old readVars) readVars
  | .fail _, succLive, _ => .fail succLive
  | .while old readVars body, succLive, throwLive =>
      let newBody := calcLiveVarsPass body (union succLive old) throwLive
      .while (union (union old (getNodeData newBody)) readVars) readVars newBody
  | .condition old readVars thenProgram elseProgram, succLive, throwLive =>
      let newThen := calcLiveVarsPass thenProgram succLive throwLive
      let newElse := calcLiveVarsPass elseProgram succLive throwLive
      .condition (union (union (union old (getNodeData newThen))
          (getNodeData newElse)) readVars) readVars newThen newElse
  | .seq old left right, succLive, throwLive =>
      let newRight := calcLiveVarsPass right succLive throwLive
      let newLeft := calcLiveVarsPass left (getNodeData newRight) throwLive
      .seq (union old (getNodeData newLeft)) newLeft newRight
  | .catch old body handler, succLive, throwLive =>
      let newHandler := calcLiveVarsPass handler succLive throwLive
      let newBody := calcLiveVarsPass body succLive (getNodeData newHandler)
      .catch (union old (getNodeData newBody)) newBody newHandler
  | .recGuard old body, succLive, throwLive =>
      let newBody := calcLiveVarsPass body succLive throwLive
      .recGuard (union old (getNodeData newBody)) newBody

private def sameLiveData [DecidableEq Var] :
    Prog (Finset Var) Expr Modification Call ->
      Prog (Finset Var) Expr Modification Call -> Bool
  | .init left _, .init right _ => left.equal right
  | .modify left _ _, .modify right _ _ => left.equal right
  | .guard left _, .guard right _ => left.equal right
  | .throw left, .throw right => left.equal right
  | .call left _ _ _ _, .call right _ _ _ _ => left.equal right
  | .spec left _, .spec right _ => left.equal right
  | .fail left, .fail right => left.equal right
  | .while left _ leftBody, .while right _ rightBody =>
      left.equal right && sameLiveData leftBody rightBody
  | .condition left _ leftThen leftElse, .condition right _ rightThen rightElse =>
      left.equal right && sameLiveData leftThen rightThen && sameLiveData leftElse rightElse
  | .seq left leftFirst leftSecond, .seq right rightFirst rightSecond =>
      left.equal right && sameLiveData leftFirst rightFirst && sameLiveData leftSecond rightSecond
  | .catch left leftBody leftHandler, .catch right rightBody rightHandler =>
      left.equal right && sameLiveData leftBody rightBody && sameLiveData leftHandler rightHandler
  | .recGuard left leftBody, .recGuard right rightBody =>
      left.equal right && sameLiveData leftBody rightBody
  | _, _ => false

private def liveFixpoint [DecidableEq Var]
    (step : Prog (Finset Var) Expr Modification Call ->
      Prog (Finset Var) Expr Modification Call) :
    Nat -> Prog (Finset Var) Expr Modification Call ->
      Prog (Finset Var) Expr Modification Call
  | 0, current => current
  | fuel + 1, current =>
      let next := step current
      if sameLiveData current next then current else liveFixpoint step fuel next

/--
Compute live variables to a fixed point. The finite bound counts every possible
new `(node, variable)` fact in the universe formed by reads and requested outputs.
-/
def calcLiveVars [DecidableEq Var]
    (program : Prog Node (Head × Finset Var × Tail) (Option Var) Call)
    (outputVars : Finset Var) : Prog (Finset Var) (Finset Var) (Option Var) Call :=
  let initial := mapProg (fun _ => emptySet) (fun expression => expression.2.1)
    (fun modified => modified) (fun callData => callData) program
  let relevantVars := foldProg (fun _ variables => variables)
    (fun expression variables => union expression.2.1 variables)
    (fun _ variables => variables) (fun _ variables => variables) program outputVars
  let nodeCount := foldProg (fun _ count => count + 1) (fun _ count => count)
    (fun _ count => count) (fun _ count => count) program 0
  liveFixpoint (fun current => calcLiveVarsPass current outputVars emptySet)
    (nodeCount * relevantVars.card + 1) initial

/-- Decorate each node with all variables read in its subtree. -/
def getReadVars [DecidableEq Var] :
    Prog Node (Finset Var) Modification Call ->
      Prog (Finset Var) (Finset Var) Modification Call
  | .init _ modified => .init emptySet modified
  | .modify _ readVars modified => .modify readVars readVars modified
  | .call _ readVars returnReadVars modified callData =>
      .call (unionSets readVars) readVars returnReadVars modified callData
  | .guard _ readVars => .guard readVars readVars
  | .throw _ => .throw emptySet
  | .spec _ readVars => .spec readVars readVars
  | .fail _ => .fail emptySet
  | .while _ readVars body =>
      let newBody := getReadVars body
      .while (union (getNodeData newBody) readVars) readVars newBody
  | .condition _ readVars thenProgram elseProgram =>
      let newThen := getReadVars thenProgram
      let newElse := getReadVars elseProgram
      .condition (union (union (getNodeData newThen) (getNodeData newElse)) readVars)
        readVars newThen newElse
  | .seq _ left right =>
      let newLeft := getReadVars left
      let newRight := getReadVars right
      .seq (union (getNodeData newLeft) (getNodeData newRight)) newLeft newRight
  | .catch _ body handler =>
      let newBody := getReadVars body
      let newHandler := getReadVars handler
      .catch (union (getNodeData newBody) (getNodeData newHandler)) newBody newHandler
  | .recGuard _ body =>
      let newBody := getReadVars body
      .recGuard (getNodeData newBody) newBody

/-- `none` is the conservative top/unknown modification set. -/
abbrev ModificationSet (Var : Type u) := Option (Finset Var)

private def unionModified [DecidableEq Var] :
    ModificationSet Var -> ModificationSet Var -> ModificationSet Var
  | some left, some right => some (union left right)
  | _, _ => none

/-- Decorate each node with its conservative modification set. -/
def getModifiedVars [DecidableEq Var] :
    Prog Node Expr (Option Var) Call -> Prog (ModificationSet Var) Expr (Option Var) Call
  | .init _ writtenVars => .init (some (setFromSome writtenVars)) writtenVars
  | .modify _ expression writtenVars =>
      .modify (some (setFromSome writtenVars)) expression writtenVars
  | .call _ arguments returnExpression writtenVars callData =>
      .call (some (setFromSome writtenVars)) arguments returnExpression writtenVars callData
  | .guard _ expression => .guard (some emptySet) expression
  | .throw _ => .throw (some emptySet)
  | .spec _ expression => .spec none expression
  | .fail _ => .fail (some emptySet)
  | .while _ expression body =>
      let newBody := getModifiedVars body
      .while (getNodeData newBody) expression newBody
  | .condition _ expression thenProgram elseProgram =>
      let newThen := getModifiedVars thenProgram
      let newElse := getModifiedVars elseProgram
      .condition (unionModified (getNodeData newThen) (getNodeData newElse))
        expression newThen newElse
  | .seq _ left right =>
      let newLeft := getModifiedVars left
      let newRight := getModifiedVars right
      .seq (unionModified (getNodeData newLeft) (getNodeData newRight)) newLeft newRight
  | .catch _ body handler =>
      let newBody := getModifiedVars body
      let newHandler := getModifiedVars handler
      .catch (unionModified (getNodeData newBody) (getNodeData newHandler))
        newBody newHandler
  | .recGuard _ body =>
      let newBody := getModifiedVars body
      .recGuard (getNodeData newBody) newBody

/-! ## Liveness reduction theorems -/

theorem calcLiveVarsPass_seq [DecidableEq Var]
    (old succLive throwLive : Finset Var)
    (left right : Prog (Finset Var) (Finset Var) (Option Var) Call) :
    calcLiveVarsPass (.seq old left right) succLive throwLive =
      let newRight := calcLiveVarsPass right succLive throwLive
      let newLeft := calcLiveVarsPass left (getNodeData newRight) throwLive
      .seq (union old (getNodeData newLeft)) newLeft newRight := by
  rfl

theorem calcLiveVarsPass_catch [DecidableEq Var]
    (old succLive throwLive : Finset Var)
    (body handler : Prog (Finset Var) (Finset Var) (Option Var) Call) :
    calcLiveVarsPass (.catch old body handler) succLive throwLive =
      let newHandler := calcLiveVarsPass handler succLive throwLive
      let newBody := calcLiveVarsPass body succLive (getNodeData newHandler)
      .catch (union old (getNodeData newBody)) newBody newHandler := by
  rfl

theorem calcLiveVarsPass_while [DecidableEq Var]
    (old readVars succLive throwLive : Finset Var)
    (body : Prog (Finset Var) (Finset Var) (Option Var) Call) :
    calcLiveVarsPass (.while old readVars body) succLive throwLive =
      let newBody := calcLiveVarsPass body (union succLive old) throwLive
      .while (union (union old (getNodeData newBody)) readVars) readVars newBody := by
  rfl

end Zag.Lang.AutoCorres.ML.Prog
