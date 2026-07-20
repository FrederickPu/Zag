import Zag.Theory

namespace Zag.Lang.SSA

open Zag

structure SSAVar where
  name : String
  ty : Ty

namespace SSAVar

def tys (vars : List SSAVar) : List Ty :=
  vars.map SSAVar.ty

def tyIndex {vars : List SSAVar} (idx : Fin vars.length) : Fin ((SSAVar.tys vars).length) :=
  Fin.mk idx.val (by simp [tys, idx.isLt])

def packState {primCtx : PrimitiveCtx} (vars : List SSAVar) (terms : List (Term primCtx)) : Term primCtx :=
  match vars, terms with
  | [_], [term] => term
  | _, _ => .app (.mkStruct (SSAVar.tys vars)) terms

end SSAVar

structure LoopScope (state : List SSAVar) where
  base : Nat
  resultTy : Ty

def LoopScope.stateTys {state : List SSAVar} (_scope : LoopScope state) : List Ty :=
  SSAVar.tys state

def LoopScope.stateTy {state : List SSAVar} (scope : LoopScope state) : Ty :=
  .struct scope.stateTys

def LoopScope.motiveTy {state : List SSAVar} (scope : LoopScope state) : Ty :=
  .func [scope.stateTy] scope.resultTy

abbrev Env (primCtx : PrimitiveCtx) := List (String × Term primCtx)

def Env.lookup? {primCtx : PrimitiveCtx} (env : Env primCtx) (name : String) : Option (Term primCtx) :=
  (env.find? (·.1 = name)).map (·.2)

structure LoopLowerCtx where
  base : Nat
  state : List SSAVar

structure LowerCtx (primCtx : PrimitiveCtx) where
  vars : Env primCtx := []
  loop? : Option LoopLowerCtx := none

def LoopScope.phiTerm {primCtx : PrimitiveCtx} {state : List SSAVar} (scope : LoopScope state)
    (idx : Fin state.length) : Term primCtx :=
  if state.length = 1 then
    .var scope.base
  else
    .app (.structProj (SSAVar.tys state) (SSAVar.tyIndex idx)) [.var scope.base]

def LoopScope.phiEnv {primCtx : PrimitiveCtx} {state : List SSAVar} (scope : LoopScope state) : Env primCtx :=
  (List.finRange state.length).map fun idx => (state[idx].name, scope.phiTerm idx)

mutual

inductive SSAValue (primCtx : PrimitiveCtx) where
| raw (term : Term primCtx)
| var (name : String)
| call (fn : SSAValue primCtx) (args : List (SSAValue primCtx))
| struct (tys : List Ty) (fields : List (SSAValue primCtx))
| field (tys : List Ty) (idx : Fin tys.length) (value : SSAValue primCtx)
| primEq (lhs rhs : SSAValue primCtx)
| primLt (lhs rhs : SSAValue primCtx)
| primGt (lhs rhs : SSAValue primCtx)
/- access variable from scope -/
| phi {state : List SSAVar} (scope : LoopScope state) (idx : Fin state.length)
| loopBody
    (varCtx : VarCtx)
    (state : List SSAVar)
    (init : List (SSAValue primCtx))
    (resultTy : Ty)
    (body : SSAExpr primCtx)

inductive SSAExpr (primCtx : PrimitiveCtx) where
| ret (value : SSAValue primCtx)
| let_ (name : String) (value : SSAValue primCtx) (next : SSAExpr primCtx)
| ite (cond : SSAValue primCtx) (thenExpr elseExpr : SSAExpr primCtx)
| yield (next : List (SSAValue primCtx))

end

namespace SSAValue

def prim {primCtx : PrimitiveCtx} (ty : Ty) (value : Ty.type primCtx ty) : SSAValue primCtx :=
  .raw (.prim ty value)

def nat {primCtx : PrimitiveCtx} (value : Nat) : SSAValue primCtx :=
  .raw (Term.nat value)

def bool {primCtx : PrimitiveCtx} (value : Bool) : SSAValue primCtx :=
  .raw (Term.bool value)

def primFunc {primCtx : PrimitiveCtx} (name : String) : SSAValue primCtx :=
  .raw (.primFunc name)

def scopedLoop {primCtx : PrimitiveCtx} (varCtx : VarCtx) (state : List SSAVar) (init : List (SSAValue primCtx))
    (resultTy : Ty) (body : (scope : LoopScope state) -> SSAExpr primCtx) : SSAValue primCtx :=
  .loopBody varCtx state init resultTy (body { base := 0, resultTy := resultTy })

end SSAValue

namespace SSAExpr

def seq {primCtx : PrimitiveCtx} (bindings : List (String × SSAValue primCtx)) (result : SSAValue primCtx) : SSAExpr primCtx :=
  bindings.foldr (fun binding next => .let_ binding.1 binding.2 next) (.ret result)

mutual

def valueToTerm? {primCtx : PrimitiveCtx} : SSAValue primCtx -> LowerCtx primCtx -> Option (Term primCtx)
| .raw term, _ctx => some term
| .var name, ctx => ctx.vars.lookup? name
| .call fn args, ctx => do
    let fnTerm <- valueToTerm? fn ctx
    let argTerms <- valuesToTerms? args ctx
    some (.app fnTerm argTerms)
| .struct tys fields, ctx => do
    let fieldTerms <- valuesToTerms? fields ctx
    some (.app (.mkStruct tys) fieldTerms)
| .field tys idx value, ctx => do
    let term <- valueToTerm? value ctx
    some (.app (.structProj tys idx) [term])
| .primEq lhs rhs, ctx => do
    let lhsTerm <- valueToTerm? lhs ctx
    let rhsTerm <- valueToTerm? rhs ctx
    some (.primEq lhsTerm rhsTerm)
| .primLt lhs rhs, ctx => do
    let lhsTerm <- valueToTerm? lhs ctx
    let rhsTerm <- valueToTerm? rhs ctx
    some (.primLt lhsTerm rhsTerm)
| .primGt lhs rhs, ctx => do
    let lhsTerm <- valueToTerm? lhs ctx
    let rhsTerm <- valueToTerm? rhs ctx
    some (.primGt lhsTerm rhsTerm)
| @SSAValue.phi _ _ scope idx, _ctx =>
    some (scope.phiTerm idx)
| .loopBody _varCtx state init resultTy body, ctx => do
    let initTerms <- valuesToTerms? init ctx
    let base := 0
    let scope : LoopScope state := { base := base, resultTy := resultTy }
    let bodyTerm <- toTerm?
      body
      { vars := scope.phiEnv ++ ctx.vars
        loop? := some { base := base, state := state } }
    some (.recurse resultTy (SSAVar.packState state initTerms) bodyTerm)

def valuesToTerms? {primCtx : PrimitiveCtx} : List (SSAValue primCtx) -> LowerCtx primCtx -> Option (List (Term primCtx))
| [], _ctx => some []
| expr :: exprs, ctx => do
    let term <- valueToTerm? expr ctx
    let terms <- valuesToTerms? exprs ctx
    some (term :: terms)

def toTerm? {primCtx : PrimitiveCtx} : SSAExpr primCtx -> LowerCtx primCtx -> Option (Term primCtx)
| .ret value, ctx => valueToTerm? value ctx
| .let_ name value next, ctx => do
    let term <- valueToTerm? value ctx
    toTerm? next { ctx with vars := (name, term) :: ctx.vars }
| .ite cond thenExpr elseExpr, ctx => do
    let condTerm <- valueToTerm? cond ctx
    let thenTerm <- toTerm? thenExpr ctx
    let elseTerm <- toTerm? elseExpr ctx
    some (.ite condTerm thenTerm elseTerm)
| .yield next, ctx =>
    match ctx.loop? with
    | none => none
    | some loop => do
        let nextTerms <- valuesToTerms? next ctx
        some (.app (.var (loop.base + 1)) [SSAVar.packState loop.state nextTerms])

end

def toTerm {primCtx : PrimitiveCtx} (expr : SSAExpr primCtx) : Term primCtx :=
  (toTerm? expr {}).getD (.var 0)

end SSAExpr

def LoopScope.phi {primCtx : PrimitiveCtx} {state : List SSAVar} (scope : LoopScope state)
    (idx : Fin state.length) : SSAValue primCtx :=
  .phi scope idx

def LoopScope.yield {primCtx : PrimitiveCtx} {state : List SSAVar} (_scope : LoopScope state)
    (next : List (SSAValue primCtx)) : SSAExpr primCtx :=
  .yield next

declare_syntax_cat ssaExpr
declare_syntax_cat ssaValue
declare_syntax_cat ssaTy
declare_syntax_cat ssaStates

syntax "ssa%" "{" ssaExpr "}" : term
syntax "ssaExpr%" ssaExpr : term
syntax "ssaValue%" ssaValue : term
syntax "ssaName%" ident : term
syntax "ssaStateVars%" "[" ssaStates "]" : term
syntax "ssaStateInits%" "[" ssaStates "]" : term
syntax "ssaTy%" ssaTy : term

syntax ident : ssaTy
syntax str : ssaTy
syntax "(" term ")" : ssaTy
syntax ident ":" ssaTy ":=" ssaValue : ssaStates
syntax ident ":" ssaTy ":=" ssaValue "," ssaStates : ssaStates

syntax ssaValue : ssaExpr
syntax ident ":=" ssaValue ";" ssaExpr : ssaExpr
syntax "if" ssaValue "{" ssaExpr "}" "else" "{" ssaExpr "}" : ssaExpr
syntax "yield" ident,* : ssaExpr

syntax "raw(" term ")" : ssaValue
syntax "term(" term ")" : ssaValue
syntax ident : ssaValue
syntax "var(" term ")" : ssaValue
syntax "prim(" term ":" term ")" : ssaValue
syntax "prim(" term ")" : ssaValue
syntax "func(" term ")" : ssaValue
syntax "call" ident "[" ident,* "]" : ssaValue
syntax "struct(" term "," "[" ident,* "]" ")" : ssaValue
syntax "field(" term "," term "," ssaValue ")" : ssaValue
syntax "eq" ident ident : ssaValue
syntax "lt" ident ident : ssaValue
syntax "gt" ident ident : ssaValue
syntax "loop" "(" ssaStates ")" ":" ssaTy "{" ssaExpr "}" : ssaValue
syntax "loop" "(" ssaStates ")" "{" ssaExpr "}" : ssaValue

set_option linter.unusedVariables false in
macro_rules
  | `(ssa% { $body:ssaExpr }) => `(ssaExpr% $body)
  | `(ssaName% $name:ident) =>
      pure (Lean.Syntax.mkStrLit name.getId.toString)
  | `(ssaTy% Bool) => `((.prim "Bool" : Ty))
  | `(ssaTy% $ty:ident) => do
      `((.prim (ssaName% $ty) : Ty))
  | `(ssaTy% $name:str) => `((.prim $name : Ty))
  | `(ssaTy% ($ty:term)) => `(($ty : Ty))
  | `(ssaExpr% $value:ssaValue) => `(SSAExpr.ret (ssaValue% $value))
  | `(ssaExpr% $var:ident := $value:ssaValue; $next:ssaExpr) =>
      `(SSAExpr.let_ (ssaName% $var) (ssaValue% $value) (ssaExpr% $next))
  | `(ssaExpr% if $cond:ssaValue { $thenExpr:ssaExpr } else { $elseExpr:ssaExpr }) =>
      `(SSAExpr.ite (ssaValue% $cond) (ssaExpr% $thenExpr) (ssaExpr% $elseExpr))
  | `(ssaExpr% yield $next:ident,*) =>
      `(SSAExpr.yield [ $[SSAValue.var (ssaName% $next)],* ])
  | `(ssaValue% raw($term:term)) => `(SSAValue.raw $term)
  | `(ssaValue% term($term:term)) => `(($term : SSAValue _))
  | `(ssaValue% $var:ident) => `(SSAValue.var (ssaName% $var))
  | `(ssaValue% var($var:term)) => `(SSAValue.var $var)
  | `(ssaValue% prim($value:term : Nat)) => `(SSAValue.nat (($value : Nat)))
  | `(ssaValue% prim($value:term : Bool)) => `(SSAValue.bool (($value : Bool)))
  | `(ssaValue% prim($value:term)) => `(SSAValue.nat (($value : Nat)))
  | `(ssaValue% func($name:term)) => `(SSAValue.primFunc $name)
  | `(ssaValue% call $fn:ident [ $args:ident,* ]) =>
      `(SSAValue.call (SSAValue.primFunc (ssaName% $fn)) [ $[SSAValue.var (ssaName% $args)],* ])
  | `(ssaValue% struct($tys:term, [ $fields:ident,* ])) =>
      `(SSAValue.struct $tys [ $[SSAValue.var (ssaName% $fields)],* ])
  | `(ssaValue% field($tys:term, $idx:term, $value:ssaValue)) =>
      `(SSAValue.field $tys $idx (ssaValue% $value))
  | `(ssaValue% eq $lhs:ident $rhs:ident) =>
      `(SSAValue.primEq (SSAValue.var (ssaName% $lhs)) (SSAValue.var (ssaName% $rhs)))
  | `(ssaValue% lt $lhs:ident $rhs:ident) =>
      `(SSAValue.primLt (SSAValue.var (ssaName% $lhs)) (SSAValue.var (ssaName% $rhs)))
  | `(ssaValue% gt $lhs:ident $rhs:ident) =>
      `(SSAValue.primGt (SSAValue.var (ssaName% $lhs)) (SSAValue.var (ssaName% $rhs)))
  | `(ssaValue% loop ( $states:ssaStates ) : $resultTy:ssaTy { $body:ssaExpr }) =>
      `(SSAValue.loopBody (List.nil : VarCtx)
          (ssaStateVars% [ $states ])
          (ssaStateInits% [ $states ])
          (ssaTy% $resultTy)
          (ssaExpr% $body))
  | `(ssaValue% loop ( $states:ssaStates ) { $body:ssaExpr }) =>
      `(SSAValue.loopBody (List.nil : VarCtx)
          (ssaStateVars% [ $states ])
          (ssaStateInits% [ $states ])
          (.struct (SSAVar.tys (ssaStateVars% [ $states ])))
          (ssaExpr% $body))
  | `(ssaStateVars% [ $name:ident : $ty:ssaTy := $init:ssaValue ]) =>
      `([{ name := ssaName% $name, ty := (ssaTy% $ty) }])
  | `(ssaStateVars% [ $name:ident : $ty:ssaTy := $init:ssaValue, $rest:ssaStates ]) =>
      `({ name := ssaName% $name, ty := (ssaTy% $ty) } :: (ssaStateVars% [ $rest ]))
  | `(ssaStateInits% [ $name:ident : $ty:ssaTy := $init:ssaValue ]) =>
      `([ssaValue% $init])
  | `(ssaStateInits% [ $name:ident : $ty:ssaTy := $init:ssaValue, $rest:ssaStates ]) =>
      `((ssaValue% $init) :: (ssaStateInits% [ $rest ]))

namespace Examples

abbrev exampleCtx : PrimitiveCtx := [("Nat", Nat)]

def NatTy : Ty :=
  .prim "Nat"

def identitySeq : SSAExpr exampleCtx :=
  SSAExpr.seq [("x", .nat 1)] (.var "x")

def identitySeqSyntax : SSAExpr exampleCtx :=
  ssa% {
    x := prim(1 : Nat);
    x
  }

def addSyntax : SSAExpr exampleCtx :=
  ssa% {
    x := prim(1 : Nat);
    y := call add [x, x];
    y
  }

def swapState : List SSAVar :=
  [ { name := "a", ty := NatTy }
  , { name := "b", ty := NatTy }
  ]

def swapLoop : SSAExpr exampleCtx :=
  .ret <| SSAValue.scopedLoop (List.nil : VarCtx) swapState [.nat 0, .nat 1] (.struct (SSAVar.tys swapState))
    fun scope =>
      scope.yield [scope.phi (Fin.mk 1 (by decide)), scope.phi (Fin.mk 0 (by decide))]

def swapLoopSyntax : SSAExpr exampleCtx :=
  ssa% {
    x := prim(0 : Nat);
    y := prim(1 : Nat);
    loop (a : Nat := x, b : Nat := y) {
      nextA := b;
      nextB := a;
      yield nextA, nextB
    }
  }

def swapLoopTerm : Term exampleCtx :=
  swapLoopSyntax.toTerm

end Examples

end Zag.Lang.SSA
