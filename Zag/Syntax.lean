import Zag.Data

namespace Zag

declare_syntax_cat zagTy
declare_syntax_cat zagTerm
declare_syntax_cat zagTermAbbrevParam

syntax "ty%" "{" zagTy "}" : term
syntax "term%" "{" zagTerm "}" : term
syntax "zagTerm%" zagTerm : term
syntax "zagName%" ident : term
syntax ident " : " zagTy : zagTermAbbrevParam
syntax "termAbbrev%" ident "[" ident,* "]"
  "(" zagTermAbbrevParam,* ")" " : " zagTy " := " zagTerm : term
syntax "termAbbrev%" ident
  "(" zagTermAbbrevParam,* ")" " : " zagTy " := " zagTerm : term

syntax ident : zagTy
syntax str : zagTy
syntax "var(" term ")" : zagTy
syntax "option(" zagTy ")" : zagTy
syntax "m(" zagTy ")" : zagTy
syntax "union[" zagTy,* "]" : zagTy
syntax "struct[" zagTy,* "]" : zagTy
syntax "func[" zagTy,* "]" "=>" zagTy : zagTy
syntax "abbrev" str "[" zagTy,* "]" : zagTy
syntax "(" zagTy ")" : zagTy

syntax "raw(" term ")" : zagTerm
syntax "term(" term ")" : zagTerm
syntax "prim(" term ":" zagTy ")" : zagTerm
syntax "func(" ident ")" : zagTerm
syntax "func(" str ")" : zagTerm
syntax "var(" term ")" : zagTerm
syntax "call" zagTerm "[" zagTerm,* "]" : zagTerm
syntax "op" str "[" zagTerm,* "]" : zagTerm
syntax "abbrev" str "[" zagTy,* "]" "[" zagTerm,* "]" : zagTerm
syntax "recurse" zagTy "from" zagTerm "{" zagTerm "}" : zagTerm
syntax "mkStruct[" zagTy,* "]" : zagTerm
syntax "struct[" zagTy,* "]" "[" zagTerm,* "]" : zagTerm
syntax "(" zagTerm ")" : zagTerm
syntax ident : zagTerm

private def namedSyntaxIndex? (name : Lean.TSyntax `ident) : List (Lean.TSyntax `ident) → Option Nat
| [] => none
| candidate :: rest =>
    if name.getId == candidate.getId then some 0
    else (namedSyntaxIndex? name rest).map (· + 1)

private partial def lowerTermAbbrevTy (typeParams : List (Lean.TSyntax `ident))
    (stx : Lean.TSyntax `zagTy) : Lean.MacroM (Lean.TSyntax `zagTy) := do
  match stx with
  | `(zagTy| $name:ident) =>
      match namedSyntaxIndex? name typeParams with
      | some idx =>
          let idx : Lean.TSyntax `term := ⟨Lean.Syntax.mkNumLit (toString idx)⟩
          `(zagTy| var($idx))
      | none => pure stx
  | `(zagTy| $_name:str) => pure stx
  | `(zagTy| var($_idx:term)) => pure stx
  | `(zagTy| option($ty:zagTy)) =>
      let ty ← lowerTermAbbrevTy typeParams ty
      `(zagTy| option($ty))
  | `(zagTy| m($ty:zagTy)) =>
      let ty ← lowerTermAbbrevTy typeParams ty
      `(zagTy| m($ty))
  | `(zagTy| union[$tys:zagTy,*]) =>
      let tys ← tys.getElems.mapM (lowerTermAbbrevTy typeParams)
      `(zagTy| union[$[$tys],*])
  | `(zagTy| struct[$tys:zagTy,*]) =>
      let tys ← tys.getElems.mapM (lowerTermAbbrevTy typeParams)
      `(zagTy| struct[$[$tys],*])
  | `(zagTy| func[$args:zagTy,*] => $ret:zagTy) =>
      let args ← args.getElems.mapM (lowerTermAbbrevTy typeParams)
      let ret ← lowerTermAbbrevTy typeParams ret
      `(zagTy| func[$[$args],*] => $ret)
  | `(zagTy| abbrev $name:str [$args:zagTy,*]) =>
      let args ← args.getElems.mapM (lowerTermAbbrevTy typeParams)
      `(zagTy| abbrev $name [$[$args],*])
  | `(zagTy| ($ty:zagTy)) =>
      let ty ← lowerTermAbbrevTy typeParams ty
      `(zagTy| ($ty))
  | _ => Lean.Macro.throwErrorAt stx "unsupported type syntax in termAbbrev%"

private partial def lowerTermAbbrevTerm (typeParams termParams : List (Lean.TSyntax `ident))
    (stx : Lean.TSyntax `zagTerm) : Lean.MacroM (Lean.TSyntax `zagTerm) := do
  match stx with
  | `(zagTerm| $name:ident) =>
      match namedSyntaxIndex? name termParams with
      | some idx =>
          let idx : Lean.TSyntax `term := ⟨Lean.Syntax.mkNumLit (toString idx)⟩
          `(zagTerm| var($idx))
      | none => Lean.Macro.throwErrorAt name "unknown term parameter"
  | `(zagTerm| raw($_term:term)) => pure stx
  | `(zagTerm| term($_term:term)) => pure stx
  | `(zagTerm| prim($value:term : $ty:zagTy)) =>
      let ty ← lowerTermAbbrevTy typeParams ty
      `(zagTerm| prim($value : $ty))
  | `(zagTerm| func($_name:ident)) => pure stx
  | `(zagTerm| func($_name:str)) => pure stx
  | `(zagTerm| var($_idx:term)) => pure stx
  | `(zagTerm| call $fn:zagTerm [$args:zagTerm,*]) =>
      let fn ← lowerTermAbbrevTerm typeParams termParams fn
      let args ← args.getElems.mapM (lowerTermAbbrevTerm typeParams termParams)
      `(zagTerm| call $fn [$[$args],*])
  | `(zagTerm| op $name:str [$args:zagTerm,*]) =>
      let args ← args.getElems.mapM (lowerTermAbbrevTerm typeParams termParams)
      `(zagTerm| op $name [$[$args],*])
  | `(zagTerm| abbrev $name:str [$typeArgs:zagTy,*] [$args:zagTerm,*]) =>
      let typeArgs ← typeArgs.getElems.mapM (lowerTermAbbrevTy typeParams)
      let args ← args.getElems.mapM (lowerTermAbbrevTerm typeParams termParams)
      `(zagTerm| abbrev $name [$[$typeArgs],*] [$[$args],*])
  | `(zagTerm| recurse $resultTy:zagTy from $init:zagTerm { $body:zagTerm }) =>
      let resultTy ← lowerTermAbbrevTy typeParams resultTy
      let init ← lowerTermAbbrevTerm typeParams termParams init
      let body ← lowerTermAbbrevTerm typeParams termParams body
      `(zagTerm| recurse $resultTy from $init { $body })
  | `(zagTerm| mkStruct[$tys:zagTy,*]) =>
      let tys ← tys.getElems.mapM (lowerTermAbbrevTy typeParams)
      `(zagTerm| mkStruct[$[$tys],*])
  | `(zagTerm| struct[$tys:zagTy,*] [$fields:zagTerm,*]) =>
      let tys ← tys.getElems.mapM (lowerTermAbbrevTy typeParams)
      let fields ← fields.getElems.mapM (lowerTermAbbrevTerm typeParams termParams)
      `(zagTerm| struct[$[$tys],*] [$[$fields],*])
  | `(zagTerm| ($term:zagTerm)) =>
      let term ← lowerTermAbbrevTerm typeParams termParams term
      `(zagTerm| ($term))
  | _ => Lean.Macro.throwErrorAt stx "unsupported term syntax in termAbbrev%"

macro_rules
  | `(zagName% $name:ident) =>
      pure (Lean.Syntax.mkStrLit name.getId.toString)
  | `(ty% { $name:ident }) => `((Zag.Ty.prim (zagName% $name) : Zag.Ty))
  | `(ty% { $name:str }) => `((Zag.Ty.prim $name : Zag.Ty))
  | `(ty% { var($idx:term) }) => `((Zag.Ty.var (($idx : Nat)) : Zag.Ty))
  | `(ty% { option($ty:zagTy) }) => `((Zag.Ty.option (ty% { $ty }) : Zag.Ty))
  | `(ty% { m($ty:zagTy) }) => `((Zag.Ty.m (ty% { $ty }) : Zag.Ty))
  | `(ty% { union[$tys:zagTy,*] }) => `((Zag.Ty.union [ $[(ty% { $tys })],* ] : Zag.Ty))
  | `(ty% { struct[$tys:zagTy,*] }) => `((Zag.Ty.struct [ $[(ty% { $tys })],* ] : Zag.Ty))
  | `(ty% { func[$args:zagTy,*] => $ret:zagTy }) =>
      `((Zag.Ty.func [ $[(ty% { $args })],* ] (ty% { $ret }) : Zag.Ty))
  | `(ty% { abbrev $name:str [$args:zagTy,*] }) =>
      `((Zag.Ty.«abbrev» $name [ $[(ty% { $args })],* ] : Zag.Ty))
  | `(ty% { ($ty:zagTy) }) => `(ty% { $ty })
  | `(term% { $body:zagTerm }) => `(zagTerm% $body)
  | `(zagTerm% raw($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% term($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% prim($value:term : $ty:zagTy)) =>
      `(Zag.Term.prim (ty% { $ty }) (($value : Zag.Ty.type _ (ty% { $ty }))))
  | `(zagTerm% func($name:ident)) => `(Zag.Term.primFunc (zagName% $name))
  | `(zagTerm% func($name:str)) => `(Zag.Term.primFunc $name)
  | `(zagTerm% var($idx:term)) => `(Zag.Term.var (($idx : Nat)))
  | `(zagTerm% call $fn:zagTerm [ $args:zagTerm,* ]) =>
      `(Zag.Term.app (zagTerm% $fn) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% op $name:str [ $args:zagTerm,* ]) =>
      `(Zag.Term.op $name [ $[(zagTerm% $args)],* ])
  | `(zagTerm% abbrev $name:str [ $typeArgs:zagTy,* ] [ $args:zagTerm,* ]) =>
      `(Zag.Term.abbrev $name [ $[(ty% { $typeArgs })],* ] [ $[(zagTerm% $args)],* ])
  | `(zagTerm% recurse $resultTy:zagTy from $init:zagTerm { $body:zagTerm }) =>
      `(Zag.Term.recurse (ty% { $resultTy }) (zagTerm% $init) (zagTerm% $body))
  | `(zagTerm% mkStruct[$tys:zagTy,*]) =>
      `(Zag.Term.mkStruct [ $[(ty% { $tys })],* ])
  | `(zagTerm% struct[$tys:zagTy,*] [ $fields:zagTerm,* ]) =>
      `(Zag.Term.app (Zag.Term.mkStruct [ $[(ty% { $tys })],* ]) [ $[(zagTerm% $fields)],* ])
  | `(zagTerm% ($term:zagTerm)) => `(zagTerm% $term)

private def expandTermAbbrev (name : Lean.TSyntax `ident)
    (typeParams termParams : List (Lean.TSyntax `ident))
    (paramTys : List (Lean.TSyntax `zagTy)) (outTy : Lean.TSyntax `zagTy)
    (body : Lean.TSyntax `zagTerm) : Lean.MacroM Lean.Syntax := do
  let varCtx ← paramTys.toArray.mapM fun paramTy => do
    let paramTy ← lowerTermAbbrevTy typeParams paramTy
    `(term| ty% { $paramTy })
  let outTy ← lowerTermAbbrevTy typeParams outTy
  let body ← lowerTermAbbrevTerm typeParams termParams body
  let typeArity : Lean.TSyntax `term := ⟨Lean.Syntax.mkNumLit (toString typeParams.length)⟩
  `((zagName% $name, ({
      typeArity := $typeArity
      varCtx := [$[$varCtx],*]
      outTy := ty% { $outTy }
      body := term% { $body }
    } : Zag.TermAbbrev _)))

private def expandTermAbbrevParams (name : Lean.TSyntax `ident)
    (typeParams : List (Lean.TSyntax `ident))
    (params : List (Lean.TSyntax `zagTermAbbrevParam)) (outTy : Lean.TSyntax `zagTy)
    (body : Lean.TSyntax `zagTerm) : Lean.MacroM Lean.Syntax := do
  let pairs ← params.mapM fun param =>
    match param.raw with
    | `(zagTermAbbrevParam| $paramName:ident : $paramTy:zagTy) => pure (paramName, paramTy)
    | _ => Lean.Macro.throwErrorAt param.raw "invalid term parameter"
  expandTermAbbrev name typeParams (pairs.map (·.1)) (pairs.map (·.2)) outTy body

macro_rules
  | `(termAbbrev% $name:ident [$typeParams:ident,*]
        ($params:zagTermAbbrevParam,*) : $outTy:zagTy := $body:zagTerm) =>
      expandTermAbbrevParams name typeParams.getElems.toList params.getElems.toList outTy body
  | `(termAbbrev% $name:ident
        ($params:zagTermAbbrevParam,*) : $outTy:zagTy := $body:zagTerm) =>
      expandTermAbbrevParams name [] params.getElems.toList outTy body

end Zag
