import Zag.Data

/-!
Surface syntax for Zag types, terms, and blocks.

A block is written like a small SSA routine: named parameters, a sequence of `name := term;`
instructions, and a returned term. Blocks are declared explicitly and refer to one another by
name, so a program is just a list of blocks.

```
block% sumTo(n : Nat) : Nat {
  done := op "eq"[n, raw(Term.nat 0)];
  ret op "ite"[done, raw(Term.nat 0), op "add"[call "sumTo"[op "sub"[n, raw(Term.nat 1)]], n]]
}
```

The loop form is sugar for an ordinary operator term. Its listed blocks become first-class block
operands followed by the parenthesised initial values.

```
block% countDown(start : Nat) : Nat {
  final := while [countDownCond, countDownBody] (start);
  ret final
}
```
-/

namespace Zag

declare_syntax_cat zagTy
declare_syntax_cat zagTerm
declare_syntax_cat zagParam
declare_syntax_cat zagBlockRef
declare_syntax_cat zagInstr
declare_syntax_cat zagBlock

syntax "ty%" "{" zagTy "}" : term
syntax "term%" "{" zagTerm "}" : term
syntax "zagTerm%" zagTerm : term
syntax "zagName%" ident : term
syntax "params%" "(" zagParam,* ")" : term
syntax "zagBlockRef%" zagBlockRef : term
syntax "instrs%" "{" zagInstr* "}" : term
syntax "block%" zagBlock : term
syntax "blocks%" "[" zagBlock,* "]" : term
syntax "blockCtx%" "[" zagBlock,* "]" : term

/-! ### types -/

syntax ident : zagTy
syntax str : zagTy
syntax "var(" ident ")" : zagTy
syntax ident "[" zagTy,* "]" : zagTy
syntax str "[" zagTy,* "]" : zagTy
syntax "func[" zagTy,* "]" "=>" zagTy : zagTy
syntax "(" zagTy ")" : zagTy
syntax "(" term ")" : zagTy

/-! ### terms -/

syntax "raw(" term ")" : zagTerm
syntax "term(" term ")" : zagTerm
syntax "prim(" term ":" zagTy ")" : zagTerm
syntax "var(" ident ")" : zagTerm
syntax "var(" term ")" : zagTerm
syntax "apply" zagTerm "[" zagTerm,* "]" : zagTerm
syntax "op" str "[" zagTerm,* "]" : zagTerm
syntax "op" ident "[" zagTerm,* "]" : zagTerm
syntax "call" str "[" zagTerm,* "]" : zagTerm
syntax "call" ident "[" zagTerm,* "]" : zagTerm
syntax "exit" str zagTerm : zagTerm
syntax "exit" ident zagTerm : zagTerm
syntax "(" zagTerm ")" : zagTerm
syntax ident : zagTerm

/-! ### blocks -/

syntax ident " : " zagTy : zagParam

/-- A block supplied as a first-class value to an operator. -/
syntax ident : zagBlockRef
syntax str : zagBlockRef

syntax ident " := " zagTerm ";" : zagInstr
/-- Operator sugar: `final := while [cond, body] (start);`. The operator is named by
  `rawIdent` rather than `ident` so that `while`, `for` and `switch` -- all Lean keywords -- can
  be written bare; nothing here knows which operators exist, so a new entry in `OpCtx` needs
  no parser change. -/
syntax ident " := " rawIdent "[" zagBlockRef,* "]" "(" zagTerm,* ")" ";" : zagInstr
syntax ident "(" zagParam,* ")" " : " zagTy "{" zagInstr* "ret" zagTerm "}" : zagBlock

macro_rules
  | `(zagName% $name:ident) =>
      pure (Lean.Syntax.mkStrLit name.getId.toString)
  | `(ty% { $name:ident }) => `((Zag.Ty.prim (zagName% $name) [] : Zag.Ty))
  | `(ty% { $name:str }) => `((Zag.Ty.prim $name [] : Zag.Ty))
  | `(ty% { var($name:ident) }) => `((Zag.Ty.var (zagName% $name) : Zag.Ty))
  | `(ty% { $name:ident [$args:zagTy,*] }) =>
      `((Zag.Ty.prim (zagName% $name) [ $[(ty% { $args })],* ] : Zag.Ty))
  | `(ty% { $name:str [$args:zagTy,*] }) =>
      `((Zag.Ty.prim $name [ $[(ty% { $args })],* ] : Zag.Ty))
  | `(ty% { func[$args:zagTy,*] => $out:zagTy }) =>
      `((Zag.Ty.func [ $[(ty% { $args })],* ] (ty% { $out }) : Zag.Ty))
  | `(ty% { ($ty:zagTy) }) => `(ty% { $ty })
  | `(ty% { ($ty:term) }) => `(($ty : Zag.Ty))
  | `(term% { $body:zagTerm }) => `(zagTerm% $body)
  | `(zagTerm% raw($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% term($term:term)) => `(($term : Zag.Term _))
  | `(zagTerm% prim($value:term : $ty:zagTy)) =>
      `(Zag.Term.prim (ty% { $ty }) (($value : Zag.Ty.type _ (ty% { $ty }))))
  | `(zagTerm% var($name:ident)) => `(Zag.Term.var (zagName% $name))
  | `(zagTerm% var($name:term)) => `(Zag.Term.var (($name : String)))
  | `(zagTerm% apply $fn:zagTerm [ $args:zagTerm,* ]) =>
      `(Zag.Term.app (zagTerm% $fn) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% op $name:str [ $args:zagTerm,* ]) =>
      `(Zag.Term.op $name [ $[(zagTerm% $args)],* ])
  | `(zagTerm% op $name:ident [ $args:zagTerm,* ]) =>
      `(Zag.Term.op (zagName% $name) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% call $name:str [ $args:zagTerm,* ]) =>
      `(Zag.Term.call $name [ $[(zagTerm% $args)],* ])
  | `(zagTerm% call $name:ident [ $args:zagTerm,* ]) =>
      `(Zag.Term.call (zagName% $name) [ $[(zagTerm% $args)],* ])
  | `(zagTerm% exit $name:str $value:zagTerm) =>
      `(Zag.Term.exit $name (zagTerm% $value))
  | `(zagTerm% exit $name:ident $value:zagTerm) =>
      `(Zag.Term.exit (zagName% $name) (zagTerm% $value))
  | `(zagTerm% ($term:zagTerm)) => `(zagTerm% $term)
  | `(zagTerm% $name:ident) => `(Zag.Term.var (zagName% $name))

macro_rules
  | `(params% ( $params:zagParam,* )) => do
      let entries ← params.getElems.mapM fun param =>
        match param with
        | `(zagParam| $name:ident : $ty:zagTy) =>
            `(term| ((zagName% $name), ty% { $ty }))
        | _ => Lean.Macro.throwErrorAt param "invalid block parameter"
      `(([ $[$entries],* ] : Zag.VarCtx))
  | `(zagBlockRef% $name:ident) => `(zagName% $name)
  | `(zagBlockRef% $name:str) => `(($name : String))
  | `(instrs% { $instrs:zagInstr* }) => do
      let entries ← instrs.mapM fun instr =>
        match instr with
        | `(zagInstr| $name:ident := $value:zagTerm ;) =>
            `(term| (Zag.Instr.ofTerm (zagName% $name) (term% { $value }) : Zag.Instr _))
        | `(zagInstr| $name:ident := $control [ $blocks:zagBlockRef,* ] ( $args:zagTerm,* ) ;) =>
            `(term| (Zag.Instr.ofTerm (zagName% $name)
                (Zag.Term.op (zagName% $control)
                  ([ $[(Zag.Term.var (zagBlockRef% $blocks))],* ] ++
                   [ $[(term% { $args })],* ])) : Zag.Instr _))
        | _ => Lean.Macro.throwErrorAt instr "invalid instruction"
      `([ $[$entries],* ])
  | `(block% $name:ident ( $params:zagParam,* ) : $outTy:zagTy
        { $instrs:zagInstr* ret $result:zagTerm }) =>
      `(((zagName% $name), ({
          params := params% ( $params,* )
          instrs := instrs% { $instrs* }
          outTy := ty% { $outTy }
          result := term% { $result }
        } : Zag.Block _)))
  | `(blocks% [ $blocks:zagBlock,* ]) =>
      `([ $[(block% $blocks)],* ])
  | `(blockCtx% [ $blocks:zagBlock,* ]) =>
      `((⟨blocks% [ $blocks,* ], by decide⟩ : Zag.BlockCtx _))

end Zag
