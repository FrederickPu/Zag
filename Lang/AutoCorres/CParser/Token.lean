import Lang.AutoCorres.CParser.Source

/-!
# StrictC tokens

This is the terminal vocabulary from pinned `StrictC.grm`, retaining literal
and identifier payloads directly in the token kind.
-/

namespace Zag.Lang.AutoCorres.CParser

inductive Radix where
  | binary
  | octal
  | decimal
  | hexadecimal
deriving Repr, DecidableEq, Inhabited

structure NumericLiteral where
  value : Nat
  radix : Radix
  suffix : String
deriving Repr, DecidableEq, Inhabited

inductive TokenKind where
  | eof
  | star | slash | mod
  | lparen | rparen | lcurly | rcurly | lbracket | rbracket
  | comma | semicolon | colon | question
  | assign | dot | plus | minus | and | not | ampersand | bitNot
  | plusPlus | minusMinus
  | plusEq | minusEq | bitAndEq | bitOrEq | mulEq
  | divEq | modEq | bitXorEq | leftShiftEq | rightShiftEq
  | enum
  | «if» | «else» | «while» | «do» | «return» | «break» | «continue» | «for»
  | «switch» | «case» | «default» | sizeof
  | logicalOr | logicalAnd | bitwiseOr | bitwiseXor
  | equals | notEquals
  | lessEq | greaterEq | less | greater | leftShift | rightShift
  | int | bool | char | long | short | signed | unsigned | void
  | arrow
  | ident (name : String) | typeIdent (name : String)
  | numeric (literal : NumericLiteral)
  | struct | union | typedef | extern | const | volatile | restrict
  | invariant | inline | static | noReturn | threadLocal | auto
  | fnSpec | relSpec | auxUpd | ghostUpd | modifies | calls | ownedBy
  | specBegin | specEnd | dontTranslate
  | stringLiteral (value : String)
  | specBlockEnd | gccAttribute | asm | register
deriving Repr, DecidableEq, Inhabited

abbrev Token := Located TokenKind

end Zag.Lang.AutoCorres.CParser
