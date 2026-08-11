import Lang.AutoCorres.CParser.Lexer

/-!
# StrictC lexer regression tests

These tests exercise the pure token stream and diagnostics returned by the
lexer. They intentionally avoid going through the C parser.
-/

namespace Zag.Test.AutoCorres.CParser.Lexer

open Zag.Lang.AutoCorres.CParser

set_option warningAsError true

private def armLex (source : String) : Zag.Lang.AutoCorres.CParser.Lexer.Result :=
  Zag.Lang.AutoCorres.CParser.Lexer.lex .arm "input.c" source

private def kinds (result : Zag.Lang.AutoCorres.CParser.Lexer.Result) : Array TokenKind :=
  result.tokens.map (·.value)

private def messages (result : Zag.Lang.AutoCorres.CParser.Lexer.Result) : Array String :=
  result.diagnostics.map (·.message)

private def number (value : Nat) (radix : Radix := .decimal)
    (suffix : String := "") : TokenKind :=
  .numeric { value, radix, suffix }

/-! Every punctuator is recognized with longest-match precedence. -/

#guard kinds (armLex
    ">>= <<= ++ -- += -= *= |= &= /= %= ^= && || == != -> << >> <= >= * / % ( ) { } [ ] , ; : ? = . + - ! & ~ | ^ < >") =
  #[.rightShiftEq, .leftShiftEq, .plusPlus, .minusMinus, .plusEq, .minusEq,
    .mulEq, .bitOrEq, .bitAndEq, .divEq, .modEq, .bitXorEq, .logicalAnd,
    .logicalOr, .equals, .notEquals, .arrow, .leftShift, .rightShift,
    .lessEq, .greaterEq, .star, .slash, .mod, .lparen, .rparen, .lcurly,
    .rcurly, .lbracket, .rbracket, .comma, .semicolon, .colon, .question,
    .assign, .dot, .plus, .minus, .not, .ampersand, .bitNot, .bitwiseOr,
    .bitwiseXor, .less, .greater, .eof]

#guard kinds (armLex ">>=>>= <<=<<=") =
  #[.rightShiftEq, .rightShiftEq, .leftShiftEq, .leftShiftEq, .eof]
#guard (armLex ">>=>>= <<=<<=").diagnostics.isEmpty

/-! Typedef, tag, tag-body, and lexical scope transitions. -/

#guard kinds (armLex "typedef int T; T value;") =
  #[.typedef, .int, .ident "T", .semicolon, .typeIdent "T", .ident "value",
    .semicolon, .eof]

#guard kinds (armLex
    "typedef struct Tag { int field; struct Nested { int nested; }; } Alias; Alias value;") =
  #[.typedef, .struct, .ident "Tag", .lcurly, .int, .ident "field", .semicolon,
    .struct, .ident "Nested", .lcurly, .int, .ident "nested", .semicolon,
    .rcurly, .semicolon, .rcurly, .ident "Alias", .semicolon,
    .typeIdent "Alias", .ident "value", .semicolon, .eof]

#guard (armLex
    "typedef struct Tag { int field; struct Nested { int nested; }; } Alias;").diagnostics.isEmpty

#guard kinds (armLex
    "typedef int Outer; { typedef int Inner, Inner2; Outer a; Inner b; Inner2 c; } Outer d; Inner e;") =
  #[.typedef, .int, .ident "Outer", .semicolon, .lcurly, .typedef, .int,
    .ident "Inner", .comma, .ident "Inner2", .semicolon, .typeIdent "Outer",
    .ident "a", .semicolon, .typeIdent "Inner", .ident "b", .semicolon,
    .typeIdent "Inner2", .ident "c", .semicolon, .rcurly, .typeIdent "Outer",
    .ident "d", .semicolon, .ident "Inner", .ident "e", .semicolon, .eof]

/-! Leading underscores are escaped without disturbing identifier tails. -/

#guard kinds (armLex "_plain plain_under _a1 __tail _Bool") =
  #[.ident "StrictC'_plain", .ident "plain_under", .ident "StrictC'_a1",
    .ident "StrictC'__tail", .bool, .eof]

#guard kinds (armLex "typedef int _word; _word _value;") =
  #[.typedef, .int, .ident "StrictC'_word", .semicolon,
    .typeIdent "StrictC'_word", .ident "StrictC'_value", .semicolon, .eof]

/-! Integer radix, suffix, and unmatched residue behavior. -/

#guard kinds (armLex "0 077 0b101u 0x2a 42u 17LL 0XfULL 12ultra") =
  #[number 0, number 63 .octal, number 5 .binary "u", number 42 .hexadecimal,
    number 42 .decimal "u", number 17 .decimal "LL", number 15 .hexadecimal "ULL",
    number 12 .decimal "ul", .ident "tra", .eof]

#guard (armLex "0 077 0b101u 0x2a 42u 17LL 0XfULL 12ultra").diagnostics.isEmpty

#guard kinds (armLex "09 078u 0b102UL 0x 0xg") =
  #[number 0 .octal, number 7 .octal "u", number 2 .binary "UL",
    number 0 .hexadecimal, number 0 .hexadecimal, .ident "g", .eof]

#guard messages (armLex "09 078u 0b102UL 0x 0xg") =
  #["Invalid digit in octal integer literal",
    "Invalid digit in octal integer literal",
    "Invalid digit in binary integer literal",
    "Missing digits in hexadecimal integer literal",
    "Missing digits in hexadecimal integer literal"]

/-! Ordinary strings retain their source spelling rather than decoding escapes. -/

#guard kinds (armLex r#""line\nslash\\quote\"end""#) =
  #[.stringLiteral r#"line\nslash\\quote\"end"#, .eof]

/-! Character literals cover ordinary, escaped, octal, hexadecimal, and bad forms. -/

#guard kinds (armLex r#"'a' '\101' '\x41' '\n' '\'' '\\'"#) =
  #[number 97, number 65, number 65, number 10, number 39, number 92, .eof]

#guard (armLex r#"'a' '\101' '\x41' '\n' '\'' '\\'"#).diagnostics.isEmpty

#guard kinds (armLex "'' 'ab'") = #[number 0, number 0, .eof]

#guard messages (armLex "'' 'ab'") =
  #["Malformed character literal", "Malformed character literal"]

#guard kinds (armLex r#"'\q'"#) = #[number 0, number 113, .eof]

#guard messages (armLex r#"'\q'"#) = #["Malformed character literal"]

/-! ARM uses an unsigned eight-bit plain character model. -/

#guard kinds (armLex r#"'\xff'"#) = #[number 255, .eof]

#guard (armLex r#"'\xff'"#).diagnostics.isEmpty

#guard kinds (armLex r#"'\400'"#) = #[number 0, .eof]

#guard messages (armLex r#"'\400'"#) =
  #["Character literal component too large!",
    "character literal component is outside the target unsigned-char range"]

/-! Documentation comments are ignored unless they begin with an annotation marker. -/

#guard kinds (armLex "/** ordinary API documentation */ int documented;") =
  #[.int, .ident "documented", .semicolon, .eof]

#guard (armLex "/** ordinary API documentation */ int documented;").diagnostics.isEmpty

/-! Every marker accepted by the pinned AutoCorres annotation lexer. -/

private def annotationSource : String :=
  "/** INVARIANT: */ /** INV: */ /** FNSPEC */ /** RELSPEC */ /** MODIFIES: */ " ++
  "/** AUXUPD: */ /** GHOSTUPD: */ /** END-SPEC: */ /** SPEC: */ " ++
  "/** DONT_TRANSLATE */ /** CALLS */ /** OWNED_BY */"

#guard kinds (armLex annotationSource) =
  #[.invariant, .specBlockEnd, .invariant, .specBlockEnd,
    .fnSpec, .specBlockEnd, .relSpec, .specBlockEnd,
    .modifies, .specBlockEnd, .auxUpd, .specBlockEnd,
    .ghostUpd, .specBlockEnd, .specEnd, .specBlockEnd,
    .specBegin, .specBlockEnd, .dontTranslate, .specBlockEnd,
    .calls, .specBlockEnd, .ownedBy, .specBlockEnd, .eof]

#guard (armLex annotationSource).diagnostics.isEmpty

#guard kinds (armLex r#"/** FNSPEC function' _argument' "quoted\"value" */"#) =
  #[.fnSpec, .ident "function'", .ident "StrictC'_argument'",
    .stringLiteral "quoted\"value", .specBlockEnd, .eof]

/-! Both line-directive spellings reset logical files, lines, and columns. -/

private def lineResult := armLex "#line 41 \"virt.c\"\nint x;\n"

#guard lineResult.tokens[0]!.value = .int
#guard lineResult.tokens[0]!.region.left =
  { file := "virt.c", line := 41, column := 0, offset := 18 }
#guard lineResult.tokens[0]!.region.right =
  { file := "virt.c", line := 41, column := 2, offset := 20 }
#guard lineResult.tokens[1]!.region.left =
  { file := "virt.c", line := 41, column := 4, offset := 22 }
#guard lineResult.tokens[3]!.region.left =
  { file := "virt.c", line := 42, column := 0, offset := 25 }
#guard lineResult.diagnostics.isEmpty

private def gnuLineResult := armLex "# 7 \"gnu.c\" 1 3\n_x"

#guard gnuLineResult.tokens[0]!.value = .ident "StrictC'_x"
#guard gnuLineResult.tokens[0]!.region.left =
  { file := "gnu.c", line := 7, column := 0, offset := 16 }
#guard gnuLineResult.tokens[0]!.region.right =
  { file := "gnu.c", line := 7, column := 1, offset := 17 }
#guard gnuLineResult.diagnostics.isEmpty

/-! Unterminated ordinary comments stop at EOF and report their source region. -/

private def unclosedComment := armLex "/* never closed"

#guard kinds unclosedComment = #[.eof]
#guard messages unclosedComment = #["unclosed comment"]
#guard unclosedComment.diagnostics[0]!.severity = .error
#guard unclosedComment.diagnostics[0]!.region.left =
  { file := "input.c", line := 1, column := 0, offset := 0 }

end Zag.Test.AutoCorres.CParser.Lexer
