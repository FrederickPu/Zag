import Lang.AutoCorres.CParser.Parser.AstActions

namespace Zag.Test.AutoCorres.CParser.ParserActions

open Zag.Lang.AutoCorres.CParser
open Zag.Lang.AutoCorres.CParser.Parser
open Zag.Lang.AutoCorres.CParser.Parser.AstActions

set_option warningAsError true

private def statement (node : StatementNode) : Statement :=
  .stmt { value := node, region := .bogus }

private def nestedBreak : Statement :=
  statement (.block [.statement (statement (.block [.statement (statement .break)]))])

private def cases : List RawSwitchCase :=
  [({ value := [{ value := some (AstActions.exprInt 0), region := .bogus }], region := .bogus },
      [.statement nestedBreak]),
   ({ value := [{ value := none, region := .bogus }], region := .bogus },
      [.statement (statement (.returnStmt none))])]

private def cleaned := cleanSwitchCases cases .bogus

#guard cleaned.diagnostics.isEmpty
#guard cleaned.value.length = 2
#guard match cleaned.value with
  | (_, [BlockItem.statement (.stmt {
      value := .block [BlockItem.statement (.stmt { value := .block [], .. })], .. })]) :: _ => true
  | _ => false

end Zag.Test.AutoCorres.CParser.ParserActions
