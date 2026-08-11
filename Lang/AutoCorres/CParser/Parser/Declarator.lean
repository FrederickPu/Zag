import Lang.AutoCorres.CParser.Parser.Expression

/-!
# StrictC declarator parser

Declarators are implemented with expressions in `Expression` because array
bounds, parameter declarations, type names, casts, and compound literals form
one mutually recursive parser component. This module is its declarator-facing
import boundary.
-/
