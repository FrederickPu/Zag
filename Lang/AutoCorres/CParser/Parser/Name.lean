/-!
# StrictC parser names

The spelling operations in this file are the pure counterparts of the pinned
`NameGeneration.ML` operations used directly by `StrictC.grm`.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

def underscoreSafePrefix : String := "StrictC'"

def mkIdentUScoreSafe (name : String) : String :=
  if name.startsWith "_" then underscoreSafePrefix ++ name else name

def rmUScoreSafety (name : String) : String :=
  if name.startsWith underscoreSafePrefix then (name.drop underscoreSafePrefix.length).toString else name

def cStructName (name : String) : String := name ++ "_C"

def unCStructName (name : String) : String :=
  if name.endsWith "_C" then (name.dropEnd 2).toString else name

def cFieldName (name : String) : String := name ++ "_C"

def unCFieldName (name : String) : String :=
  if name.endsWith "_C" then (name.dropEnd 2).toString else name

def ensureCStructName (name : String) : String := cStructName (unCStructName name)

def ensureCFieldName (name : String) : String := cFieldName (unCFieldName name)

def internalAnonStructPrefix : String := "ISA_anon_struct|"

def anonymousStructName (index : Nat) : String := internalAnonStructPrefix ++ toString index

def phantomStateName : String := "phantom_machine_state"

def normalizeGccAttributeName (name : String) : String :=
  if name.length > 4 && name.startsWith "__" && name.endsWith "__" then
    ((name.drop 2).dropEnd 2).toString
  else
    name

end Zag.Lang.AutoCorres.CParser.Parser
