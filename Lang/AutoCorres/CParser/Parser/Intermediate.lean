import Lang.AutoCorres.CParser.Ast
import Lang.AutoCorres.CParser.Parser.Core

/-!
# StrictC parser intermediates

These datatypes replace the ML grammar's semantic stack values. Declarator
layers are syntax, not Lean functions, so parser states remain inspectable.
-/

namespace Zag.Lang.AutoCorres.CParser.Parser

def locatedMap (function : α → β) (value : Located α) : Located β :=
  { value := function value.value, region := value.region }

inductive StorageClassSpecifier where
  | typeDef
  | extern
  | static
  | auto
  | register
  | threadLocal
deriving Repr, DecidableEq, Inhabited

inductive TypeQualifier where
  | const
  | volatile
  | restrict
deriving Repr, DecidableEq, Inhabited

inductive TypeSpecToken where
  | unsigned
  | signed
  | bool
  | char
  | int
  | long
  | longLong
  | short
  | void
deriving Repr, DecidableEq, Inhabited

abbrev Parameter := Located (CType Expr × Option (Located String))
abbrev StructField := CType Expr × Located String

structure StructIdDecl where
  name : Located String
  fields : List StructField
deriving Repr, Inhabited

structure StructSpecifier where
  type : Located (CType Expr)
  declarations : List (Located StructIdDecl)
deriving Repr, Inhabited

structure EnumSpecifier where
  name : Located (Option String)
  enumerators : List (Located String × Option Expr)
  region : Region
deriving Repr, Inhabited

inductive TypeSpecifier where
  | token (value : Located TypeSpecToken)
  | struct (value : StructSpecifier)
  | enum (value : EnumSpecifier)
  | typeId (name : Located String)
deriving Repr, Inhabited

def TypeSpecifier.region : TypeSpecifier → Region
  | .token value => value.region
  | .struct value => value.type.region
  | .enum value => value.region
  | .typeId name => name.region

inductive DeclSpecifier where
  | storage (value : Located StorageClassSpecifier)
  | typeQualifier (value : Located TypeQualifier)
  | typeSpecifier (value : TypeSpecifier)
  | functionSpecifier (value : Located FunctionSpec)
deriving Repr, Inhabited

def DeclSpecifier.region : DeclSpecifier → Region
  | .storage value => value.region
  | .typeQualifier value => value.region
  | .typeSpecifier value => value.region
  | .functionSpecifier value => value.region

abbrev DeclSpecifierList := Located (List DeclSpecifier)

inductive TypeLayer where
  | identity
  | pointer
  | array (size : Option Expr)
  | function (parameterTypes : List (CType Expr))
  | compose (outer inner : TypeLayer)
deriving Repr, Inhabited

namespace TypeLayer

def apply : TypeLayer → CType Expr → CType Expr
  | .identity, type => type
  | .pointer, type => .ptr type
  | .array size, type => .array type size
  | .function parameters, type => .function type parameters
  | .compose outer inner, type => outer.apply (inner.apply type)

def thenOuter (inner outer : TypeLayer) : TypeLayer :=
  match inner, outer with
  | .identity, outer => outer
  | inner, .identity => inner
  | inner, outer => .compose inner outer

end TypeLayer

structure AbstractDeclarator where
  layer : TypeLayer
  region : Region
deriving Repr, Inhabited

namespace AbstractDeclarator

def identity (region : Region) : AbstractDeclarator := { layer := .identity, region }

def pointer (region : Region) : AbstractDeclarator := { layer := .pointer, region }

def array (region : Region) (size : Option Expr) : AbstractDeclarator :=
  { layer := .array size, region }

def function (region : Region) (parameterTypes : List (CType Expr)) : AbstractDeclarator :=
  { layer := .function parameterTypes, region }

-- Pinned `ooa(a, b)` is `a ∘ b`: `b` is applied to the base first.
def compose (outer inner : AbstractDeclarator) : AbstractDeclarator :=
  { layer := outer.layer.thenOuter inner.layer
    region := outer.region.append inner.region }

def apply (declarator : AbstractDeclarator) (base : CType Expr) : CType Expr :=
  declarator.layer.apply base

end AbstractDeclarator

structure Declarator where
  name : Located String
  abstract : AbstractDeclarator
  parameters : Option (List Parameter) := none
  attributes : List GccAttribute := []
deriving Repr, Inhabited

namespace Declarator

def region (declarator : Declarator) : Region :=
  declarator.name.region.append declarator.abstract.region

def direct (name : Located String) : Declarator :=
  { name, abstract := .identity name.region }

-- Pinned `ood(d, a)` composes the existing direct layer outside `a`.
def compose (declarator : Declarator) (inner : AbstractDeclarator) : Declarator :=
  { declarator with abstract := declarator.abstract.compose inner }

def addAttributes (declarator : Declarator) (attributes : List GccAttribute) : Declarator :=
  { declarator with attributes := attributes ++ declarator.attributes }

def addParameters (declarator : Declarator) (parameters : List Parameter) : Declarator :=
  match declarator.parameters with
  | some _ => declarator
  | none => { declarator with parameters := some parameters }

def apply (declarator : Declarator) (base : CType Expr) : CType Expr :=
  declarator.abstract.apply base

end Declarator

structure InitDeclarator where
  declarator : Located Declarator
  initializer : Option Initializer
deriving Repr, Inhabited

structure StructDeclarator where
  declarator : Located Declarator
  bitWidth : Option Expr
deriving Repr, Inhabited

def storageClass? : StorageClassSpecifier → Option StorageClass
  | .typeDef => none
  | .extern => some .extern
  | .static => some .static
  | .auto => some .auto
  | .register => some .register
  | .threadLocal => some .threadLocal

end Zag.Lang.AutoCorres.CParser.Parser
