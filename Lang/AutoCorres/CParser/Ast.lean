import Lang.AutoCorres.CParser.CType
import Lang.AutoCorres.CParser.Token

/-!
# StrictC abstract syntax

Pure counterparts of the datatypes in `Absyn-CType.ML`, `Absyn-Expr.ML`, and
`Absyn-StmtDecl.ML` from pinned l4v commit
`bc2599a59c43e673dca021b10b9841e9b8da4430`.
-/

namespace Zag.Lang.AutoCorres.CParser

structure NumLiteralInfo where
  value : Int
  suffix : String
  base : Radix
deriving Repr, DecidableEq, Inhabited

inductive LiteralConstantNode where
  | numConst (info : NumLiteralInfo)
  | stringLit (value : String)
deriving Repr, DecidableEq, Inhabited

abbrev LiteralConstant := Located LiteralConstantNode

inductive BinOpType where
  | logOr
  | logAnd
  | equals
  | notEquals
  | bitwiseAnd
  | bitwiseOr
  | bitwiseXor
  | lt
  | gt
  | leq
  | geq
  | plus
  | minus
  | times
  | divides
  | modulus
  | rShift
  | lShift
deriving Repr, DecidableEq, Inhabited

inductive UnOpType where
  | negate
  | not
  | addr
  | bitNegate
deriving Repr, DecidableEq, Inhabited

inductive MoreInfo where
  | mungedVar (munge : String) (ownedBy : Option String)
  | enumC
  | functionName
deriving Repr, DecidableEq, Inhabited

-- The ML parser mutates a reference containing this payload during analysis.
-- The pure syntax stores the current payload directly.
abbrev VarInfo := Option (AnalyzedCType × MoreInfo)

mutual
  inductive ExprNode where
    | binOp (op : BinOpType) (left right : Expr)
    | unOp (op : UnOpType) (operand : Expr)
    | condExp (condition thenExpr elseExpr : Expr)
    | constant (value : LiteralConstant)
    | var (name : String) (info : VarInfo)
    | structDot (value : Expr) (field : String)
    | arrayDeref (array index : Expr)
    | deref (value : Expr)
    | typeCast (type : Located (CType Expr)) (value : Expr)
    | sizeof (value : Expr)
    | sizeofTy (type : Located (CType Expr))
    | eFnCall (function : Expr) (arguments : List Expr)
    | compLiteral (type : CType Expr)
        (initializers : List (List Designator × Initializer))
    | arbitrary (type : CType Expr)
    | mkBool (value : Expr)
  deriving Repr, Inhabited

  inductive Expr where
    | e (node : Located ExprNode)
  deriving Repr, Inhabited

  inductive Initializer where
    | initE (value : Expr)
    | initList (initializers : List (List Designator × Initializer))
  deriving Repr, Inhabited

  inductive Designator where
    | designE (index : Expr)
    | designFld (field : String)
  deriving Repr, Inhabited
end

structure EnumBinding where
  name : String
  value : Int
  enumName : Option String
deriving Repr, Inhabited

structure ECEnv where
  enumEnv : List EnumBinding
  typing : Expr → AnalyzedCType
  structSize : String → Int

inductive GccAttribute where
  | attribId (name : String)
  | attribFn (name : String) (arguments : List Expr)
  | ownedBy (name : String)
deriving Repr, Inhabited

inductive FunctionSpec where
  | fnSpec (specification : Located String)
  | relSpec (specification : Located String)
  | modifies (names : List String)
  | didNotTranslate
  | gccAttributes (attributes : List GccAttribute)
deriving Repr, Inhabited

inductive StorageClass where
  | extern
  | static
  | auto
  | register
  | threadLocal
deriving Repr, Inhabited

inductive Declaration where
  | varDecl
      (type : CType Expr)
      (name : Located String)
      (storageClasses : List StorageClass)
      (initializer : Option Initializer)
      (attributes : List GccAttribute)
  | structDecl
      (name : Located String)
      (fields : List (CType Expr × Located String))
  | typeDecl (declarators : List (CType Expr × Located String))
  | extFnDecl
      (returnType : CType Expr)
      (name : Located String)
      (parameters : List (CType Expr × Option String))
      (storageClasses : List StorageClass)
      (specifications : List FunctionSpec)
  | enumDecl
      (name : Located (Option String))
      (enumerators : List (Located String × Option Expr))
deriving Repr, Inhabited

abbrev NamedStringExpr := Option String × String × Expr

structure AsmBlock where
  head : String
  mod1 : List NamedStringExpr
  mod2 : List NamedStringExpr
  mod3 : List String
deriving Repr, Inhabited

inductive Trappable where
  | break
  | continue
deriving Repr, DecidableEq, Inhabited

mutual
  inductive StatementNode where
    | assign (left right : Expr)
    | assignFnCall
        (left : Option Expr) (function : Expr) (arguments : List Expr)
    | chaos (value : Expr)
    | embeddedFnCall (left function : Expr) (arguments : List Expr)
    | block (items : List BlockItem)
    | whileStmt
        (condition : Expr) (invariant : Option (Located String)) (body : Statement)
    | trap (kind : Trappable) (body : Statement)
    | returnStmt (value : Option Expr)
    | returnFnCall (function : Expr) (arguments : List Expr)
    | break
    | continue
    | ifStmt (condition : Expr) (thenBranch elseBranch : Statement)
    | switch (value : Expr)
        (cases : List (List (Option Expr) × List BlockItem))
    | emptyStmt
    | auxUpdate (text : String)
    | ghostUpdate (text : String)
    | spec (annotation : (String × String) × List Statement × String)
    | asmStmt (volatile : Bool) (asmBlock : AsmBlock)
    | localInit (value : Expr)
  deriving Repr, Inhabited

  inductive Statement where
    | stmt (node : Located StatementNode)
  deriving Repr, Inhabited

  inductive BlockItem where
    | statement (value : Statement)
    | declaration (value : Located Declaration)
  deriving Repr, Inhabited
end

abbrev Body := Located (List BlockItem)

inductive ExternalDeclaration where
  | functionDefinition
      (function : CType Expr × Located String)
      (parameters : List (CType Expr × Located String))
      (storageClasses : List StorageClass)
      (specifications : List FunctionSpec)
      (body : Body)
  | declaration (value : Located Declaration)
deriving Repr, Inhabited

end Zag.Lang.AutoCorres.CParser
