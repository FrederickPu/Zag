import Lang.AutoCorres.CParser.Target

/-!
# StrictC analyzed C types

Pure counterparts of the type representation and operations in
`Absyn-CType.ML` at l4v commit
`bc2599a59c43e673dca021b10b9841e9b8da4430`. Operations which raised `Fail`
in ML return `CTypeError`.
-/

namespace Zag.Lang.AutoCorres.CParser

inductive CType (α : Type) where
  | signed (kind : IntKind)
  | unsigned (kind : IntKind)
  | bool
  | plainChar
  | structTy (name : String)
  | enumTy (name : Option String)
  | ptr (type : CType α)
  | array (type : CType α) (size : Option α)
  | bitfield (signed : Bool) (width : α)
  | ident (name : String)
  | function (returnType : CType α) (parameterTypes : List (CType α))
  | void
deriving Repr, BEq, Inhabited

abbrev AnalyzedCType := CType Int

mutual
  def decEqCType [DecidableEq α] :
      (left right : CType α) → Decidable (left = right)
    | .signed left, .signed right =>
        if h : left = right then
          isTrue (by rw [h])
        else
          isFalse (fun equality => h (by injection equality))
    | .unsigned left, .unsigned right =>
        if h : left = right then
          isTrue (by rw [h])
        else
          isFalse (fun equality => h (by injection equality))
    | .bool, .bool => isTrue rfl
    | .plainChar, .plainChar => isTrue rfl
    | .structTy left, .structTy right =>
        if h : left = right then
          isTrue (by rw [h])
        else
          isFalse (fun equality => h (by injection equality))
    | .enumTy left, .enumTy right =>
        if h : left = right then
          isTrue (by rw [h])
        else
          isFalse (fun equality => h (by injection equality))
    | .ptr left, .ptr right =>
        match decEqCType left right with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun equality => h (by injection equality))
    | .array leftType leftSize, .array rightType rightSize =>
        match decEqCType leftType rightType with
        | isTrue hType =>
            if hSize : leftSize = rightSize then
              isTrue (by rw [hType, hSize])
            else
              isFalse (fun equality => hSize (by injection equality))
        | isFalse hType =>
            isFalse (fun equality => hType (by injection equality))
    | .bitfield leftSigned leftWidth, .bitfield rightSigned rightWidth =>
        if hSigned : leftSigned = rightSigned then
          if hWidth : leftWidth = rightWidth then
            isTrue (by rw [hSigned, hWidth])
          else
            isFalse (fun equality => hWidth (by injection equality))
        else
          isFalse (fun equality => hSigned (by injection equality))
    | .ident left, .ident right =>
        if h : left = right then
          isTrue (by rw [h])
        else
          isFalse (fun equality => h (by injection equality))
    | .function leftReturn leftParameters, .function rightReturn rightParameters =>
        match decEqCType leftReturn rightReturn,
            decEqCTypeList leftParameters rightParameters with
        | isTrue hReturn, isTrue hParameters =>
            isTrue (by rw [hReturn, hParameters])
        | isFalse hReturn, _ =>
            isFalse (fun equality => hReturn (by injection equality))
        | _, isFalse hParameters =>
            isFalse (fun equality => hParameters (by injection equality))
    | .void, .void => isTrue rfl
    | .signed _, .unsigned _ | .unsigned _, .signed _ => isFalse nofun
    | .signed _, .bool | .bool, .signed _ => isFalse nofun
    | .signed _, .plainChar | .plainChar, .signed _ => isFalse nofun
    | .signed _, .structTy _ | .structTy _, .signed _ => isFalse nofun
    | .signed _, .enumTy _ | .enumTy _, .signed _ => isFalse nofun
    | .signed _, .ptr _ | .ptr _, .signed _ => isFalse nofun
    | .signed _, .array _ _ | .array _ _, .signed _ => isFalse nofun
    | .signed _, .bitfield _ _ | .bitfield _ _, .signed _ => isFalse nofun
    | .signed _, .ident _ | .ident _, .signed _ => isFalse nofun
    | .signed _, .function _ _ | .function _ _, .signed _ => isFalse nofun
    | .signed _, .void | .void, .signed _ => isFalse nofun
    | .unsigned _, .bool | .bool, .unsigned _ => isFalse nofun
    | .unsigned _, .plainChar | .plainChar, .unsigned _ => isFalse nofun
    | .unsigned _, .structTy _ | .structTy _, .unsigned _ => isFalse nofun
    | .unsigned _, .enumTy _ | .enumTy _, .unsigned _ => isFalse nofun
    | .unsigned _, .ptr _ | .ptr _, .unsigned _ => isFalse nofun
    | .unsigned _, .array _ _ | .array _ _, .unsigned _ => isFalse nofun
    | .unsigned _, .bitfield _ _ | .bitfield _ _, .unsigned _ => isFalse nofun
    | .unsigned _, .ident _ | .ident _, .unsigned _ => isFalse nofun
    | .unsigned _, .function _ _ | .function _ _, .unsigned _ => isFalse nofun
    | .unsigned _, .void | .void, .unsigned _ => isFalse nofun
    | .bool, .plainChar | .plainChar, .bool => isFalse nofun
    | .bool, .structTy _ | .structTy _, .bool => isFalse nofun
    | .bool, .enumTy _ | .enumTy _, .bool => isFalse nofun
    | .bool, .ptr _ | .ptr _, .bool => isFalse nofun
    | .bool, .array _ _ | .array _ _, .bool => isFalse nofun
    | .bool, .bitfield _ _ | .bitfield _ _, .bool => isFalse nofun
    | .bool, .ident _ | .ident _, .bool => isFalse nofun
    | .bool, .function _ _ | .function _ _, .bool => isFalse nofun
    | .bool, .void | .void, .bool => isFalse nofun
    | .plainChar, .structTy _ | .structTy _, .plainChar => isFalse nofun
    | .plainChar, .enumTy _ | .enumTy _, .plainChar => isFalse nofun
    | .plainChar, .ptr _ | .ptr _, .plainChar => isFalse nofun
    | .plainChar, .array _ _ | .array _ _, .plainChar => isFalse nofun
    | .plainChar, .bitfield _ _ | .bitfield _ _, .plainChar => isFalse nofun
    | .plainChar, .ident _ | .ident _, .plainChar => isFalse nofun
    | .plainChar, .function _ _ | .function _ _, .plainChar => isFalse nofun
    | .plainChar, .void | .void, .plainChar => isFalse nofun
    | .structTy _, .enumTy _ | .enumTy _, .structTy _ => isFalse nofun
    | .structTy _, .ptr _ | .ptr _, .structTy _ => isFalse nofun
    | .structTy _, .array _ _ | .array _ _, .structTy _ => isFalse nofun
    | .structTy _, .bitfield _ _ | .bitfield _ _, .structTy _ => isFalse nofun
    | .structTy _, .ident _ | .ident _, .structTy _ => isFalse nofun
    | .structTy _, .function _ _ | .function _ _, .structTy _ => isFalse nofun
    | .structTy _, .void | .void, .structTy _ => isFalse nofun
    | .enumTy _, .ptr _ | .ptr _, .enumTy _ => isFalse nofun
    | .enumTy _, .array _ _ | .array _ _, .enumTy _ => isFalse nofun
    | .enumTy _, .bitfield _ _ | .bitfield _ _, .enumTy _ => isFalse nofun
    | .enumTy _, .ident _ | .ident _, .enumTy _ => isFalse nofun
    | .enumTy _, .function _ _ | .function _ _, .enumTy _ => isFalse nofun
    | .enumTy _, .void | .void, .enumTy _ => isFalse nofun
    | .ptr _, .array _ _ | .array _ _, .ptr _ => isFalse nofun
    | .ptr _, .bitfield _ _ | .bitfield _ _, .ptr _ => isFalse nofun
    | .ptr _, .ident _ | .ident _, .ptr _ => isFalse nofun
    | .ptr _, .function _ _ | .function _ _, .ptr _ => isFalse nofun
    | .ptr _, .void | .void, .ptr _ => isFalse nofun
    | .array _ _, .bitfield _ _ | .bitfield _ _, .array _ _ => isFalse nofun
    | .array _ _, .ident _ | .ident _, .array _ _ => isFalse nofun
    | .array _ _, .function _ _ | .function _ _, .array _ _ => isFalse nofun
    | .array _ _, .void | .void, .array _ _ => isFalse nofun
    | .bitfield _ _, .ident _ | .ident _, .bitfield _ _ => isFalse nofun
    | .bitfield _ _, .function _ _ | .function _ _, .bitfield _ _ => isFalse nofun
    | .bitfield _ _, .void | .void, .bitfield _ _ => isFalse nofun
    | .ident _, .function _ _ | .function _ _, .ident _ => isFalse nofun
    | .ident _, .void | .void, .ident _ => isFalse nofun
    | .function _ _, .void | .void, .function _ _ => isFalse nofun
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf <;> decreasing_trivial

  def decEqCTypeList [DecidableEq α] :
      (left right : List (CType α)) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse nofun
    | _ :: _, [] => isFalse nofun
    | leftHead :: leftTail, rightHead :: rightTail =>
        match decEqCType leftHead rightHead, decEqCTypeList leftTail rightTail with
        | isTrue hHead, isTrue hTail => isTrue (by rw [hHead, hTail])
        | isFalse hHead, _ =>
            isFalse (fun equality => hHead (by injection equality))
        | _, isFalse hTail =>
            isFalse (fun equality => hTail (by injection equality))
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf <;> decreasing_trivial
end

instance instDecidableEqCType [DecidableEq α] : DecidableEq (CType α) :=
  decEqCType

inductive CTypeError where
  | nonArithmeticType (operation typeName : String)
  | maximumUndefined (typeName : String)
  | minimumUndefined (typeName : String)
  | widthUndefined (typeName : String)
  | notUnifiable (left right : String)
  | invalidByteWidth
  | incompleteArraySize
  | bitfieldSize
  | typedefSize (name : String)
  | functionSize
  | voidSize
deriving Repr, DecidableEq, Inhabited

namespace IntKind

def name : IntKind → String
  | .char => "char"
  | .short => "short"
  | .int => "int"
  | .long => "long"
  | .longLong => "longlong"

def rank : IntKind → Nat
  | .char => 1
  | .short => 2
  | .int => 3
  | .long => 4
  | .longLong => 5

end IntKind

namespace CType

def isSigned (target : Target) : CType α → Bool
  | .signed _ => true
  | .plainChar => target.charSigned
  | _ => false

def scalarType : CType α → Bool
  | .signed _ | .unsigned _ | .plainChar | .ptr _ | .enumTy _ | .array _ _ | .bool => true
  | _ => false

def ptrType : CType α → Bool
  | .ptr _ => true
  | _ => false

def integerType (type : CType α) : Bool :=
  type.scalarType && !type.ptrType

def arithmeticType (type : CType α) : Bool :=
  type.integerType

def arrayType : CType α → Bool
  | .array _ _ => true
  | _ => false

def functionType : CType α → Bool
  | .function _ _ => true
  | _ => false

def aggregateType : CType α → Bool
  | .structTy _ | .array _ _ => true
  | _ => false

mutual
  def fparamNorm : CType α → CType α
    | .ptr (.array type none) => .ptr (.ptr (fparamNorm type))
    | .ptr type => .ptr (fparamNorm type)
    | .array type size => .array (fparamNorm type) size
    | .function returnType parameterTypes =>
        .function (fparamNorm returnType) (parameterTypes.map paramNorm)
    | type => type

  def paramNorm : CType α → CType α
    | .function returnType parameterTypes =>
        .ptr (.function (fparamNorm returnType) (parameterTypes.map paramNorm))
    | .array type _ => .ptr (fparamNorm type)
    | type => fparamNorm type
end

def removeEnums : CType α → CType α
  | .ptr type => .ptr type.removeEnums
  | .array type size => .array type.removeEnums size
  | .function returnType parameterTypes =>
      .function returnType.removeEnums (parameterTypes.map removeEnums)
  | .enumTy _ => .signed .int
  | type => type

def typeNameWith (showComponent : α → String) : CType α → String
  | .signed .char => "signed_char"
  | .signed kind => kind.name
  | .unsigned .int => "unsigned"
  | .unsigned kind => "unsigned_" ++ kind.name
  | .plainChar => "char"
  | .bool => "_Bool"
  | .ptr type => "ptr_to_" ++ typeNameWith showComponent type
  | .array type (some size) =>
      typeNameWith showComponent type ++ "_array" ++ showComponent size
  | .array type none => typeNameWith showComponent type ++ "_array[incomplete]"
  | .structTy name => "struct_" ++ name
  | .ident name => "typedef_" ++ name
  | .bitfield true width => "int:" ++ showComponent width
  | .bitfield false width => "unsigned:" ++ showComponent width
  | .void => "void"
  | .function returnType parameterTypes =>
      "[" ++ String.intercalate "," (parameterTypes.map (typeNameWith showComponent)) ++
        "]->" ++ typeNameWith showComponent returnType
  | .enumTy (some name) => "enum_" ++ name
  | .enumTy none => "anonymous_enum"

def typeName (type : AnalyzedCType) : String :=
  typeNameWith toString type

def tyName0 (showComponent : α → String) (type : CType α) : String :=
  typeNameWith showComponent type

def tyName (type : AnalyzedCType) : String :=
  typeName type

private def signedCharMaximum (target : Target) : Int :=
  -- This is intentionally not `signedMax target.charWidth`; it preserves the pin.
  Target.signedMax target.intWidth

def integerPromotions (target : Target) : CType α → CType α
  | .bool => .signed .int
  | .signed .char => .signed .int
  | .unsigned .char =>
      if Target.unsignedMax target.charWidth > Target.signedMax target.intWidth then
        .unsigned .int
      else
        .signed .int
  | .signed .short => .signed .int
  | .unsigned .short =>
      if Target.unsignedMax target.shortWidth > Target.signedMax target.intWidth then
        .unsigned .int
      else
        .signed .int
  | .plainChar =>
      let charMaximum :=
        if target.charSigned then signedCharMaximum target else Target.unsignedMax target.charWidth
      if charMaximum > Target.signedMax target.intWidth then .unsigned .int else .signed .int
  | .enumTy _ => .signed .int
  | type => type

def maximum (target : Target) (type : CType α) : Except CTypeError Int :=
  match type with
  | .bool => .ok 1
  | .plainChar =>
      .ok (if target.charSigned then signedCharMaximum target else Target.unsignedMax target.charWidth)
  | .unsigned kind => .ok (Target.unsignedMax (target.intWidthOf kind))
  | .signed .char => .ok (signedCharMaximum target)
  | .signed kind => .ok (Target.signedMax (target.intWidthOf kind))
  | _ => .error (.maximumUndefined (typeNameWith (fun _ => "") type))

def minimum (target : Target) (type : CType α) : Except CTypeError Int :=
  match type with
  | .unsigned _ | .bool => .ok 0
  | .signed kind => .ok (Target.signedMin (target.intWidthOf kind))
  | .plainChar =>
      .ok (if target.charSigned then Target.signedMin target.charWidth else 0)
  | _ => .error (.minimumUndefined (typeNameWith (fun _ => "") type))

def imax (target : Target) (type : CType α) : Except CTypeError Int :=
  maximum target type

def imin (target : Target) (type : CType α) : Except CTypeError Int :=
  minimum target type

private def signedInfo (operation : String) (type : CType α) :
    Except CTypeError (Bool × IntKind) :=
  match type with
  | .signed kind => .ok (true, kind)
  | .unsigned kind => .ok (false, kind)
  | _ => .error (.nonArithmeticType operation (typeNameWith (fun _ => "") type))

def arithmeticConversion (target : Target) (left right : CType α) :
    Except CTypeError (CType α) := do
  let left := left.integerPromotions target
  let right := right.integerPromotions target
  let (leftSigned, leftKind) ← signedInfo "arithmeticConversion" left
  let (rightSigned, rightKind) ← signedInfo "arithmeticConversion" right
  if leftSigned == rightSigned then
    if leftKind.rank < rightKind.rank then return right else return left
  let signedType := if leftSigned then left else right
  let signedKind := if leftSigned then leftKind else rightKind
  let unsignedType := if leftSigned then right else left
  let unsignedKind := if leftSigned then rightKind else leftKind
  if signedKind.rank < unsignedKind.rank then
    return unsignedType
  if (← signedType.maximum target) ≥ (← unsignedType.maximum target) then
    return signedType
  return .unsigned signedKind

private def pointerLike : CType α → Bool
  | .ptr _ | .array _ _ => true
  | _ => false

private def unifyTypesCore [DecidableEq α] (target : Target) (left right : CType α) :
    Except CTypeError (CType α) := do
  letI : BEq α := ⟨fun a b => decide (a = b)⟩
  let right := match right with | .array type _ => CType.ptr type | type => type
  match left, right with
  | .signed _, .ptr _ | .unsigned _, .ptr _ | .plainChar, .ptr _ | .enumTy _, .ptr _ =>
      return right
  | .ptr leftType, .ptr rightType =>
      if leftType == .void then
        return right
      else if rightType == .void then
        return left
      else if leftType == rightType then
        return left
      else
        throw (CTypeError.notUnifiable (typeNameWith (fun _ => "") left)
          (typeNameWith (fun _ => "") right))
  | _, _ =>
      if left.integerType && right.integerType then
        arithmeticConversion target left right
      else if left == right then
        return left
      else
        throw (CTypeError.notUnifiable (typeNameWith (fun _ => "") left)
          (typeNameWith (fun _ => "") right))

def unifyTypes [DecidableEq α] (target : Target) (left right : CType α) :
    Except CTypeError (CType α) :=
  if left.pointerLike && !right.pointerLike then
    unifyTypesCore target right left
  else
    unifyTypesCore target left right

def intWidth (target : Target) (kind : IntKind) : Nat :=
  target.intWidthOf kind

def width (target : Target) (type : CType α) : Except CTypeError Nat :=
  match type with
  | .signed kind | .unsigned kind => .ok (target.intWidthOf kind)
  | .plainChar => .ok target.charWidth
  | _ => .error (.widthUndefined (typeNameWith (fun _ => "") type))

def tyWidth (target : Target) (type : CType α) : Except CTypeError Nat :=
  width target type

def intSizeOf (target : Target) (kind : IntKind) : Except CTypeError Nat :=
  if target.charWidth == 0 then
    .error .invalidByteWidth
  else
    .ok (target.intWidthOf kind / target.charWidth)

def intSizeof := intSizeOf

def sizeof (target : Target) (structSizes : String → Int) :
    AnalyzedCType → Except CTypeError Int
  | .signed kind | .unsigned kind => intSizeOf target kind
      |>.map Int.ofNat
  | .plainChar => .ok 1
  | .bool =>
      if target.charWidth == 0 then .error .invalidByteWidth
       else .ok (Int.ofNat (target.boolWidth / target.charWidth))
  | .structTy name => .ok (structSizes name)
  | .enumTy _ => (intSizeOf target .int).map Int.ofNat
  | .ptr _ =>
      if target.charWidth == 0 then .error .invalidByteWidth
       else .ok (Int.ofNat (target.pointerWidth / target.charWidth))
  | .array type (some count) => return count * (← sizeof target structSizes type)
  | .array _ none => .error .incompleteArraySize
  | .bitfield _ _ => .error .bitfieldSize
  | .ident name => .error (.typedefSize name)
  | .function _ _ => .error .functionSize
  | .void => .error .voidSize

def sizeOf := sizeof

namespace ImplementationTypes

def sizeT : CType α := .unsigned .int

def ptrdiffT : CType α := .signed .int

def ptrvalT (target : Target) : CType α := .unsigned target.pointerKind

end ImplementationTypes

end CType

end Zag.Lang.AutoCorres.CParser
