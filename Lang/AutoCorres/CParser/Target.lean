/-!
# StrictC implementation numbers

Pure target models corresponding to `TargetNumbers-sig.ML` and the selected
architecture-specific `TargetNumbers.ML` files in l4v.
-/

namespace Zag.Lang.AutoCorres.CParser

inductive Architecture where
  | arm
  | armHyp
  | aarch64
  | riscv64
  | x64
deriving Repr, DecidableEq, Inhabited

inductive IntKind where
  | char
  | short
  | int
  | long
  | longLong
deriving Repr, DecidableEq, Inhabited

structure Target where
  architecture : Architecture
  boolWidth : Nat
  charWidth : Nat
  shortWidth : Nat
  intWidth : Nat
  longWidth : Nat
  longLongWidth : Nat
  pointerWidth : Nat
  pointerKind : IntKind
  charSigned : Bool
deriving Repr, DecidableEq, Inhabited

namespace Target

def arm : Target :=
  { architecture := .arm
    boolWidth := 8
    charWidth := 8
    shortWidth := 16
    intWidth := 32
    longWidth := 32
    longLongWidth := 64
    pointerWidth := 32
    pointerKind := .long
    charSigned := false }

def armHyp : Target := { arm with architecture := .armHyp }

def model64 (architecture : Architecture) : Target :=
  { architecture
    boolWidth := 8
    charWidth := 8
    shortWidth := 16
    intWidth := 32
    longWidth := 64
    longLongWidth := 64
    pointerWidth := 64
    pointerKind := .long
    charSigned := false }

def aarch64 : Target := model64 .aarch64
def riscv64 : Target := model64 .riscv64
def x64 : Target := model64 .x64

def forArchitecture : Architecture → Target
  | .arm => arm
  | .armHyp => armHyp
  | .aarch64 => aarch64
  | .riscv64 => riscv64
  | .x64 => x64

def intWidthOf (target : Target) : IntKind → Nat
  | .char => target.charWidth
  | .short => target.shortWidth
  | .int => target.intWidth
  | .long => target.longWidth
  | .longLong => target.longLongWidth

def unsignedMax (width : Nat) : Int :=
  (2 : Int) ^ width - 1

def signedMax (width : Nat) : Int :=
  (2 : Int) ^ (width - 1) - 1

def signedMin (width : Nat) : Int :=
  -((2 : Int) ^ (width - 1))

def charBit (target : Target) : Nat := target.charWidth
def unsignedCharMax (target : Target) : Int := unsignedMax target.charWidth
def unsignedShortMax (target : Target) : Int := unsignedMax target.shortWidth
def unsignedIntMax (target : Target) : Int := unsignedMax target.intWidth
def unsignedLongMax (target : Target) : Int := unsignedMax target.longWidth
def unsignedLongLongMax (target : Target) : Int := unsignedMax target.longLongWidth

-- The pinned target files define `SCHAR_MAX` using `intWidth`; preserve it.
def signedCharMax (target : Target) : Int := signedMax target.intWidth
def signedShortMax (target : Target) : Int := signedMax target.shortWidth
def signedIntMax (target : Target) : Int := signedMax target.intWidth
def signedLongMax (target : Target) : Int := signedMax target.longWidth
def signedLongLongMax (target : Target) : Int := signedMax target.longLongWidth

def signedCharMin (target : Target) : Int := signedMin target.charWidth
def signedShortMin (target : Target) : Int := signedMin target.shortWidth
def signedIntMin (target : Target) : Int := signedMin target.intWidth
def signedLongMin (target : Target) : Int := signedMin target.longWidth
def signedLongLongMin (target : Target) : Int := signedMin target.longLongWidth

def charMax (target : Target) : Int :=
  if target.charSigned then target.signedCharMax else target.unsignedCharMax

def charMin (target : Target) : Int :=
  if target.charSigned then target.signedCharMin else 0

def charLiteralConversion (target : Target) (value : Int) : Except String Int :=
  let maximum := unsignedMax target.charWidth
  if value < 0 || value > maximum then
    .error "character literal component is outside the target unsigned-char range"
  else if target.charSigned && value > signedMax target.charWidth then
    .ok (signedMin target.charWidth + value)
  else
    .ok value

end Target

end Zag.Lang.AutoCorres.CParser
