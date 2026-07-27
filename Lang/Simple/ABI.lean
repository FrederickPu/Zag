import Lang.Simple.Defs

/-!
  Concrete word/state ABI for Simpl → AutoCorres pipeline.

  **`Word` is `BitVec 32`**. WA maps to `Nat` under no-overflow (see `Lift/WA.lean`).

  **State = full C-parser-style record** (AC `'s` in L1Defs.thy:16), not a bare list:
  ```
  FullState = { locals : List Word; globals : Globals }
  Globals   = { heap : Heap }    -- residual after LocalVarExtract (L2Defs.thy:11)
  ```
  Local lookup = field access at index i (`gets`/`L1_modify` — L1Defs.thy:19).
  Position i is named by `LocalContext` (C0 `x`,`y`,…).
-/

namespace Lang.Simple.ABI

open Lang.Simple

/-- Machine word width for the C0 / Simpl ABI. -/
def wordWidth : Nat := 32

/-- Concrete machine word: 32-bit bitvector (unsigned view for `+`, `-`, `<`). -/
abbrev Word := BitVec wordWidth

/-- Byte/word heap (concrete before HL). -/
abbrev Heap := List Word
abbrev Ptr := Nat

/--
  Globals residual after L2 local extract.
  AC: ambient `'s` of L2_monad — L2Defs.thy:11 / LocalVarExtract.
-/
structure Globals where
  heap : Heap
  deriving Repr

/--
  Full SIMPL/'s record (locals + globals/heap).
  AC: `'s` of L1_monad — L1Defs.thy:16
-/
structure FullState where
  locals : List Word
  globals : Globals
  deriving Repr

/-- Ambient Simpl/L1 state = full record. -/
abbrev State := FullState

/-- L2 ambient residual. -/
abbrev L2State := Globals

/-- AC `st` in L2corres — L2Defs.thy:85–90 -/
def projectGlobals (s : FullState) : L2State := s.globals

/-- Host `Nat` → machine word (truncating). -/
def Word.ofNat (n : Nat) : Word :=
  BitVec.ofNat wordWidth n

/-- Machine word → host `Nat` (unsigned). -/
def Word.toNat (w : Word) : Nat :=
  BitVec.toNat w

def WordTy : Zag.Ty :=
  .prim "Word"

def StateTy : Zag.Ty :=
  .prim "State"

def HeapTy : Zag.Ty := .prim "Heap"
def PtrTy : Zag.Ty := .prim "Ptr"

/--
  Shared Simpl/L1/L2 prims (AutoCorres.md §5.0): one `primCtx`, `M := Id`,
  state threaded explicitly (Zag encoding of AC StateM).
-/
def primitiveCtx : Zag.PrimitiveCtx :=
  { prims := [
      .of "State" State, .of "Word" Word, .of "Nat" Nat, .of "Bool" Bool,
      .of "Unit" Unit, .of "Heap" Heap, .of "Ptr" Ptr]
    M := Id
    monad := inferInstance }

instance : Zag.Peano.Types primitiveCtx where
  natType := by rfl
  boolType := by rfl

/-- List update helper (locals and heap). -/
def setAt? : List Word → Nat → Word → Option (List Word)
  | [], _, _ => none
  | _ :: words, 0, word => some (word :: words)
  | head :: words, idx + 1, word => do
      let words' ← setAt? words idx word
      some (head :: words')

namespace State

def ofFull (s : State) : Zag.Ty.type primitiveCtx StateTy := by
  simpa [StateTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using s

def toFull (s : Zag.Ty.type primitiveCtx StateTy) : State := by
  simpa [StateTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using s

def ofWord (word : Word) : Zag.Ty.type primitiveCtx WordTy := by
  simpa [WordTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using word

def toWord (word : Zag.Ty.type primitiveCtx WordTy) : Word := by
  simpa [WordTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using word

/-- Pack locals into full state (default empty heap). AC record construction. -/
def mk (locals : List Word) (heap : Heap := []) : State :=
  ⟨locals, ⟨heap⟩⟩

def val (locals : List Word) (heap : Heap := []) : Zag.Val primitiveCtx :=
  .mk StateTy (ofFull (mk locals heap))

def valFull (s : State) : Zag.Val primitiveCtx :=
  .mk StateTy (ofFull s)

def wordVal (word : Word) : Zag.Val primitiveCtx :=
  .mk WordTy (ofWord word)

def asFull? (value : Zag.Val primitiveCtx) : Option State := do
  let s ← value.as? StateTy
  some (toFull s)

/-- Locals field only (compat name `toWords` / `asWords?`). -/
def toWords (s : Zag.Ty.type primitiveCtx StateTy) : List Word :=
  (toFull s).locals

def asWords? (value : Zag.Val primitiveCtx) : Option (List Word) := do
  let s ← asFull? value
  some s.locals

def asWord? (value : Zag.Val primitiveCtx) : Option Word := do
  let word ← value.as? WordTy
  some (toWord word)

/-- Field get — AC `L2_gets f names ≡ liftE (gets f)` — L2Defs.thy:15 -/
def getLocal? (s : State) (i : Nat) : Option Word :=
  s.locals[i]?

/-- Field set — AC L1_modify — L1Defs.thy:19 -/
def setLocal? (s : State) (i : Nat) (w : Word) : Option State := do
  let locals' ← setAt? s.locals i w
  some { s with locals := locals' }

end State

def statePackName (arity : Nat) : String :=
  "state.pack." ++ toString arity

def stateGetName (idx : Nat) : String :=
  "state.get." ++ toString idx

def stateSetName (idx : Nat) : String :=
  "state.set." ++ toString idx

def statePackFunc (arity : Nat) : Zag.PrimFunc primitiveCtx where
  args := List.replicate arity "Word"
  out := "State"
  hprim := by
    intro name hname
    simp only [List.mem_cons, List.mem_replicate] at hname
    rcases hname with hname | ⟨_, hname⟩
    · simp [primitiveCtx, hname]
    · simp [primitiveCtx, hname]
  interp := fun args => do
    let words ← args.mapM State.asWord?
    some (State.val words)

def stateGetFunc (idx : Nat) : Zag.PrimFunc primitiveCtx where
  args := ["State"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [stateVal] => do
        let s ← State.asFull? stateVal
        let word ← s.getLocal? idx
        some (State.wordVal word)
    | _ => none

def stateSetFunc (idx : Nat) : Zag.PrimFunc primitiveCtx where
  args := ["State", "Word"]
  out := "State"
  hprim := by decide
  interp := fun
    | [stateVal, wordVal] => do
        let s ← State.asFull? stateVal
        let word ← State.asWord? wordVal
        let s' ← s.setLocal? idx word
        some (State.valFull s')
    | _ => none

/-- Unsigned 32-bit comparison (before WA). -/
def wordLtFunc : Zag.PrimFunc primitiveCtx where
  args := ["Word", "Word"]
  out := "Bool"
  hprim := by decide
  interp := fun
    | [lhs, rhs] => do
        let a ← State.asWord? lhs
        let b ← State.asWord? rhs
        some (Zag.Val.bool (decide (BitVec.ult a b)))
    | _ => none

/-- Wrapping 32-bit addition (concrete; WA rewrites to `Nat.add` under no-overflow side condition). -/
def wordAddFunc : Zag.PrimFunc primitiveCtx where
  args := ["Word", "Word"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [lhs, rhs] => do
        let a ← State.asWord? lhs
        let b ← State.asWord? rhs
        some (State.wordVal (a + b))
    | _ => none

/-- Wrapping 32-bit subtraction. -/
def wordSubFunc : Zag.PrimFunc primitiveCtx where
  args := ["Word", "Word"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [lhs, rhs] => do
        let a ← State.asWord? lhs
        let b ← State.asWord? rhs
        some (State.wordVal (a - b))
    | _ => none

def wordPrimFuncs : Zag.PrimFuncCtx primitiveCtx :=
  [("word.lt", wordLtFunc), ("word.add", wordAddFunc), ("word.sub", wordSubFunc)]

/--
  HL heap ABI (AutoCorres HeapLift.thy): concrete `Heap`/`Ptr` plus typed `HeapW`.
  `heap.load` / `heap.store` pure first-cut; HL rewrites to `heap.w.*` + valid.
-/
def heapPrimitiveCtx : Zag.PrimitiveCtx :=
  { prims := [
      .of "State" State, .of "Word" Word, .of "Nat" Nat, .of "Bool" Bool,
      .of "Unit" Unit, .of "Heap" Heap, .of "Ptr" Ptr, .of "HeapW" Heap]
    M := Id
    monad := inferInstance }

instance : Zag.Peano.Types heapPrimitiveCtx where
  natType := by rfl
  boolType := by rfl

def heapAsList (v : Zag.Ty.type heapPrimitiveCtx (.prim "Heap")) : Heap := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using v

def heapWAsList (v : Zag.Ty.type heapPrimitiveCtx (.prim "HeapW")) : Heap := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using v

def ptrAsNat (v : Zag.Ty.type heapPrimitiveCtx (.prim "Ptr")) : Ptr := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using v

def wordAsNat (v : Zag.Ty.type heapPrimitiveCtx (.prim "Word")) : Word := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using v

def ofHeapWord (w : Word) : Zag.Ty.type heapPrimitiveCtx (.prim "Word") := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using w

def ofHeap (h : Heap) : Zag.Ty.type heapPrimitiveCtx (.prim "Heap") := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using h

def ofHeapW (h : Heap) : Zag.Ty.type heapPrimitiveCtx (.prim "HeapW") := by
  simpa [heapPrimitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using h

def heapLoadFunc : Zag.PrimFunc heapPrimitiveCtx where
  args := ["Heap", "Ptr"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [h, p] => do
        let heap ← h.as? (.prim "Heap")
        let ptr ← p.as? (.prim "Ptr")
        let w ← (heapAsList heap)[ptrAsNat ptr]?
        some (Zag.Val.mk (.prim "Word") (ofHeapWord w))
    | _ => none

def heapStoreFunc : Zag.PrimFunc heapPrimitiveCtx where
  args := ["Heap", "Ptr", "Word"]
  out := "Heap"
  hprim := by decide
  interp := fun
    | [h, p, w] => do
        let heap ← h.as? (.prim "Heap")
        let ptr ← p.as? (.prim "Ptr")
        let word ← w.as? (.prim "Word")
        let heap' ← setAt? (heapAsList heap) (ptrAsNat ptr) (wordAsNat word)
        some (Zag.Val.mk (.prim "Heap") (ofHeap heap'))
    | _ => none

def heapWGetFunc : Zag.PrimFunc heapPrimitiveCtx where
  args := ["HeapW", "Ptr"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [h, p] => do
        let heap ← h.as? (.prim "HeapW")
        let ptr ← p.as? (.prim "Ptr")
        let w ← (heapWAsList heap)[ptrAsNat ptr]?
        some (Zag.Val.mk (.prim "Word") (ofHeapWord w))
    | _ => none

def heapWSetFunc : Zag.PrimFunc heapPrimitiveCtx where
  args := ["HeapW", "Ptr", "Word"]
  out := "HeapW"
  hprim := by decide
  interp := fun
    | [h, p, w] => do
        let heap ← h.as? (.prim "HeapW")
        let ptr ← p.as? (.prim "Ptr")
        let word ← w.as? (.prim "Word")
        let heap' ← setAt? (heapWAsList heap) (ptrAsNat ptr) (wordAsNat word)
        some (Zag.Val.mk (.prim "HeapW") (ofHeapW heap'))
    | _ => none

def heapWValidFunc : Zag.PrimFunc heapPrimitiveCtx where
  args := ["HeapW", "Ptr"]
  out := "Bool"
  hprim := by decide
  interp := fun
    | [h, p] => do
        let heap ← h.as? (.prim "HeapW")
        let ptr ← p.as? (.prim "Ptr")
        some (Zag.Val.bool (decide (ptrAsNat ptr < (heapWAsList heap).length)))
    | _ => none

def heapPrimFuncs : Zag.PrimFuncCtx heapPrimitiveCtx :=
  [("heap.load", heapLoadFunc), ("heap.store", heapStoreFunc),
   ("heap.w.get", heapWGetFunc), ("heap.w.set", heapWSetFunc),
   ("heap.w.valid", heapWValidFunc)]

/-- Concrete heap ops on shared Simpl/L1/L2 primCtx (before HL). -/
def primHeapLoadFunc : Zag.PrimFunc primitiveCtx where
  args := ["Heap", "Ptr"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [h, p] => do
        let heap ← h.as? HeapTy
        let ptr ← p.as? PtrTy
        let hp : Heap := by simpa [HeapTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using heap
        let pt : Ptr := by simpa [PtrTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using ptr
        let w ← hp[pt]?
        some (State.wordVal w)
    | _ => none

def primHeapStoreFunc : Zag.PrimFunc primitiveCtx where
  args := ["Heap", "Ptr", "Word"]
  out := "Heap"
  hprim := by decide
  interp := fun
    | [h, p, w] => do
        let heap ← h.as? HeapTy
        let ptr ← p.as? PtrTy
        let word ← State.asWord? w
        let hp : Heap := by simpa [HeapTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using heap
        let pt : Ptr := by simpa [PtrTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using ptr
        let heap' ← setAt? hp pt word
        some (Zag.Val.mk HeapTy (by simpa [HeapTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using heap'))
    | _ => none

def statePrimFuncCtx (arity : Nat) : Zag.PrimFuncCtx primitiveCtx :=
  (List.range arity).map (fun idx => (stateGetName idx, stateGetFunc idx)) ++
  (List.range arity).map (fun idx => (stateSetName idx, stateSetFunc idx)) ++
  [(statePackName arity, statePackFunc arity)] ++
  wordPrimFuncs ++
  [("heap.load", primHeapLoadFunc), ("heap.store", primHeapStoreFunc)]

def wordStateContext (arity : Nat) : Context where
  zagCtx := {
    primCtx := primitiveCtx
    primFuncCtx := statePrimFuncCtx arity
    opCtx := Zag.Peano.opCtx primitiveCtx
  }
  stateTy := StateTy
  types := inferInstance
  iteOp := by rfl

/--
  Lookup a declared primFunc by Fin index (for hasType proofs).
-/
theorem hasType_primFunc_at {ctx : Zag.Ctx} {varCtx : Zag.VarCtx}
    (idx : Fin ctx.primFuncCtx.length) :
    Zag.Term.hasType ctx varCtx
      (.primFunc ctx.primFuncCtx[idx].1) ctx.primFuncCtx[idx].2.ty :=
  Zag.Term.hasType.primFunc (ctx := ctx) (varCtx := varCtx) (idx := idx)

/-- BitVec-32 word ABI placeholder for WA (unsigned `Nat` target side is in WA.lean). -/
abbrev Word32 := BitVec 32

def word32PrimitiveCtx : Zag.PrimitiveCtx :=
  { prims := [.of "Word" Word32, .of "Nat" Nat, .of "Bool" Bool, .of "Int" Int, .of "Unit" Unit]
    M := Id
    monad := inferInstance }

instance : Zag.Peano.Types word32PrimitiveCtx where
  natType := by rfl
  boolType := by rfl

end Lang.Simple.ABI
