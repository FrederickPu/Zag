import Zag.Theory

/-!
  A Zag-backed Simpl fragment.

  `Basic` is not an arbitrary Lean `state -> state`; it is a typed Zag term over
  a declared Zag state.  Since Zag has no lambda term, a state transformer is
  represented as an open body under one state variable:

  `[State] ⊢ body : State`

  The default state ABI below models `State` as a list of machine words and
  exposes primitive functions for packing, projecting, and updating fields.
-/

namespace Lang.Simple

universe u v

abbrev Word := Nat
abbrev State := List Word

def WordTy : Zag.Ty :=
  .prim "Word"

def StateTy : Zag.Ty :=
  .prim "State"

def primitiveCtx : Zag.PrimitiveCtx :=
  [("State", State), ("Word", Word), ("Nat", Nat), ("Bool", Bool)]

namespace State

def ofWords (words : State) : Zag.Ty.type primitiveCtx StateTy := by
  simpa [StateTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using words

def toWords (words : Zag.Ty.type primitiveCtx StateTy) : State := by
  simpa [StateTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using words

def ofWord (word : Word) : Zag.Ty.type primitiveCtx WordTy := by
  simpa [WordTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using word

def toWord (word : Zag.Ty.type primitiveCtx WordTy) : Word := by
  simpa [WordTy, primitiveCtx, Zag.Ty.type, Zag.PrimitiveCtx.get?] using word

def val (words : State) : Zag.Val primitiveCtx :=
  .mk StateTy (ofWords words)

def wordVal (word : Word) : Zag.Val primitiveCtx :=
  .mk WordTy (ofWord word)

def asWords? (value : Zag.Val primitiveCtx) : Option State := do
  let words <- value.as? StateTy
  some (toWords words)

def asWord? (value : Zag.Val primitiveCtx) : Option Word := do
  let word <- value.as? WordTy
  some (toWord word)

def setAt? : State -> Nat -> Word -> Option State
  | [], _, _ => none
  | _ :: words, 0, word => some (word :: words)
  | head :: words, idx + 1, word => do
      let words' <- setAt? words idx word
      some (head :: words')

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
    let words <- args.mapM State.asWord?
    some (State.val words)

def stateGetFunc (idx : Nat) : Zag.PrimFunc primitiveCtx where
  args := ["State"]
  out := "Word"
  hprim := by decide
  interp := fun
    | [stateVal] => do
        let words <- State.asWords? stateVal
        let word <- words[idx]?
        some (State.wordVal word)
    | _ => none

def stateSetFunc (idx : Nat) : Zag.PrimFunc primitiveCtx where
  args := ["State", "Word"]
  out := "State"
  hprim := by decide
  interp := fun
    | [stateVal, wordVal] => do
        let words <- State.asWords? stateVal
        let word <- State.asWord? wordVal
        let words' <- State.setAt? words idx word
        some (State.val words')
    | _ => none

def statePrimFuncCtx (arity : Nat) : Zag.PrimFuncCtx primitiveCtx :=
  (List.range arity).map (fun idx => (stateGetName idx, stateGetFunc idx)) ++
  (List.range arity).map (fun idx => (stateSetName idx, stateSetFunc idx)) ++
  [(statePackName arity, statePackFunc arity)]

/-- The Zag context used by a Simple program. -/
structure Context where
  primCtx : Zag.PrimitiveCtx
  primFuncCtx : Zag.PrimFuncCtx primCtx
  stateTy : Zag.Ty

def wordStateContext (arity : Nat) : Context where
  primCtx := primitiveCtx
  primFuncCtx := statePrimFuncCtx arity
  stateTy := StateTy

def stateVarCtx (ctx : Context) : Zag.VarCtx :=
  [ctx.stateTy]

abbrev Basic (ctx : Context) : Type :=
  Zag.TermOf ctx.primCtx ctx.primFuncCtx (stateVarCtx ctx) ctx.stateTy

abbrev BExp (ctx : Context) : Type :=
  Zag.TermOf ctx.primCtx ctx.primFuncCtx (stateVarCtx ctx) (.prim "Bool")

/-- Liftable Simpl commands. Unsupported full-Simpl features are intentionally absent. -/
inductive Com (ctx : Context) (proc : Type u) (fault : Type v) where
  | Skip : Com ctx proc fault
  | Basic : Basic ctx -> Com ctx proc fault
  | Seq : Com ctx proc fault -> Com ctx proc fault -> Com ctx proc fault
  | Cond : BExp ctx -> Com ctx proc fault -> Com ctx proc fault -> Com ctx proc fault
  | While : BExp ctx -> Com ctx proc fault -> Com ctx proc fault
  | Call : proc -> Com ctx proc fault
  | Throw : Com ctx proc fault
  | Catch : Com ctx proc fault -> Com ctx proc fault -> Com ctx proc fault

namespace Com

variable {ctx : Context} {proc : Type u} {fault : Type v}

def bseq : Com ctx proc fault -> Com ctx proc fault -> Com ctx proc fault :=
  .Seq

def flatten : Com ctx proc fault -> List (Com ctx proc fault)
  | .Skip => [.Skip]
  | .Basic update => [.Basic update]
  | .Seq c1 c2 => flatten c1 ++ flatten c2
  | .Cond b c1 c2 => [.Cond b c1 c2]
  | .While b c => [.While b c]
  | .Call p => [.Call p]
  | .Throw => [.Throw]
  | .Catch c1 c2 => [.Catch c1 c2]

def sequence (seq : Com ctx proc fault -> Com ctx proc fault -> Com ctx proc fault) :
    List (Com ctx proc fault) -> Com ctx proc fault
  | [] => .Skip
  | [c] => c
  | c :: cs => seq c (sequence seq cs)

def normalize : Com ctx proc fault -> Com ctx proc fault
  | .Skip => .Skip
  | .Basic update => .Basic update
  | .Seq c1 c2 => sequence .Seq (flatten (normalize c1) ++ flatten (normalize c2))
  | .Cond b c1 c2 => .Cond b (normalize c1) (normalize c2)
  | .While b c => .While b (normalize c)
  | .Call p => .Call p
  | .Throw => .Throw
  | .Catch c1 c2 => .Catch (normalize c1) (normalize c2)

end Com

end Lang.Simple
