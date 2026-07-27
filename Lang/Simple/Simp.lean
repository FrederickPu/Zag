import Lang.Simple.Defs

/-!
  Peephole normalization for Simpl commands (not part of the embedding).
-/

namespace Lang.Simple.Com

variable {ctx : Context} {proc : Type u} {fault : Type v}

def flatten : Com ctx proc fault → List (Com ctx proc fault)
  | .Skip => [.Skip]
  | .Basic update => [.Basic update]
  | .Guard b c => [.Guard b c]
  | .Seq c1 c2 => flatten c1 ++ flatten c2
  | .Cond b c1 c2 => [.Cond b c1 c2]
  | .While b c => [.While b c]
  | .Call p => [.Call p]
  | .Throw => [.Throw]
  | .Catch c1 c2 => [.Catch c1 c2]

def sequence (seq : Com ctx proc fault → Com ctx proc fault → Com ctx proc fault) :
    List (Com ctx proc fault) → Com ctx proc fault
  | [] => .Skip
  | [c] => c
  | c :: cs => seq c (sequence seq cs)

def normalize : Com ctx proc fault → Com ctx proc fault
  | .Skip => .Skip
  | .Basic update => .Basic update
  | .Guard b c => .Guard b (normalize c)
  | .Seq c1 c2 => sequence .Seq (flatten (normalize c1) ++ flatten (normalize c2))
  | .Cond b c1 c2 => .Cond b (normalize c1) (normalize c2)
  | .While b c => .While b (normalize c)
  | .Call p => .Call p
  | .Throw => .Throw
  | .Catch c1 c2 => .Catch (normalize c1) (normalize c2)

end Lang.Simple.Com
