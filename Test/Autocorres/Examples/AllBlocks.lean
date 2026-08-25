import Test.Autocorres.Examples.AllBlocksFirst
import Test.Autocorres.Examples.AllBlocksSecond

namespace Zag.Test.Autocorres.Examples

open Zag.Lib.PeanoHeap

abbrev autocorresBlocks : BlockCtx.Raw heapCtx :=
  autocorresBlocksFirst ++ autocorresBlocksSecond

private theorem BlockCtx.Valid.append {left right : BlockCtx.Raw heapCtx}
    (hleft : BlockCtx.Valid left) (hright : BlockCtx.Valid right)
    (hdisjoint : ∀ a ∈ left.map Prod.fst, ∀ b ∈ right.map Prod.fst, a ≠ b) :
    BlockCtx.Valid (left ++ right) := by
  constructor
  · rw [List.map_append, List.nodup_append]
    exact ⟨hleft.1, hright.1, hdisjoint⟩
  · intro entry hentry name hname
    rw [List.mem_append] at hentry
    rw [List.map_append, List.mem_append]
    rcases hentry with hentry | hentry
    · exact Or.inl (hleft.2 entry hentry name hname)
    · exact Or.inr (hright.2 entry hentry name hname)

theorem autocorresBlocksValid : BlockCtx.Valid autocorresBlocks := by
  apply BlockCtx.Valid.append autocorresBlocksFirstValid autocorresBlocksSecondValid
  native_decide

abbrev autocorresCtx : Ctx where
  primCtx := heapCtx
  M := StateM Heap
  monad := StateT.instMonad
  opCtx := allocOpCtx
  blockCtx := checkedBlocks autocorresBlocks autocorresBlocksValid
  postShape := .arg Heap .pure
  wpMonad := inferInstance

end Zag.Test.Autocorres.Examples
