import Meta.Eval.Composition

/-! Induction adapters for recursive evaluation specifications. -/

namespace Zag

/-- Prove a self-recursive block specification by induction on `target`. -/
syntax (name := tailInductionTactic) "tail_induction" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace ident
  (" generalizing" (ppSpace colGt ident)+)? : tactic

syntax (name := tailInductionQTactic) "tail_induction?" (ppSpace num)?
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace ident
  (" generalizing" (ppSpace colGt ident)+)? : tactic

macro_rules
| `(tactic| tail_induction $[$bound?]? [$lemmas,*] $target:ident) =>
    `(tactic|
      (apply_refinement (PropRefinement.natInduction $target)
       · evaluates_call_machine $[$bound?]? [$lemmas,*]
       ·
         intro $target ih
         evaluates_call_machine $[$bound?]? [$lemmas,*]
         zspec_call $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction $[$bound?]? [$lemmas,*] $target:ident generalizing $vars*) =>
    `(tactic|
      (revert $vars*
       apply_refinement (PropRefinement.natInduction $target)
       ·
         intro $vars*
         evaluates_call_machine $[$bound?]? [$lemmas,*]
       ·
         intro $target ih $vars*
         evaluates_call_machine $[$bound?]? [$lemmas,*]
         zspec_call $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction? $[$bound?]? [$lemmas,*] $target:ident) =>
    `(tactic|
      (apply_refinement (PropRefinement.natInduction $target)
       · evaluates_call_machine? $[$bound?]? [$lemmas,*]
       ·
         intro $target ih
         evaluates_call_machine $[$bound?]? [$lemmas,*]
         zspec_call? $[$bound?]? [$lemmas,*] ih))
| `(tactic| tail_induction? $[$bound?]? [$lemmas,*] $target:ident generalizing $vars*) =>
    `(tactic|
      (revert $vars*
       apply_refinement (PropRefinement.natInduction $target)
       ·
         intro $vars*
         evaluates_call_machine? $[$bound?]? [$lemmas,*]
       ·
         intro $target ih $vars*
         evaluates_call_machine $[$bound?]? [$lemmas,*]
         zspec_call? $[$bound?]? [$lemmas,*] ih))

end Zag
