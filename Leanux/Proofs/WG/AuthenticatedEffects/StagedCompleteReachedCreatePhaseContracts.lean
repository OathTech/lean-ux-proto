import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseModel

/-! Semantic coverage of the existing fixed source points. Composition uses
actual successful original binds; a whole-tree certificate is never inferred
from the final account. Concrete trees must discharge their leaf contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal CreatePoints
set_option maxHeartbeats 600000

def Covers (E : CreatePoints.History → World → Prop) :
    {α : Type} → {action : PrefixM Event α} → Shape action → World → CreatePoints.History → Prop
  | _,_,.pure _,w,h=>E h w
  | _,_,.atom token,w,h=>E h w ∧ ∀ value u middle,
      runPrefix token.action w h=(.ok (value,u),middle) → E middle u
  | _,action,.child _,w,h=>E h w ∧ ∀ value u middle,
      runPrefix action w h=(.ok (value,u),middle) → E middle u
  | _,_,@Shape.bind _ _ body _ head tail,w,h=>Covers E head w h ∧ ∀ value u middle,
      runPrefix body w h=(.ok (value,u),middle) → Covers E (tail value) u middle
  | _,_,.marked _ body,w,h=>Covers E body w h

theorem Covers.entry {shape : Shape action} (safe : Covers E shape w h) : E h w := by
  induction shape with
  | pure=>exact safe
  | atom=>exact safe.1
  | child=>exact safe.1
  | bind head tail ih _=>exact ih safe.1
  | marked label body ih=>exact ih safe

theorem Covers.normal {shape : Shape action} (safe : Covers E shape w h)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : E middle u := by
  induction shape generalizing w h with
  | pure returned=>cases performed; exact safe
  | atom token=>exact safe.2 _ _ _ performed
  | child token=>exact safe.2 _ _ _ performed
  | bind head tail ih rest=>
    rw [runPrefix_bind] at performed
    rename_i body next
    cases leading : runPrefix body w h with
    | mk out prior=>
      rw [leading] at performed
      cases out with
      | error=>cases performed
      | ok pair=>
        obtain ⟨value,v⟩:=pair
        exact rest value (safe.2 value v prior leading) performed
  | marked label body ih=>exact ih safe performed

/-- Structural source contracts imply evidence for each actual canonical
point, including points reached before a later stopped continuation. -/
theorem Covers.point {shape : Shape action} (safe : Covers E shape w h)
    (point : Point shape w h leaf u middle remaining) : E middle u := by
  induction point with
  | entry=>exact safe.entry
  | returned shape performed=>exact safe.normal performed
  | left tail point ih=>exact ih safe.1
  | right head tail leading point ih=>exact ih (safe.2 _ _ _ leading)
  | marked label point ih=>exact ih safe

theorem covers_pure (value : α) (before : E h w) : Covers E (Shape.pure value) w h := before

theorem covers_atom (token : Atom α) (before : E h w)
    (normal : ∀ value u middle,runPrefix token.action w h=(.ok (value,u),middle) → E middle u) :
    Covers E (.atom token) w h := ⟨before,normal⟩

theorem covers_child (token : Child action) (before : E h w)
    (normal : ∀ value u middle,runPrefix action w h=(.ok (value,u),middle) → E middle u) :
    Covers E (.child token) w h := ⟨before,normal⟩

theorem covers_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    {head : Shape body} {tail : ∀ value,Shape (next value)}
    (first : Covers E head w h)
    (rest : ∀ value u middle,runPrefix body w h=(.ok (value,u),middle) → Covers E (tail value) u middle) :
    Covers E (.bind head tail) w h := ⟨first,rest⟩

theorem covers_marked (label : Label) (safe : Covers E shape w h) :
    Covers E (.marked label shape) w h := safe

theorem covers_type_cast {left right : PrefixM Event α}
    (types : Shape left=Shape right) (same : left=right) (shape : Shape left) :
    Covers E (cast types shape) w h=Covers E shape w h := by
  cases same
  rfl

theorem covers_cast {action other : PrefixM Event α} (equal : action=other)
    {shape : Shape other} (safe : Covers E shape w h) : Covers E (equal.symm ▸ shape) w h := by
  cases equal
  exact safe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
