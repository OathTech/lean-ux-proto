import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointCoverage

/-! Child-free NAPI source witnesses justify omitting a child contract by
their actual syntax. A native point cannot hide a packet-processing child
behind an empty relation: the source itself must prove it has no such node. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

def Shape.ChildFree : {α : Type} → {action : PrefixM Event α} → Shape action → Prop
  | _,_,.pure _=>True
  | _,_,.native _=>True
  | _,_,.child _=>False
  | _,_,.failed _ _=>True
  | _,_,.bind head tail=>head.ChildFree ∧ ∀value,(tail value).ChildFree
  | _,_,.marked _ shape=>shape.ChildFree

theorem Point.childFree (free : shape.ChildFree)
    (point : Point inside shape w h site u middle) : Point Boundary shape w h site u middle := by
  induction point with
  | entry shape=>exact .entry shape
  | returned shape performed=>exact .returned shape performed
  | interior token point=>exact False.elim free
  | metadata point => exact .metadata point
  | rx point => exact .rx point
  | free point => exact .free point
  | left tail point ih=>exact .left tail (ih free.1)
  | right head tail leading point ih=>exact .right head tail leading (ih (free.2 _))
  | marked label point ih=>exact .marked label (ih free)

theorem Point.childFree_remaining {α : Type} {action : PrefixM Event α} {shape : Shape action}
    (free : shape.ChildFree) (point : Point inside shape w h site u middle) :
    ∃remaining,runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry shape=>exact ⟨_,rfl⟩
  | returned shape performed=>exact ⟨pure _,performed⟩
  | interior token point=>exact False.elim free
  | metadata point => exact ⟨_,metadataRemainder_run _ point⟩
  | rx point => exact ⟨_,rxRemainder_run _ point⟩
  | free point => exact ⟨_,freeRemainder_run _ point⟩
  | left tail point ih=>
    rename_i body next head
    obtain ⟨remaining,same⟩:=ih free.1
    exact ⟨remaining >>= next,by simp only [runPrefix_bind,same]⟩
  | right head tail leading point ih=>
    obtain ⟨remaining,same⟩:=ih (free.2 _)
    exact ⟨remaining,by rw [runPrefix_bind,leading];exact same⟩
  | marked label point ih=>exact ih free

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
