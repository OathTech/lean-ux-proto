import Leanux.Proofs.WG.Roaming.PublicationFrames
import Leanux.Proofs.WG.Roaming.PublicationReadFrames
import Leanux.WG.PrevQueue

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Whole-WireGuard variant of campaign 1's PrevQueue_peek_spec and
PrevQueue_peek_sameSnapshot. The native WG.M type still admits writes to
receive-packet storage, so this preservation remains substantive. -/
theorem PrevQueue_peek_spec_wg_variant {α : Type} (q : PrevQueue α) (P : WGWorld → Prop) :
    ⦃fun g => ⌜P g⌝⦄ q.peek ⦃⇓? _ g => ⌜P g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases peeked : q.peeked with
  | some item =>
    simp [PrevQueue.peek, peeked, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | none =>
    cases stub : q.tailIsStub <;> cases items : q.items with
    | nil =>
      simp [PrevQueue.peek, PrevQueue.dequeue, peeked, stub, items,
        branch, AmbientM.branch, invariant, AmbientM.invariant] at run
      all_goals cases run
      all_goals exact pre
    | cons item rest =>
      cases rest <;>
        simp [PrevQueue.peek, PrevQueue.dequeue, peeked, stub, items,
          branch, AmbientM.branch] at run
      all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals exact pre

theorem read_get : Campaign2.Product.read = (do
    let w ← get
    pure (Campaign2.Product.snapshot w)) := rfl

/-- Read provenance and preservation for the original product packet observation. -/
theorem getRxSkb_packet (id : SkbId) (entry : Campaign2.Product.Snapshot) :
    ⦃fun w => ⌜∀ id, packetAt (Campaign2.Product.snapshot w) id = packetAt entry id⌝⦄
      liftWG (getRxSkb id)
    ⦃⇓? packet w => ⌜(∀ id, packetAt (Campaign2.Product.snapshot w) id = packetAt entry id) ∧
      packetAt entry id = some packet⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w packet final pre run
  obtain ⟨same, resident⟩ := getRxSkb_read id w w packet final rfl run
  subst final
  exact ⟨pre, (pre id).symm.trans resident⟩

end Leanux.Proofs.WG.Roaming
