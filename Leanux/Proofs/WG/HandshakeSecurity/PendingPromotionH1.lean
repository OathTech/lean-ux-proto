import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionProjection

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

/-- Local operational consequences required from C2 H1 at pin
`be8c209c`.

`session` is the projection of `Noise.PendingTickets.session_step` and its
`Step` preservation lemmas, with `NextBounds` obtained from C1 `CurrentSlots`.
`confirmation` is `Noise.PendingTickets.confirmation_step` when the received
cell is resident; the no-cell branch additionally needs retention from
`Noise.receivedWithKeypair_effect`. `clear` is the pending-slot projection of
`Noise.keypairsClear_effect`. These fields are native single-call facts only.
No initialized uniqueness or history transport is assumed. -/
structure H1PendingPromotionEdges : Prop where
  session : ∀ (pid : PeerId) (r : WGRunWitness Bool),
    CurrentSlots.Inv r.before → Bounded (PendingPromotion.view r.before) →
    Unique (PendingPromotion.view r.before) → r.Valid (beginSession pid) →
    Transition (PendingPromotion.view r.before) (PendingPromotion.view r.after) ∧
      Bounded (PendingPromotion.view r.after) ∧ Unique (PendingPromotion.view r.after)
  confirmation : ∀ (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool),
    r.Valid (receivedWithKeypair pid kid) →
    match PendingPromotion.label kid r with
    | none => Retained (PendingPromotion.view r.before) (PendingPromotion.view r.after)
    | some stamp => (PendingPromotion.view r.before).slots pid = some stamp ∧
        Retained ((PendingPromotion.view r.before).put pid none) (PendingPromotion.view r.after)
  clear : ∀ (pid : PeerId) (r : WGRunWitness Unit),
    r.Valid (keypairsClear pid) →
    Retained (PendingPromotion.view r.before) (PendingPromotion.view r.after)

namespace PendingPromotion

theorem session (H1 : H1PendingPromotionEdges) (pid : PeerId) (r : WGRunWitness Bool)
    (hi : Inv confirmed r.before) (slots : CurrentSlots.Inv r.before)
    (valid : r.Valid (beginSession pid)) : Inv confirmed r.after := by
  obtain ⟨step,bounded,unique⟩ := H1.session pid r slots hi.bounded hi.unique valid
  exact hi.advanced step bounded unique

/-- A successful inner confirmation extends a supplied pending-history
invariant immediately; a later caller Stop cannot defer its freshness check. -/
theorem confirmation (H1 : H1PendingPromotionEdges) (pid : PeerId) (kid : KeypairId)
    (r : WGRunWitness Bool) (hi : Inv confirmed r.before)
    (valid : r.Valid (receivedWithKeypair pid kid)) :
    Inv (confirmed ++ (label kid r).toList) r.after := by
  have step := H1.confirmation pid kid r valid
  cases found : label kid r with
  | none => simpa only [found,Option.toList_none,List.append_nil] using
      hi.retained (by simpa only [found] using step)
  | some stamp =>
    have effect : (view r.before).slots pid = some stamp ∧
        Retained ((view r.before).put pid none) (view r.after) := by
      simpa only [found] using step
    simpa only [found,Option.toList_some] using hi.confirmed pid stamp effect.1 effect.2

theorem clear (H1 : H1PendingPromotionEdges) (pid : PeerId) (r : WGRunWitness Unit)
    (hi : Inv confirmed r.before) (valid : r.Valid (keypairsClear pid)) :
    Inv confirmed r.after := hi.retained (H1.clear pid r valid)

end PendingPromotion
end Leanux.Proofs.WG.HandshakeSecurity
