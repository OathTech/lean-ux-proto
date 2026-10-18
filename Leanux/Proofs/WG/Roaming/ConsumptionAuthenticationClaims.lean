import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes Noise.ConsumeConfirmation Noise.ConfirmationOrder

/-- Every completed data consume in the exact initialized receive history,
including normal nondelivery and receipts retained before a later Stop. -/
theorem initialized_consumptions_authenticated (trace : Runner.Trace) (placeholders : Bool) :
    ∃ qs,
      observations trace placeholders = .ok qs ∧
      qs.Pairwise (fun a b => a.position < b.position) ∧
      qs.length = consumedCount (history trace placeholders) ∧
      (∀ q, q ∈ qs ↔ OccursAt trace placeholders q) ∧
      ∀ q ∈ qs, ∃ e : ConsumptionAuthentication, e.Valid trace placeholders q ∧ e.Facts q := by
  obtain ⟨qs,run,ids,ordered,count,complete,facts⟩ := initialized_complete trace placeholders
  exact ⟨qs,run,ordered,count,complete,fun q member =>
    consumption_authenticated trace placeholders q ((complete q).mp member)⟩

end Leanux.Proofs.WG.Roaming
