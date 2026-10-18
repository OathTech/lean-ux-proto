import Leanux.Proofs.WG.Noise.PendingTicketConsumeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Leanux Leanux.WG Lifetimes PendingTickets

theorem completed_optional_history (o : ConfirmationObservation) (valid : o.Valid)
    (seen : List Nat) (initial : Inv (projected o.entry) seen) :
    Inv (projected o.finish)
      (record (confirmationInputLabel o.entry o.peer o.packet.keypair) seen) :=
  (completed_optional_transition o valid).preserves initial

end Leanux.Proofs.WG.Noise.ConsumeConfirmation

namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

/-- Whole original consume on every normal outcome, with its entry-selected
ticket; no successful inner-call or local key-residency premise is supplied. -/
theorem consume_optional_step (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint) (fun s => s = entry)
      (fun _ final => Step (projected entry) (confirmationInputLabel entry pid pkt.keypair)
        (projected final)) := by
  intro g ambient value final after pre run
  subst entry
  exact ConsumeConfirmation.receipt_optional_step
    ⟨pid,pkt,endpoint,⟨value,g,final,ambient,after⟩⟩ run

theorem consume_optional_history (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (entry : Campaign2.Snapshot) (seen : List Nat) (initial : Inv (projected entry) seen) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint) (fun s => s = entry)
      (fun _ final => Inv (projected final)
        (record (confirmationInputLabel entry pid pkt.keypair) seen)) := by
  intro g ambient value final after pre run
  exact (consume_optional_step pid pkt endpoint entry
    g ambient value final after pre run).preserves initial

end Leanux.Proofs.WG.Noise.PendingTickets
