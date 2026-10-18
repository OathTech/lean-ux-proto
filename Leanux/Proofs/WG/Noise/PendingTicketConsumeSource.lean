import Leanux.Proofs.WG.Noise.PendingTicketConsumeFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues PendingTickets

/-- The same completed consume carries its actual optional confirmation ticket
through the entire later tail, including a normal packet-drop return. -/
theorem completed_optional_transition (o : ConfirmationObservation) (valid : o.Valid) :
    PendingTickets.Step (projected o.entry)
      (confirmationInputLabel o.entry o.peer o.packet.keypair) (projected o.finish) := by
  have first := observation_optional_transition o valid
  have last : Retained (projected o.after) (projected o.finish) := by
    obtain ⟨r,c,rfl,rv,endpoint,confirm,tail⟩ := valid
    exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (afterConfirmation_retained r.peer r.packet c.value)
      c.after c.ambientAfter r.run.value r.run.after r.run.ambientAfter tail
  exact first.retained_after last

theorem receipt_optional_step (r : RxDisposition.ConsumeReceipt) (valid : r.Valid) :
    PendingTickets.Step (view r.run.before) (CounterConsume.receiptLabel r) (view r.run.after) := by
  obtain ⟨c,endpoint,confirm,tail,_⟩ := receipt_observation r valid
  exact completed_optional_transition (projects r c) ⟨r,c,rfl,valid,endpoint,confirm,tail⟩

end Leanux.Proofs.WG.Noise.ConsumeConfirmation
