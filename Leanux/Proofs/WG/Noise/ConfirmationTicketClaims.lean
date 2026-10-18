import Leanux.Proofs.WG.Noise.CounterConsumeClaims
import Leanux.Proofs.WG.Noise.PendingTicketCallClaims
import Leanux.Proofs.WG.Noise.PendingTicketEndpointFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes ConsumeConfirmation

/-- Every committed initialized consume supplies the actual pending-ticket
transition, labelled by the resident allocation stamp on true confirmation. -/
theorem initialized_confirmation_transition (trace : Runner.Trace) (placeholders : Bool)
    (n id : Nat) (stamp : PacketStamp) (observation : ConfirmationObservation)
    (occurs : Occurs trace placeholders n id stamp observation) :
    ∃ allocation,
      projectedStampAt observation.entry observation.packet.keypair = some allocation ∧
      PendingTickets.Step (PendingTickets.projected observation.entry)
        (if observation.confirmed then some allocation else none)
        (PendingTickets.projected observation.after) := by
  obtain ⟨pre,post,r,c,position,rfl,rv,endpoint,confirm,tail⟩ := occurs
  have valid : (projects r c).Valid := ⟨r,c,rfl,rv,endpoint,confirm,tail⟩
  obtain ⟨allocation,resident⟩ := initialized_consumed_stamp trace placeholders
    pre post n id stamp r position
  obtain ⟨d,p,before,read,final,hd,hp,hb,hr,slots,stamps,hf,effect,matched⟩ :=
    observation_valid_facts (projects r c) valid
  change c.before.dev = some before at hb
  have beforeStamp : (before.keypairs[r.packet.keypair]?).map Keypair.internalId = some allocation := by
    simpa only [projectedStampAt,projects,Campaign2.snapshot,Campaign2.core,hb,
      Option.bind_some] using stamps.trans resident
  obtain ⟨key,hkey,hstamp⟩ := Option.map_eq_some_iff.mp beforeStamp
  have step := PendingTickets.receivedWithKeypair_step r.peer r.packet.keypair
    c.before.keypairCounter before read key hr hkey c.before c.ambientBefore c.value
    c.after c.ambientAfter ⟨hb,rfl⟩ confirm
  have entrySame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PendingTickets.setPeerEndpoint_frame r.peer r.endpoint)
    r.run.before r.run.ambientBefore () c.before c.ambientBefore endpoint
  have start : PendingTickets.deviceView c.before.keypairCounter before = PendingTickets.view c.before := by
    simp [PendingTickets.deviceView,PendingTickets.view,hb]
  rw [start,entrySame,hstamp] at step
  exact ⟨allocation,resident,step⟩

/-- The actual initialized occurrence preserves a supplied pending-history
invariant and extends it exactly on successful confirmation. -/
theorem initialized_confirmation_history (trace : Runner.Trace) (placeholders : Bool)
    (n id : Nat) (stamp : PacketStamp) (observation : ConfirmationObservation)
    (occurs : Occurs trace placeholders n id stamp observation)
    (seen : List Nat) (history : PendingTickets.Inv (PendingTickets.projected observation.entry) seen) :
    ∃ allocation,
      projectedStampAt observation.entry observation.packet.keypair = some allocation ∧
      PendingTickets.Inv (PendingTickets.projected observation.after)
        (if observation.confirmed then allocation :: seen else seen) := by
  obtain ⟨allocation,resident,step⟩ :=
    initialized_confirmation_transition trace placeholders n id stamp observation occurs
  have next := step.preserves history
  refine ⟨allocation,resident,?_⟩
  cases choice : observation.confirmed <;> simpa [choice,PendingTickets.record] using next

end Leanux.Proofs.WG.Noise.CounterConsume
