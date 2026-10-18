import Leanux.Proofs.WG.Noise.PendingTicketCallClaims
import Leanux.Proofs.WG.Noise.PendingTicketEndpointFrames
import Leanux.Proofs.WG.Noise.CounterConsumeClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged

/-- Data-only label reconstructed from the actual entry. A matching pending
numeric slot whose key has disappeared supplies no allocation stamp. -/
def confirmationInputLabel (entry : Campaign2.Snapshot) (pid received : Nat) : Option Nat := do
  let d ← entry.wg.device
  let p ← d.peers[pid]?
  if p.keypairNext == some received then
    (d.keypairs[received]?).map Keypair.internalId
  else none

theorem confirmation_optional_step (pid received : Nat) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun s => s = entry)
      (fun ok final => Step (projected entry)
        (if ok then (projected entry).slots pid else none) (projected final)) := by
  intro g ambient ok final after pre run
  subst entry
  cases device : g.dev with
  | none =>
    simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have step := receivedWithKeypair_step_optional pid received g.keypairCounter d p peer
        g ambient ok final after ⟨device,rfl⟩ run
      simpa [projected,Campaign2.snapshot,Campaign2.core,deviceView,view,device] using step

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes PendingTickets

theorem input_label_actual (o : ConfirmationObservation) (valid : o.Valid) :
    confirmationInputLabel o.entry o.peer o.packet.keypair =
      if o.confirmed then projectedStampAt o.entry o.packet.keypair else none := by
  obtain ⟨d,p,before,read,final,hd,hp,hb,hr,slots,stamps,hf,effect,matched⟩ :=
    observation_valid_facts o valid
  cases confirmed : o.confirmed with
  | false =>
    have different : p.keypairNext ≠ some o.packet.keypair := by
      intro equal
      have yes := matched.mpr equal
      rw [confirmed] at yes
      cases yes
    simp [confirmationInputLabel,hd,hp,different]
  | true =>
    have equal := matched.mp confirmed
    simp [confirmationInputLabel,projectedStampAt,hd,hp,equal]

theorem input_label_pending (o : ConfirmationObservation) (valid : o.Valid) :
    confirmationInputLabel o.entry o.peer o.packet.keypair =
      if o.confirmed then (projected o.entry).slots o.peer else none := by
  obtain ⟨d,p,before,read,final,hd,hp,hb,hr,slots,stamps,hf,effect,matched⟩ :=
    observation_valid_facts o valid
  rw [input_label_actual o valid]
  cases confirmed : o.confirmed with
  | false => rfl
  | true =>
    have equal := matched.mp confirmed
    simp [projected,pending,projectedStampAt,hd,hp,equal]
    cases d.keypairs[o.packet.keypair]? <;> rfl

/-- The entry label comes from the same original nested confirmation call.
The endpoint prefix is a pending-view frame; no later caller state is inferred. -/
theorem observation_optional_transition (o : ConfirmationObservation) (valid : o.Valid) :
    PendingTickets.Step (projected o.entry) (confirmationInputLabel o.entry o.peer o.packet.keypair)
      (projected o.after) := by
  obtain ⟨r,c,rfl,rv,endpoint,confirm,tail⟩ := valid
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (setPeerEndpoint_frame r.peer r.endpoint)
    r.run.before r.run.ambientBefore () c.before c.ambientBefore endpoint
  have step := confirmation_optional_step r.peer r.packet.keypair
    (Campaign2.snapshot c.before c.ambientBefore)
    c.before c.ambientBefore c.value c.after c.ambientAfter rfl confirm
  have start : projected (Campaign2.snapshot c.before c.ambientBefore) =
      projected (Campaign2.snapshot r.run.before r.run.ambientBefore) := same
  rw [start] at step
  have label := input_label_pending (projects r c) ⟨r,c,rfl,rv,endpoint,confirm,tail⟩
  rw [label]
  exact step

end Leanux.Proofs.WG.Noise.ConsumeConfirmation

namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation PendingTickets

/-- Every committed initialized true confirmation contributes its actual
resident allocation stamp; no true occurrence is lost by the optional local label. -/
theorem initialized_label_complete (trace : Runner.Trace) (placeholders : Bool)
    (n id : Nat) (stamp : PacketStamp) (o : ConfirmationObservation)
    (occurs : Occurs trace placeholders n id stamp o) :
    ∃ allocation, projectedStampAt o.entry o.packet.keypair = some allocation ∧
      confirmationInputLabel o.entry o.peer o.packet.keypair =
        (if o.confirmed then some allocation else none) ∧
      (confirmationInputLabel o.entry o.peer o.packet.keypair = some allocation ↔ o.confirmed = true) := by
  obtain ⟨valid,_,allocation,resident,_⟩ :=
    initialized_confirmation_stamped trace placeholders n id stamp o occurs
  have label := input_label_actual o valid
  rw [resident] at label
  refine ⟨allocation,resident,label,?_⟩
  rw [label]
  cases o.confirmed <;> simp

end Leanux.Proofs.WG.Noise.CounterConsume
