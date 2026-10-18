import Leanux.Proofs.WG.HandshakeSecurity.ResponderReceiveFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationH1
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationLabels
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes

theorem identity_pool (w : WGWorld) (kid : KeypairId) :
    Confirmation.keyIdentityAt w kid = (pool w kid).map (·.allocation) := by
  cases device : w.dev <;> simp [Confirmation.keyIdentityAt, pool, Function.comp_def, keyCore, device]

theorem confirmedAt_identity (w : WGWorld) (kid : KeypairId) (accepted : Bool) :
    confirmedAt w kid accepted = (if accepted then Confirmation.keyIdentityAt w kid else none).toList := by
  cases accepted <;> cases device : w.dev <;>
    simp [confirmedAt, keyCoreAt, Confirmation.keyIdentityAt, Function.comp_def, keyCore, device]

theorem completedLabel_source (r : Queues.RxDisposition.ConsumeReceipt) :
    Confirmation.completedLabel r =
      (r.run.before.dev.bind fun d => d.peers[r.peer]?).bind (fun p =>
        if p.keypairNext == some r.packet.keypair then
          Confirmation.keyIdentityAt r.run.before r.packet.keypair else none) := by
  cases device : r.run.before.dev <;>
    simp [Confirmation.completedLabel, Confirmation.keyIdentityAt, device]

/-- The original endpoint write does not alter the optional allocation label,
and H1's native result/next-slot fact identifies the exact completed event label.
No initialized completeness premise or surviving key is needed here. -/
theorem completed_label_cut (H1 : H1ConfirmationEdges)
    (r : Queues.RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool)
    (cut : Confirmation.SourceCut r c) :
    (Confirmation.completedLabel r).toList = confirmedAt c.before r.packet.keypair c.value := by
  obtain ⟨before, after, beforeSlots, _, accepted, _, _, _⟩ :=
    H1 r.peer r.packet.keypair c.before c.after c.ambientBefore c.ambientAfter c.value cut.2.1
  have fields := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields)
      r.peer r.endpoint (CurrentSlots.fields r.run.before))
    _ _ _ _ _ rfl cut.1
  have fieldAt := congrFun (congrArg (fun fields => fields.2.1) fields) r.peer
  obtain ⟨peer, resident, shape⟩ := Option.map_eq_some_iff.mp beforeSlots
  have selected : ((c.before.dev.bind fun d => d.peers[r.peer]?).map CurrentSlots.slotCell) =
      some (before.current, before.previous, before.next) := by
    rw [resident, Option.map_some, ← shape]
    rfl
  have oldSelected : ((r.run.before.dev.bind fun d => d.peers[r.peer]?).map CurrentSlots.slotCell) =
      some (before.current, before.previous, before.next) := fieldAt.symm.trans selected
  obtain ⟨oldPeer, oldResident, oldShape⟩ := Option.map_eq_some_iff.mp oldSelected
  have next : oldPeer.keypairNext = before.next := congrArg (fun fields => fields.2.2) oldShape
  have material := (hoare_iff_run_ambient _ _ _).mp
    ((pool_of_material (Origins.Retaining.setPeerEndpoint_material r.peer r.endpoint)) (pool r.run.before))
    _ _ _ _ _ rfl cut.1
  have identity : Confirmation.keyIdentityAt c.before r.packet.keypair =
      Confirmation.keyIdentityAt r.run.before r.packet.keypair := by
    rw [identity_pool, identity_pool, material]
  rw [completedLabel_source, oldResident, Option.bind_some, next, confirmedAt_identity, identity]
  cases value : c.value with
  | true =>
    have yes := accepted.mp value
    simp [yes]
  | false =>
    have no : before.next ≠ some r.packet.keypair := by
      intro yes
      have impossible := accepted.mpr yes
      rw [value] at impossible
      cases impossible
    simp [no]

/-- A normal native consumer extends exactly campaign 1's existing completed
confirmation history while retaining responder-current authorization. -/
theorem completed_consumer_history (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (confirmed : List Nat) (r : Queues.RxDisposition.ConsumeReceipt) (valid : r.Valid)
    (entry : Authorized confirmed r.run.before) :
    Authorized (confirmed ++ (Confirmation.completedLabel r).toList) r.run.after := by
  obtain ⟨c, cut⟩ := Confirmation.completed_source_cut r valid
  rw [completed_label_cut slots r c cut]
  exact completed_consumer_authorized H1 confirmed r c cut entry

end Leanux.Proofs.WG.HandshakeSecurity.Responder
