import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingCreate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingChecked

/-! Actual submission derives the allocator's pending batch and immediately
feeds that same ledger and ownership to the complete prefix creation contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation

theorem with_fact {P : List Event→WGWorld→Ambient→Prop} {body : WGPrefix Event α}
    (rule : StateEnsures P CompleteProduct.Safe body (fun _=>P)) (fact : Prop) :
    StateEnsures (fun h w a=>P h w a ∧ fact) CompleteProduct.Safe body (fun _ h w a=>P h w a ∧ fact) := by
  intro w a h before
  obtain ⟨suffix,grown,safe,post⟩ := rule w a h ⟨before.1.1,before.2⟩
  refine ⟨suffix,grown,safe,?_⟩
  cases outcome : (runPrefix (body.run w) a h).1 with
  | error stop=>trivial
  | ok out=>
    rw [outcome] at post
    exact ⟨⟨post.1,before.1.2⟩,post.2⟩

theorem allocation_tail (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) :
    StateEnsures (fun h w a=>CompleteSelected.Ready ledger debts locals generation pid peer position h w a ∧
      BatchPayload.Shape pid kid peer.staged packets) CompleteProduct.Safe
      (do let items←state (Journal.allocate packets); CausalJournal.create pid items) (fun _=>Carrier debts locals) := by
  apply StateEnsures.bind (allocate ledger debts locals generation pid peer position kid packets)
  intro items w a h before
  obtain ⟨prior,receipt,_,_,_,_,_,_,accounted,pending⟩ := before.1
  exact Creation.create _ debts locals pid items w a h ⟨⟨accounted,pending⟩,before.2⟩

theorem submit (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) :
    StateEnsures (fun h w a=>CompleteSelected.Ready ledger debts locals generation pid peer position h w a ∧
      BatchPayload.Shape pid kid peer.staged packets) CompleteProduct.Safe
      (HeldSource.submit pid kid packets) (fun _=>Carrier debts locals) := by
  unfold HeldSource.submit
  apply StateEnsures.bind (with_fact (selected_native (CompleteSelected.world
    (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩)
    _ (fun initial=>indexOwner_peerDeref_preserves _ (fun w=>w=initial)))) _)
  intro owner
  exact StateEnsures.bind (with_fact (selected_native (CompleteSelected.acquire_peer
    (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) owner)) _)
    (fun _=>allocation_tail ledger debts locals generation pid peer position kid packets)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
