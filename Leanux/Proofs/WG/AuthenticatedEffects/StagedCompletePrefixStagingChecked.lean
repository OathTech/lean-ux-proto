import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingFrames

/-! The original nonce loop is reused with the logical prefix certificate in
its carrier. Its consuming callbacks must supply their own prefix contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal

set_option maxHeartbeats 600000

theorem checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId)
    (peer : Peer) (position : Nat) (keypair : Option KeypairId)
    (Post : List Event→WGWorld→Ambient→Prop)
    (noKey : Option KeypairId→Bool→WGPrefix Event Unit)
    (submit : KeypairId→List DataPacket→WGPrefix Event Unit)
    (rejected : ∀ kp invalid,
      StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
        CompleteProduct.Safe (noKey kp invalid) (fun _=>Post))
    (submitted : ∀ kid packets,
      StateEnsures (fun h w a=>CompleteSelected.Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets)
        CompleteProduct.Safe (submit kid packets) (fun _=>Post)) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid=>state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _=>Post) := by
  apply CheckedCarrier.checked
    (WithState (CompleteSelected.Ready ledger debts locals generation pid peer position) CompleteProduct.Safe)
    pid peer keypair (All CompleteProduct.Safe) (fun _ _ _ before=>before.2)
  · intro α action
    exact selected_native (CompleteSelected.ambient
      (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) action)
  · intro α action same
    exact selected_native (CompleteSelected.world
      (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) action same)
  · intro kid
    exact selected_native (CompleteSelected.read_key
      (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) kid)
  · exact reserve
  · exact fun _ _ _ before=>before.2
  · exact rejected
  · intro kid packets
    apply StatePrefixEnsures.consequence (submitted kid packets)
    · intro h w a before
      exact ⟨⟨before.1.1,before.2⟩,before.1.2⟩
    · exact fun _ _ _ _ after=>after

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
