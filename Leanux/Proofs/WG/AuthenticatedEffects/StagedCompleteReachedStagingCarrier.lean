import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingFrames

/-! The exact guarded prefix derives submission shape and retains the same
selected native carrier. Stopped runs retain the selected receipt anchor;
their actual failed prefix is exposed separately by the caller certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteSelected

def Matches (pid : PeerId) (packets : List Packet) : Decision→Prop
  | .submit kid batch=>BatchPayload.Shape pid kid packets batch
  | _=>True

theorem walk_checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId)
    (peer : Peer) (position : Nat) (kid : KeypairId) (remaining seen : List Packet)
    (packets : List DataPacket) :
    StatePrefixEnsures
      (fun h w a=>Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid seen packets)
      (CompleteSelected.Active ledger debts generation pid peer position)
      (walkWith liftWGPrefix (fun key=>state (Journal.reserve key)) pid kid remaining packets)
      (fun decision h w a=>Ready ledger debts locals generation pid peer position h w a ∧
        Matches pid (seen++remaining) decision) := by
  induction remaining generalizing seen packets with
  | nil=>
    unfold walkWith
    apply StatePrefixEnsures.bind (with_fact (ambient (fun _=>id) _) _)
    intro _
    apply StatePrefixEnsures.pure _ (fun _ _ _ before=>before.1.active)
    intro h w a before
    exact ⟨before.1,by simpa only [Matches,List.append_nil] using before.2⟩
  | cons packet rest ih=>
    unfold walkWith
    apply StatePrefixEnsures.bind (with_fact (ambient (fun _=>id) _) _)
    intro _
    apply StatePrefixEnsures.bind (with_fact (world (fun _=>id) _ (ipTunnelEcnEncap_sameWGWorld packet)) _)
    intro ds
    apply StatePrefixEnsures.bind (with_fact (reserve (fun _=>id) kid) _)
    intro nonce
    apply StatePrefixEnsures.bind (with_fact (ambient (fun _=>id) _) _)
    intro over
    cases over with
    | true=>
      apply StatePrefixEnsures.pure _ (fun _ _ _ before=>before.1.active)
      exact fun _ _ _ before=>⟨before.1,True.intro⟩
    | false=>
      apply StatePrefixEnsures.consequence (ih (seen++[packet]) _)
      · exact fun _ _ _ before=>⟨before.1,shape_snoc before.2 packet nonce ds⟩
      · intro decision h w a after
        simpa only [List.append_assoc,List.singleton_append] using after

theorem prefix_checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId)
    (peer : Peer) (position : Nat) (keypair : Option KeypairId) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position)
      (CompleteSelected.Active ledger debts generation pid peer position) (checkedPrefix pid peer keypair)
      (fun decision h w a=>Ready ledger debts locals generation pid peer position h w a ∧
        Matches pid peer.staged decision) := by
  unfold checkedPrefix prefixWith
  apply StatePrefixEnsures.bind (ambient (fun _=>id) _)
  intro missing
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.active)
      (fun _ _ _ before=>⟨before,True.intro⟩)
  · cases keypair with
    | none=>
      exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.active)
        (fun _ _ _ before=>⟨before,True.intro⟩)
    | some kid=>
      apply StatePrefixEnsures.bind (read_key (fun _=>id) kid)
      intro key
      apply StatePrefixEnsures.bind (ambient (fun _=>id) _)
      intro invalid
      split
      · exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.active)
          (fun _ _ _ before=>⟨before,True.intro⟩)
      · apply StatePrefixEnsures.bind (world (fun _=>id) _ (branchExpired_sameWGWorld _ _ _ _))
        intro expired
        split
        · exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.active)
            (fun _ _ _ before=>⟨before,True.intro⟩)
        · apply StatePrefixEnsures.consequence
            (walk_checked ledger debts locals generation pid peer position kid peer.staged [] [])
          · intro h w a before
            exact ⟨before,rfl,by intro packet member; cases member⟩
          · intro decision h w a after
            simpa only [List.nil_append] using after

theorem allocation_checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId)
    (peer : Peer) (position : Nat) (keypair : Option KeypairId) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position)
      (CompleteSelected.Active ledger debts generation pid peer position) (allocationPrefix pid peer keypair)
      (fun decision h w a=>Ready ledger debts locals generation pid peer position h w a ∧
        Matches pid peer.staged decision) := by
  unfold allocationPrefix
  apply StatePrefixEnsures.bind (prefix_checked ledger debts locals generation pid peer position keypair)
  intro decision
  cases decision with
  | rejected kp invalid=>
    exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.1.active)
      (fun _ _ _ before=>before)
  | unreachable=>
    exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.1.active)
      (fun _ _ _ before=>before)
  | submit kid packets=>
    apply StatePrefixEnsures.bind (with_fact
      (world (fun _=>id) _ (fun initial=>indexOwner_peerDeref_preserves _ (fun w=>w=initial))) _)
    intro owner
    apply StatePrefixEnsures.bind (with_fact (acquire_peer (fun _=>id) owner) _)
    intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ before=>before.1.active) (fun _ _ _ before=>before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
