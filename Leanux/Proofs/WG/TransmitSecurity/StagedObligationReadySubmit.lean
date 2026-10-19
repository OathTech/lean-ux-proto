import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyAllocation

/-! Actual owner lookup, peer borrowing and allocation feed the create callback
with the whole entry bundle at the same native cut. Failure before allocation
retains selected ownership; allocation is total under the carried entry. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation

private theorem with_shape {Safe : List Event → Prop}
    (rule : StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe action)
    (fact : Prop) :
    StatePrefixPreserves (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧ fact)
      Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,safe,post⟩ := rule w a h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases result : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using post,before.2⟩

theorem allocation_tail (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) (Safe : List Event → Prop) (Post : List Event → WGWorld → Ambient → Prop)
    (created : ∀ after items, StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h after debts (⟨.unpublished,pid,items⟩ :: locals) w)
      Safe (CausalJournal.create pid items) (fun _ => Post)) :
    StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe
      (do let items ← state (Journal.allocate packets); CausalJournal.create pid items) (fun _ => Post) := by
  intro w a h before
  obtain ⟨items,v,performed,_,_,entry⟩ := allocate before.1 before.2
  simp only [StateT.run_bind,runPrefix_bind]
  change runPrefix ((state (Journal.allocate packets)).run w) a h = _ at performed
  rw [performed]
  obtain ⟨suffix,extended,safe,post⟩ := created (assignBatch position h.length ledger) items v a
    (h ++ [Event.old (.allocated packets ⟨items,w,v,a,a⟩)]) entry
  refine ⟨[Event.old (.allocated packets ⟨items,w,v,a,a⟩)] ++ suffix,?_,safe,post⟩
  simpa only [runStatePrefix,List.append_assoc] using extended

/-- The real staged submission obtains allocation preconditions from the
selected nonce traversal. Its sole remaining callback is actual createData
observed on the complete unpublished entry; preallocation Stop keeps the
selected frontier, and no allocation-success premise is supplied. -/
theorem submit (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) (Safe : List Event → Prop)
    (frontier : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop)
    (created : ∀ after items, StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h after debts (⟨.unpublished,pid,items⟩ :: locals) w)
      Safe (CausalJournal.create pid items) (fun _ => Post)) :
    StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (HeldSource.submit pid kid packets) (fun _ => Post) := by
  unfold HeldSource.submit
  apply StatePrefixEnsures.bind (with_shape
    (world frontier _ (fun initial => indexOwner_peerDeref_preserves _ (fun w => w = initial))) _)
  intro owner
  exact StatePrefixEnsures.bind (with_shape (acquire_peer frontier owner) _) (fun _ =>
    allocation_tail ledger debts locals generation pid peer position kid packets Safe Post created)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
