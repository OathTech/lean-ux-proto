import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateChecked

/-! Actual selected submission feeds its derived pending batch and paired
unpublished owner to the closed create contract. Preallocation failures retain
the selected frontier; no success premise is imposed on the enclosing call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal CompleteCarrier

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
    (packets : List DataPacket) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe
      (do let items ← state (Journal.allocate packets); CausalJournal.create pid items)
      (fun _ => Carrier debts locals) := by
  intro w a h before
  obtain ⟨items,v,performed,_,_,entry,pending⟩ := allocate before.1 before.2
  simp only [StateT.run_bind,runPrefix_bind]
  change runPrefix ((state (Journal.allocate packets)).run w) a h = _ at performed
  rw [performed]
  obtain ⟨suffix,extended,safe,post⟩ := CompleteCreate.checked (assignBatch position h.length ledger)
    debts locals pid items Safe accountSafe v a
    (h ++ [Event.old (.allocated packets ⟨items,w,v,a,a⟩)]) ⟨entry,pending⟩
  refine ⟨[Event.old (.allocated packets ⟨items,w,v,a,a⟩)] ++ suffix,?_,safe,post⟩
  simpa only [runStatePrefix,List.append_assoc] using extended

theorem submit (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) (Safe : List Event → Prop)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe
      (HeldSource.submit pid kid packets) (fun _ => Carrier debts locals) := by
  unfold HeldSource.submit
  apply StatePrefixEnsures.bind (with_shape
    (world frontier _ (fun initial => indexOwner_peerDeref_preserves _ (fun w => w = initial))) _)
  intro owner
  exact StatePrefixEnsures.bind (with_shape (acquire_peer frontier owner) _) (fun _ =>
    allocation_tail ledger debts locals generation pid peer position kid packets Safe accountSafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
