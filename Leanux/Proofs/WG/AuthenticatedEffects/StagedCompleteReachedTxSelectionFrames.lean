import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakeComposition

/-! Selection frames preserve the same complete ledger across actual peek,
readiness and packet reads, then transfer the queue occurrence to a local
owner at the native dequeue. No callback outcome is needed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CompleteCarrier AllocatedObligation CompletionBatch
open StagedTerminalComplete

theorem peek (before : Accounted h ledger [] locals w.wg)
    (performed : runPrefix (TxSelection.peek pid) w h=(.ok (first,u),middle)) :
    Accounted middle ledger [] locals u.wg ∧
      (∀p,peerAt u.wg pid=some p → p.txQueue.peeked=first) := by
  have complete:=Converse.peek_complete pid before.complete w
  rw [performed] at complete
  obtain ⟨entry,cached,_⟩:=TxSelection.peek_entry pid before.entry performed
  exact ⟨⟨entry,complete⟩,cached⟩

theorem ready (before : Accounted h ledger [] locals w.wg)
    (performed : runPrefix (TxWorker.ready first) w h=(.ok (go,u),middle)) :
    Accounted middle ledger [] locals u.wg ∧ u.wg=w.wg ∧
      (go=true → ∃items id packet,first=some items ∧ items.head?=some id ∧
        TxDisposition.txPackets w.wg id=some packet ∧ packet.state≠.uncrypted) := by
  have complete:=Converse.ready_complete first before.complete w
  rw [performed] at complete
  obtain ⟨entry,same,shape⟩:=TxWorker.ready_entry first before.entry performed
  exact ⟨⟨entry,complete⟩,same,shape⟩

theorem packet {id : SkbId} (before : Accounted h ledger [] locals w.wg)
    (performed : runPrefix (CausalJournal.completionOps.packet id) w h=(.ok (value,u),middle)) :
    Accounted middle ledger [] locals u.wg ∧ u.wg=w.wg := by
  have complete : Complete (runPrefix (CausalJournal.completionOps.packet id) w h).2 ledger :=
    Converse.focused_access_complete before.complete (getTxSkbPrefix id) w
  rw [performed] at complete
  obtain ⟨entry,same,_⟩:=TxWorker.packet_entry id before.entry performed
  exact ⟨⟨entry,complete⟩,same⟩

theorem drop (before : Accounted h ledger [] locals w.wg)
    (cached : ∀p,peerAt w.wg pid=some p → p.txQueue.peeked=some items)
    (performed : runPrefix (CausalJournal.completionOps.drop pid items) w h=(.ok ((),u),middle)) :
    Accounted middle ledger [] (⟨.selected,pid,items⟩::locals) u.wg ∧
      CreateDisposal.PendingBatch middle ledger items := by
  have complete:=Converse.drop_complete pid items before.complete w
  rw [performed] at complete
  obtain ⟨entry,pending⟩:=TxSelection.drop_entry pid items before.entry cached performed
  exact ⟨⟨entry,complete⟩,pending⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
