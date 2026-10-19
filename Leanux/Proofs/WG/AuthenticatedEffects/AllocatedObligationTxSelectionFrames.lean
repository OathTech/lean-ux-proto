import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryFrames

/-! The native TX queue peek changes only its representation; the native
remove transfers one exact cached batch into a selected caller local. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

private theorem queue_views (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (queue : PrevQueue (List SkbId)) :
    let v := replacePeer w d pid {p with txQueue := queue}
    Packets.epoch v = Packets.epoch w ∧ Staged.stagedAt v = Staged.stagedAt w ∧
    PacketMaterial.view v = PacketMaterial.view w ∧ Packets.snapshot v = Packets.snapshot w ∧
    TxDisposition.txPackets v = TxDisposition.txPackets w := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [Packets.epoch,replacePeer,device]
  · funext other
    by_cases same : pid = other
    · subst other
      simp [Staged.stagedAt,replacePeer,device,found]
    · simp [Staged.stagedAt,replacePeer,device,Std.TreeMap.getElem?_insert,same]
  · funext id
    simp [PacketMaterial.view,TxDisposition.txPackets,replacePeer,device]
  · simp [Packets.snapshot,Packets.deviceStore,replacePeer,device]
  · funext id
    simp [TxDisposition.txPackets,replacePeer,device]

/-- A successful original remove preserves the same fixed ledger and native
packet cells while transferring the exact cached queue batch to a local. -/
theorem drop_native (pid : PeerId) (a b : Ambient)
    (before : StagedEntry.Inv history ledger debts locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = some items)
    (performed : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    StagedEntry.Inv history ledger debts (⟨.selected,pid,items⟩ :: locals) v := by
  obtain ⟨d,p,device,found,_,after⟩ := txDrop_effect pid a b performed
  have peeked := cached p (by simp [peerAt,device,found])
  rw [after]
  obtain ⟨epoch,staged,material,snapshot,_⟩ := queue_views device found p.txQueue.dropPeeked
  have core := before.core.quiet_views [] (by simp) epoch staged material
  refine ⟨by simpa only [List.append_nil] using core,before.justified,before.allocationLinks,
    before.noSelected,?_,before.coverage.drop device found peeked,before.inventory.drop device found peeked⟩
  simpa only [Packets.Inv,snapshot] using before.packets

/-- Original queue peek retains full Entry. At an idle boundary with no
cleanup debts, its actual selected batch is backed by pending fixed tickets. -/
theorem peek_native (pid : PeerId) (a b : Ambient)
    (before : StagedEntry.Inv history ledger [] locals w)
    (performed : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    StagedEntry.Inv history ledger [] locals v ∧
    (∀ p, peerAt v pid = some p → p.txQueue.peeked = first) ∧
    (∀ items, first = some items → PendingBatch history ledger items) := by
  obtain ⟨d,p,queue,device,found,contents,cached,after⟩ := txPeek_effect pid a b performed
  have views := queue_views device found queue
  rw [after]
  obtain ⟨epoch,staged,material,snapshot,packets⟩ := views
  have queues : txQueueContents (replacePeer w d pid {p with txQueue := queue}) = txQueueContents w := by
    funext other
    by_cases same : pid = other
    · subst other
      simp [txQueueContents,RxCredits.handoffTxView,replacePeer,device,found,contents]
    · simp [txQueueContents,RxCredits.handoffTxView,replacePeer,device,Std.TreeMap.getElem?_insert,same]
  have entry : StagedEntry.Inv history ledger [] locals (replacePeer w d pid {p with txQueue := queue}) := by
    simpa only [List.append_nil] using before.views [] (by simp) epoch staged material snapshot packets queues
  refine ⟨entry,?_,?_⟩
  · intro current resident
    have same : current = {p with txQueue := queue} := by
      simpa [peerAt,replacePeer] using resident.symm
    subst current
    exact cached
  · intro items selected
    apply DeadEntry.queued_pending (pid := pid) entry (peer := {p with txQueue := queue})
    · simp [peerAt,replacePeer]
    · simp [PrevQueue.all,cached,selected]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
