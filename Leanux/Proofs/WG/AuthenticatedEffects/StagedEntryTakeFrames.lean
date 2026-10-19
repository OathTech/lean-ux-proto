import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOwnershipFrames

/-! Taking staged plaintexts changes no allocated TX cell or owning TX queue.
The cached peer is the exact native read, including its allocation stamp.
Missing peers stop at that read; an empty staged queue is a normal idle return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TakeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Obligations
open RetirementSecurity RetirementSecurity.StagingOccurrences Queues.RxCredits
open HandshakeSecurity.StagedConservation

abbrev ownership := StagedAdmission.Front.Ownership.view

theorem native (r : Take.Receipt) (valid : r.Valid) : ownership r.run.after = ownership r.run.before := by
  cases result : r.run.value with
  | none =>
    have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
        .ok ((none,r.run.after),r.run.ambientAfter) := by rw [←result]; exact valid
    obtain ⟨_,_,_,_,_,same,_⟩ := Take.take_none _ _ _ _ _ run
    rw [same]
  | some peer =>
    have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
        .ok ((some peer,r.run.after),r.run.ambientAfter) := by rw [←result]; exact valid
    obtain ⟨d,device,resident,_,after,_⟩ := Take.take_some _ _ _ _ _ peer run
    change (geometry r.run.after,txQueueContents r.run.after) =
      (geometry r.run.before,txQueueContents r.run.before)
    apply Prod.ext
    · simp [geometry,Packets.snapshot,Packets.deviceStore,TxDisposition.txPackets,device,after]
    · funext other
      by_cases same : r.pid = other
      · subst other; simp [txQueueContents,handoffTxView,device,after,resident]
      · simp [txQueueContents,handoffTxView,device,after,Std.TreeMap.getElem?_insert,same]

theorem physical {r : Take.Receipt} (before : Inv history ledger debts locals r.run.before) (valid : r.Valid) :
    Packets.Inv r.run.after ∧ TxCoverage locals r.run.after ∧ TxInventory locals r.run.after := by
  have frame := native r valid
  have snapshot : Packets.snapshot r.run.after = Packets.snapshot r.run.before := congrArg (fun x => x.1.1) frame
  have packets : TxDisposition.txPackets r.run.after = TxDisposition.txPackets r.run.before := congrArg (fun x => x.1.2) frame
  have queues : txQueueContents r.run.after = txQueueContents r.run.before := congrArg Prod.snd frame
  exact ⟨by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.cells packets queues,before.inventory.queueContents queues packets⟩

/-- The selected peer's whole cached record is from this invocation, and the
resident record has exactly its staged list cleared. No key borrow is needed. -/
theorem cached (r : Take.Receipt) (valid : r.Valid) (chosen : r.run.value = some peer) :
    ∃ d, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧ peer.staged.isEmpty = false ∧
      r.run.after = {r.run.before with dev := some {d with peers := d.peers.insert r.pid {peer with staged := []}}} ∧
      Staged.stagedAt r.run.after r.pid = some (peer.internalId,[]) := by
  have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
      .ok ((some peer,r.run.after),r.run.ambientAfter) := by rw [←chosen]; exact valid
  obtain ⟨d,device,resident,nonempty,after,_⟩ := Take.take_some _ _ _ _ _ peer run
  exact ⟨d,device,resident,nonempty,after,by simp [Staged.stagedAt,after]⟩

theorem missing (pid : PeerId) (w : WGWorld) (a : Ambient)
    (absent : (w.dev.bind fun d => d.peers[pid]?) = none) :
    ∃ stop, ((Take.takePrefix pid).run w).run a = .error stop := by
  cases device : w.dev with
  | none =>
    simp [Take.takePrefix,getPeer,getDev,device,invariant,AmbientM.invariant]
    exact ⟨_,rfl⟩
  | some d =>
    have absentPeer : d.peers[pid]? = none := by simpa [device] using absent
    simp [Take.takePrefix,getPeer,getDev,device,absentPeer,invariant,AmbientM.invariant]
    exact ⟨_,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TakeFrames
