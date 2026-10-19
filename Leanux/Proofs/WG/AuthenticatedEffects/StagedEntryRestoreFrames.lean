import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTake
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCarrier

/-! Restoring held plaintext changes no allocated TX cell or owning TX queue.
These exact native frames require neither a live current key nor any bound on
its references; restore concerns the resident peer's staged queue. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Obligations
open RetirementSecurity RetirementSecurity.StagingOccurrences Queues.RxCredits
open HandshakeSecurity.StagedConservation

theorem native_views (r : Restore.Receipt) (valid : r.Valid) :
    StagedAdmission.Front.Ownership.view r.run.after = StagedAdmission.Front.Ownership.view r.run.before := by
  obtain ⟨d,p,device,resident,after,_⟩ := HandshakeSecurity.NonceRejection.restoration r.pid r.packets r.run valid
  change (geometry r.run.after,txQueueContents r.run.after) =
    (geometry r.run.before,txQueueContents r.run.before)
  apply Prod.ext
  · simp [geometry,Packets.snapshot,Packets.deviceStore,TxDisposition.txPackets,device,after]
  · funext other
    by_cases same : r.pid = other
    · subst other; simp [txQueueContents,handoffTxView,device,after,resident]
    · simp [txQueueContents,handoffTxView,device,after,Std.TreeMap.getElem?_insert,same]

theorem physical (r : Restore.Receipt) (valid : r.Valid)
    (before : Active history ledger debts locals position r.run.before) :
    Packets.Inv r.run.after ∧ TxCoverage locals r.run.after ∧ TxInventory locals r.run.after := by
  have frame := native_views r valid
  have snapshot : Packets.snapshot r.run.after = Packets.snapshot r.run.before := congrArg (fun x => x.1.1) frame
  have cells : TxDisposition.txPackets r.run.after = TxDisposition.txPackets r.run.before := congrArg (fun x => x.1.2) frame
  have queues : txQueueContents r.run.after = txQueueContents r.run.before := congrArg Prod.snd frame
  exact ⟨by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.cells cells queues,before.inventory.queueContents queues cells⟩

/-- A resident staged queue makes the native restore cut total: there are no
allocation choices, key-reference tests or ambient effects in these reads and
write. Later no-key work is outside this cut. -/
theorem native_total (pid : PeerId) (packets : List WG.Packet) (w : WGWorld) (a : Ambient)
    (resident : Staged.stagedAt w pid = some (allocation,queued)) :
    ∃ v, ((Restore.nativeRestore pid packets).run w).run a = .ok (((),v),a) := by
  cases device : w.dev with
  | none => simp [Staged.stagedAt,device] at resident
  | some d =>
    cases peer : d.peers[pid]? with
    | none => simp [Staged.stagedAt,device,peer] at resident
    | some p =>
      refine ⟨{w with dev := some {d with peers := d.peers.insert pid {p with staged := packets ++ p.staged}}},?_⟩
      simp [Restore.nativeRestore,getPeer,getDev,setPeer,modifyDev,device,peer]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
