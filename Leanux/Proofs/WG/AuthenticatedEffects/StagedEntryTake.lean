import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTakeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAllocationLineage

/-! A completed take separates idle entry state from an active selected
frontier. The latter retains exactly the same provenance and native ownership
components, replacing NoSelected by the sole actual take position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance
open HandshakeSecurity.StagedConservation

structure Active (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (position : Nat) (w : WGWorld) : Prop where
  core : Core history ledger debts w
  justified : Justified history ledger
  allocationLinks : AllocationLinks history ledger
  onlySelected : OnlySelected position ledger
  packets : Packets.Inv w
  coverage : TxCoverage locals w
  inventory : TxInventory locals w

/-- Active frontiers retain the same fixed take position under passive native
views and birth-free history extension. This does not finish the invocation. -/
theorem Active.views (before : Active history ledger debts locals position w)
    (suffix : List Event) (quiet : ∀ event ∈ suffix, birthPackets event = [])
    (epoch : Packets.epoch v = Packets.epoch w) (queues : Staged.stagedAt v = Staged.stagedAt w)
    (material : PacketMaterial.view v = PacketMaterial.view w)
    (snapshot : Packets.snapshot v = Packets.snapshot w)
    (packets : Queues.TxDisposition.txPackets v = Queues.TxDisposition.txPackets w)
    (owners : txQueueContents v = txQueueContents w) :
    Active (history ++ suffix) ledger debts locals position v := by
  refine ⟨before.core.quiet_views suffix quiet epoch queues material,
    before.justified.append suffix,before.allocationLinks.append suffix,before.onlySelected,?_,
    before.coverage.cells packets owners,before.inventory.queueContents owners packets⟩
  simpa only [Packets.Inv,snapshot] using before.packets

theorem taken (r : Take.Receipt) (valid : r.Valid) (chosen : r.run.value = some peer)
    (before : Inv history ledger debts locals r.run.before) :
    ∃ after, TakeAccounted (births history) ledger history r after ∧
      Active (history ++ [.stagingTaken r]) after debts locals history.length r.run.after ∧
      ∃ generation, Packets.epoch r.run.before = some generation ∧
        after = transferLocation (.staged generation r.pid peer.internalId) (.selected history.length) ledger ∧
        Aligned (Born (history ++ [.stagingTaken r]) generation r.pid peer.internalId)
          (pendingAt (.selected history.length) after) peer.staged := by
  obtain ⟨after,accounted,core⟩ := core_take r valid before.core
  have exactTransfer := accounted.exactTransfer
  rw [chosen] at exactTransfer
  obtain ⟨generation,epoch,equal,_,aligned⟩ := exactTransfer
  have native := TakeFrames.physical before valid
  refine ⟨after,accounted,⟨core,?_,?_,take_selected_only r chosen accounted before.noSelected,
    native.1,native.2.1,native.2.2⟩,generation,epoch,equal,aligned⟩
  · rw [equal]
    exact (before.justified.transfer _ _).append _
  · rw [equal]
    exact (before.allocationLinks.transferred _ _ (by simp) (by simp)).append _

/-- Empty take is a true idle return, with the resident empty peer explicitly
witnessed and the original ledger unchanged. It is not an absent-peer case. -/
theorem idle (r : Take.Receipt) (valid : r.Valid) (empty : r.run.value = none)
    (before : Inv history ledger debts locals r.run.before) :
    Inv (history ++ [.stagingTaken r]) ledger debts locals r.run.after ∧
      ∃ d peer, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧
        peer.staged.isEmpty = true ∧ r.run.after = r.run.before := by
  have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
      .ok ((none,r.run.after),r.run.ambientAfter) := by rw [←empty]; exact valid
  obtain ⟨d,peer,device,resident,emptyPeer,same,_⟩ := Take.take_none _ _ _ _ _ run
  refine ⟨?_,d,peer,device,resident,emptyPeer,same⟩
  rw [same]
  exact before.views _ (by intro e member; have eq := List.mem_singleton.mp member; subst e; rfl)
    rfl rfl rfl rfl rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
