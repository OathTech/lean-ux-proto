import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryContract

/-! Entry frames for the original DEAD-worker repayment suffix. The selected
packet cells have already been freed, so the cached key is repaid directly. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal QueueHandoff

theorem key_entry (key : KeypairId)
    (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
      w history = (.ok ((),v),last)) : StagedEntry.Inv last ledger debts locals v.wg := by
  obtain ⟨owned,bounds⟩ := key_put_owned (some key) (StagedEntry.Queue.owned before) before.packets performed
  obtain ⟨suffix,extended,_⟩ := focused_quiet (TxDisposition.nativeAccess (keypairPutPrefix (some key) false)) w history
  change (runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [extended] at owned ⊢
  exact StagedEntry.Queue.semantic before suffix owned bounds

/-- At an idle worker boundary no earlier completion cleanup debt exists.
Actual owning queue membership therefore yields pending allocation tickets,
using resident cell coverage rather than assuming a conservation result. -/
theorem queued_pending (before : StagedEntry.Inv history ledger [] locals w)
    (resident : peerAt w pid = some peer) (queued : items ∈ peer.txQueue.all) :
    PendingBatch history ledger items := by
  intro id member
  obtain ⟨packet,cell⟩ := before.inventory.queueResident pid peer resident id
    (List.mem_flatten.mpr ⟨items,queued,member⟩)
  have material : PacketMaterial.view w id = some (PacketMaterial.material packet) := by
    simp only [PacketMaterial.view,cell,Option.map_some]
  obtain ⟨generation,ticket,position,ordinal,_,origin,pending⟩ := before.core.physical.covered.pending material
  exact ⟨ticket,position,ordinal,generation,PacketMaterial.material packet,pending,origin⟩

/-- An actually selected local at a debt-free worker boundary has the same
pending allocation assignment for every resident packet. -/
theorem selected_pending (before : StagedEntry.Inv history ledger [] (⟨phase,pid,items⟩ :: locals) w) :
    PendingBatch history ledger items := by
  intro id member
  obtain ⟨packet,cell⟩ := before.inventory.localResident id (by simp [txLocalItems,member])
  have material : PacketMaterial.view w id = some (PacketMaterial.material packet) := by
    simp only [PacketMaterial.view,cell,Option.map_some]
  obtain ⟨generation,ticket,position,ordinal,_,origin,pending⟩ := before.core.physical.covered.pending material
  exact ⟨ticket,position,ordinal,generation,PacketMaterial.material packet,pending,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
