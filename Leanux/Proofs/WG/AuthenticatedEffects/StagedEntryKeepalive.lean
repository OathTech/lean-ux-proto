import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTake
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeepalive

/-! Native keepalive preparation admits a fixed empty-packet ticket only on
its successful empty-queue arm. A nonempty queue can return true without a
birth. The same ledger retains provenance and physical TX ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance Staged

inductive KeepaliveChange (history : List Event) (ledger : Ledger) (pid : PeerId)
    (r : WGRunWitness Bool) : Ledger → Prop where
  | unchanged (noBirth : birthPackets (.keepalivePrepared pid r) = [])
      (same : r.after = r.before) : KeepaliveChange history ledger pid r ledger
  | admitted (generation stamp mtu : Nat) (ready : r.value = true)
      (epoch : Packets.epoch r.before = some generation)
      (empty : stagedAt r.before pid = some (stamp,[]))
      (mtuRead : r.before.dev.map Device.mtu = some mtu) :
      KeepaliveChange history ledger pid r
        (StagedAdmission.appendBirths ledger history.length (.staged generation pid stamp) [{mtu}])

theorem keepalive_physical (pid : PeerId) (r : WGRunWitness Bool)
    (native : r.Valid (OccurrenceHandshake.keepalivePrepare pid))
    (before : Inv history ledger debts locals r.before) :
    Packets.Inv r.after ∧ TxCoverage locals r.after ∧ TxInventory locals r.after := by
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceHandshake.keepalive_prepare_geometry pid) r.before r.ambientBefore r.value r.after r.ambientAfter native
  have queue := (ProjectedAction.iff_run_ambient _ _ _).mp
    (contents_factor (OccurrenceHandshake.keepalive_prepare_queues pid))
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  have snapshot : Packets.snapshot r.after = Packets.snapshot r.before := congrArg Prod.fst shape
  have cells : TxDisposition.txPackets r.after = TxDisposition.txPackets r.before := congrArg Prod.snd shape
  exact ⟨by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.cells cells queue,before.inventory.queueContents queue cells⟩

/-- One actual preparation receipt transports the entire entry bundle. Its
fixed ticket domain records exactly the new keepalive, never an already-staged
packet, and all previous terminal results keep their native evidence. -/
theorem keepalive_receipt (pid : PeerId) (r : WGRunWitness Bool)
    (native : r.Valid (OccurrenceHandshake.keepalivePrepare pid))
    (before : Inv history ledger debts locals r.before) :
    ∃ after, Inv (history ++ [.keepalivePrepared pid r]) after debts locals r.after ∧
      KeepaliveChange history ledger pid r after ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  obtain ⟨d,p,device,resident,outcome⟩ := Staged.keepalive_prepare pid r native
  have unchanged (noBirth : birthPackets (.keepalivePrepared pid r) = []) (same : r.after = r.before) :
      ∃ after, Inv (history ++ [.keepalivePrepared pid r]) after debts locals r.after ∧
        KeepaliveChange history ledger pid r after ∧
        ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ after := by
    refine ⟨ledger,before.views _ ?_ (same ▸ rfl) (same ▸ rfl) (same ▸ rfl)
      (same ▸ rfl) (same ▸ rfl) (same ▸ rfl),.unchanged noBirth same,fun _ _ member => member⟩
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact noBirth
  rcases outcome with ⟨nonempty,ready,same⟩ | ⟨_,refused,same⟩ | ⟨empty,ready,changed⟩
  · apply unchanged ?_ same
    have queue : stagedAt r.before pid = some (p.internalId,p.staged) := by simp [stagedAt,device,resident]
    cases packets : p.staged with
    | nil => exact (nonempty packets).elim
    | cons packet rest => simp [birthPackets,ready,queue,packets]
  · exact unchanged (by simp [birthPackets,refused]) same
  · let event := Event.keepalivePrepared pid r
    let added : List Packet := [{mtu := d.mtu}]
    let after := StagedAdmission.appendBirths ledger history.length (.staged d.ifindex pid p.internalId) added
    have epoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
    have sameEpoch : Packets.epoch r.after = Packets.epoch r.before := by simp [Packets.epoch,device,changed]
    have cells : PacketMaterial.view r.after = PacketMaterial.view r.before := by
      funext id
      simp [PacketMaterial.view,TxDisposition.txPackets,device,changed]
    have old : stagedAt r.before pid = some (p.internalId,[]) := by simp [stagedAt,device,resident,empty]
    have next : stagedAt r.after pid = some (p.internalId,[{mtu := d.mtu}]) := by simp [stagedAt,changed]
    have others : ∀ other, pid ≠ other → stagedAt r.after other = stagedAt r.before other := by
      intro other different
      simp [stagedAt,changed,device,Std.TreeMap.getElem?_insert,different]
    have born : Aligned (Born (history ++ [event]) d.ifindex pid p.internalId)
        (freshTickets history.length 0 added) added :=
      .cons (.keepalive r history [] d.mtu rfl native ready (sameEpoch.trans epoch) old next
        (by simp [device])) .nil
    obtain ⟨valid,_,queues,terminals⟩ := StagedAdmission.admission before.core.valid
      (births_bounded history) before.core.queues epoch sameEpoch old next others born
    have physical := keepalive_physical pid r native before
    refine ⟨after,⟨⟨?_,queues,?_,?_⟩,?_,?_,before.noSelected.admitted _ _ _ _ added,
      physical.1,physical.2.1,physical.2.2⟩,.admitted d.ifindex p.internalId d.mtu ready epoch old (by simp [device]),terminals⟩
    · simpa only [births_emit,birthPackets,ready,ite_true,old,freshTickets] using valid
    · exact (before.core.selected.admitted history.length d.ifindex pid p.internalId added).append _
    · exact ((before.core.physical.ledger_frame (admission_allocated_frame _ _ _ _ added)).views sameEpoch cells).append _
    · exact (before.justified.admitted _ _ added).append _
    · exact (before.allocationLinks.admitted _ _ _ _ added).append _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
