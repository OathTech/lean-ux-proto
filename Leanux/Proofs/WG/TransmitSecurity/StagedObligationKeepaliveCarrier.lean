import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative

/-! Keepalive preparation adds exactly the canonical successful birth, or no
birth at either native refusal arm. Existing allocated packets and cleanup
debts retain their exact ledger identities. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins Queues
open AuthenticatedEffects CausalJournal AllocatedObligation

/-- A successful preparation admits one fixed ticket at the actual event;
refusal and a nonempty queue admit none. No incoming bound or birth-count
assumption is needed because the domain is computed from the journal. -/
theorem core_keepalive (pid : PeerId) (r : WGRunWitness Bool)
    (native : r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (before : Core history ledger debts r.before) :
    ∃ after, Core (history ++ [.keepalivePrepared pid r]) after debts r.after ∧
      (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after) := by
  obtain ⟨d,p,device,resident,outcome⟩ := Staged.keepalive_prepare pid r native
  have unchanged (noBirth : birthPackets (.keepalivePrepared pid r) = [])
      (same : r.after = r.before) :
      ∃ after, Core (history ++ [.keepalivePrepared pid r]) after debts r.after ∧
        (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ after) := by
    refine ⟨ledger,before.quiet_views _ ?_ (same ▸ rfl) (same ▸ rfl) (same ▸ rfl),fun _ _ member => member⟩
    intro event member
    have equal : event = .keepalivePrepared pid r := by simpa using member
    subst event
    exact noBirth
  rcases outcome with ⟨nonempty,ready,same⟩ | ⟨_,refused,same⟩ | ⟨empty,ready,changed⟩
  · apply unchanged ?_ same
    have queue : stagedAt r.before pid = some (p.internalId,p.staged) := by
      simp [stagedAt,device,resident]
    cases packets : p.staged with
    | nil => exact (nonempty packets).elim
    | cons packet rest => simp [birthPackets,ready,queue,packets]
  · exact unchanged (by simp [birthPackets,refused]) same
  · let event := Event.keepalivePrepared pid r
    let added : List Packet := [{mtu := d.mtu}]
    let after := StagedAdmission.appendBirths ledger history.length
      (.staged d.ifindex pid p.internalId) added
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
    obtain ⟨valid,_,queues,terminals⟩ := StagedAdmission.admission before.valid
      (births_bounded history) before.queues epoch sameEpoch old next others born
    refine ⟨after,⟨?_,queues,?_,?_⟩,terminals⟩
    · simpa only [births_emit,birthPackets,ready,ite_true,old,freshTickets] using valid
    · exact (before.selected.admitted history.length d.ifindex pid p.internalId added).append _
    · exact ((before.physical.ledger_frame (admission_allocated_frame _ _ _ _ added)).views sameEpoch cells).append _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
