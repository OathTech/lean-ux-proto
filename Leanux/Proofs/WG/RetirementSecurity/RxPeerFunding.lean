import Leanux.Proofs.WG.RetirementSecurity.RxPeekHolders
import Leanux.Proofs.WG.RetirementSecurity.PeerHolderFunding

/-! RX disposal uses its actual selected carrier credit. Published key slots
also need their independent base/caller peer reference; the two requirements
are checked against the native durable peer ledger, not key-credit counts. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem selected_rx_peer_release_ready {selected : Carrier} {holders : DurableHolders}
    (funded : RxCredits.Protected (selected :: rest) (holders.owners ++ loans) w)
    (anchors : SlotPeerReferences holders loans w)
    (phase : selected.phase = .selected) : PeerReleaseReady selected.owner.slot w := by
  intro p found final
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨q,resident,budget⟩ := selected_credit funded phase
  obtain ⟨old,oldDevice,epoch,oldStored,stamp⟩ := resident_fields resident
  have devices : old = d := Option.some.inj (oldDevice.symm.trans device)
  subst old
  have peers : q = p := Option.some.inj (oldStored.symm.trans stored)
  subst q
  have owner : selected.owner = ⟨d.ifindex,selected.owner.slot,p.internalId⟩ := by
    cases own : selected.owner
    simp only [own] at epoch stamp
    simp_all
  have bound := funded selected.owner
  have balanceEq : RxCredits.balance w selected.owner = p.refcount := by
    simp [RxCredits.balance,resident]
  rw [balanceEq] at bound
  simp only [demand,charges_cons,phase,Phase.charged,and_self,ite_true,
    DurableHolders.owners,List.count_append] at bound
  have noSlots : ¬ (p.keypairNext ≠ none ∨ p.keypairPrevious ≠ none ∨ p.keypairCurrent ≠ none) := by
    intro slots
    have anchored := anchors d selected.owner.slot p device stored slots
    rw [← owner] at anchored
    have positive := List.count_pos_iff.mpr anchored
    simp only [List.count_append] at positive
    omega
  refine ⟨?_,?_,?_⟩
  · by_cases same : p.keypairNext = none
    · exact same
    · exact False.elim (noSlots (Or.inl same))
  · by_cases same : p.keypairPrevious = none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inl same)))
  · by_cases same : p.keypairCurrent = none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inr same)))

/-- Full native selected-packet cleanup derives queue detachment and peer
release safety from the actual carrier ledger and base/caller protection.
The selected key credit is paid once before the physical packet is freed. -/
theorem HolderAccount.cleanup_rx_carrier {selected : Carrier} {holders : DurableHolders}
    (account : HolderAccount (allocation :: temporary) w)
    (carriers : CarrierState (selected :: rest) (holders.owners ++ loans) w)
    (anchors : SlotPeerReferences holders loans w) (phase : selected.phase = .selected)
    (packet : packetAt w selected.packet = some pkt) (key : pkt.keypair = allocation.slot)
    (flag : Bool) (a b : Ambient)
    (run : ((cleanup selected.packet.slot pkt flag).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  obtain ⟨_,stored,resident,owner⟩ := carriers.inventory.present selected (by simp)
  have samePacket : stored = pkt := Option.some.inj (resident.symm.trans packet)
  subst stored
  have ready := selected_rx_peer_release_ready carriers.funded anchors phase
  rw [← owner] at ready
  cases device : w.dev with
  | none => simp [packetAt,device] at packet
  | some d =>
    have epoch : selected.packet.epoch = d.ifindex := by
      by_cases equal : d.ifindex = selected.packet.epoch
      · exact equal.symm
      · simp [packetAt,device,equal] at packet
    have point : selected.packet = ⟨d.ifindex,selected.packet.slot⟩ := by
      cases fields : selected.packet
      simp only [fields] at epoch
      simp_all
    exact account.cleanup_rx pkt key flag
      (selected_rx_detached carriers.inventory carriers.queues phase device point) ready a b run

end Leanux.Proofs.WG.RetirementSecurity
