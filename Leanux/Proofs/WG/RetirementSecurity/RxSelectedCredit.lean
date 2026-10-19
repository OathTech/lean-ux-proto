import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceConfiguration
import Leanux.Proofs.WG.RetirementSecurity.RxPeekHolders

/-! Selected RX disposal derives peer-release readiness from the actual
carrier and independent base/caller protection. Its key reference is the
separate native dequeue credit, never inferred from the peer count. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
variable {selected : Carrier} {id : SkbId}

theorem selected_rx_release_funded
    (funded : holders.Funded (selected::rest) loans w)
    (anchors : SlotPeerReferences holders loans w)
    (phase : selected.phase=.selected) : PeerReleaseFunded selected.owner.slot w := by
  intro p found
  obtain ⟨q,resident,budget⟩ := selected_credit funded.carriers.funded phase
  obtain ⟨d,device,epoch,stored,stamp⟩ := resident_fields resident
  have same : q=p := Option.some.inj
    ((show peerAt w selected.owner.slot=some q by simp [peerAt,device,stored]).symm.trans found)
  subst q
  refine ⟨by omega,?_⟩
  intro final
  have noSlots : ¬(p.keypairNext≠none ∨ p.keypairPrevious≠none ∨ p.keypairCurrent≠none) := by
    intro slots
    have anchored := anchors d selected.owner.slot p device stored slots
    have owner : (⟨d.ifindex,selected.owner.slot,p.internalId⟩ : Owner)=selected.owner := by
      cases own:selected.owner
      simp_all
    rw [owner] at anchored
    have positive : 0<(holders.owners++loans).count selected.owner := by
      apply List.count_pos_iff.mpr
      rcases List.mem_append.mp anchored with base | loan
      · exact List.mem_append_left _ (by simp [DurableHolders.owners,base])
      · exact List.mem_append_right _ loan
    simp only [demand] at budget
    omega
  refine ⟨?_,?_,?_⟩
  · by_cases same:p.keypairNext=none
    · exact same
    · exact False.elim (noSlots (Or.inl same))
  · by_cases same:p.keypairPrevious=none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inl same)))
  · by_cases same:p.keypairCurrent=none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inr same)))

/-- The actual selected RX phase supplies detachment and final-peer safety
at cleanup. The saved key word is tied to its separately transferred credit. -/
theorem HolderAccount.cleanup_rx_selected
    (account : HolderAccount (allocation::temporary) w)
    (funded : holders.Funded (selected::rest) loans w)
    (anchors : SlotPeerReferences holders loans w)
    (phase : selected.phase=.selected)
    (device : w.dev=some d) (packet : selected.packet=⟨d.ifindex,id⟩)
    (owner : pkt.peer=selected.owner.slot) (key : pkt.keypair=allocation.slot)
    (flag : Bool) (a b : Ambient)
    (run : ((cleanup id pkt flag).run w).run a=.ok (((),v),b)) :
    HolderAccount temporary v ∧ CarrierState rest (holders.owners++loans) v := by
  have detached := selected_rx_detached funded.carriers.inventory funded.carriers.queues phase device packet
  have ready := (selected_rx_release_funded funded anchors phase).ready
  have keys := account.cleanup_rx pkt key flag detached (owner ▸ ready) a b run
  have slot : selected.packet.slot=id := congrArg RxCredits.Packet.slot packet
  have state := selected_cleanup funded.carriers phase owner a b (by simpa only [slot] using run)
  exact ⟨keys,state.1⟩

end Leanux.Proofs.WG.RetirementSecurity
