import Leanux.Proofs.WG.Queues.AdmissionAuxiliary
import Leanux.Proofs.WG.Queues.HolderEntry
import Leanux.Proofs.WG.Queues.ReceiveEffects

/-! Accepted RX carriers need only the existing resident/release invariant.
A previous normal-poll release forbids later residency of that identity, even
after device deletion and recreation. No new global allocation invariant is
an input to these contracts. Whole-source occurrence accounting remains a
separate use of these local facts. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.CarrierIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open DurableHolders

def stamp (p : RxCredits.Packet) : PacketStamp := (p.epoch, p.slot + 1)

theorem stamp_injective {p q : RxCredits.Packet} (he : stamp p = stamp q) : p=q := by
  cases p
  cases q
  simp only [stamp, Prod.mk.injEq, Nat.add_right_cancel_iff] at he
  cases he.1
  cases he.2
  rfl

theorem packetOfStamp (p : RxCredits.Packet) : PollCarrier.packetOfStamp (stamp p)=p := by
  cases p
  simp [stamp,PollCarrier.packetOfStamp]

theorem resident (live : packetAt w p=some packet) :
    packetResidents w (.inr p.slot)=some (stamp p) := by
  cases hd : w.dev with
  | none => simp [packetAt,hd] at live
  | some d =>
    simp only [packetAt,hd] at live
    change (if d.ifindex != p.epoch then none else d.rxSkbs[p.slot]?) = some packet at live
    split at live
    · contradiction
    · rename_i epoch
      have he : d.ifindex=p.epoch := by simpa using epoch
      simp [packetResidents,hd,live,stamp,he]

theorem pending_not_released (allocation : AllocationInv prior w)
    (inventory : Inventory cs w) (member : c ∈ cs) :
    ¬ RxJoint.PriorReleased prior (stamp c.packet) := by
  obtain ⟨_,packet,live,_⟩ := inventory.present c member
  intro released
  exact allocation.release.1.packet.2 _ released _ (resident live)

theorem boundary_not_released (account : Boundary cs loans w)
    (allocation : AllocationInv prior w) (member : c ∈ cs) :
    ¬ RxJoint.PriorReleased prior (stamp c.packet) := by
  obtain ⟨holders,funded,_⟩ := account
  exact pending_not_released allocation funded.carriers.inventory member

theorem entry_not_released (entry : HolderEntry.Inv cs loans h w) (member : c ∈ cs) :
    ¬ RxHistory.Released h (stamp c.packet) :=
  boundary_not_released entry.1.1.1 entry.2.allocation member

theorem released_prefix (released : RxHistory.Released h s) (history : k=h++tail) :
    RxHistory.Released k s := by
  rw [history,RxHistory.released_append]
  exact Or.inl released

/-- Both worlds may be separated by arbitrary committed operations, including
deletion/recreation. The original accumulated release history is retained. -/
theorem no_reentry (entry : HolderEntry.Inv cs loans k w)
    (released : RxHistory.Released h (stamp p)) (history : k=h++tail) :
    p ∉ cs.map Carrier.packet := by
  intro hm
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  exact entry_not_released entry hc (he.symm ▸ released_prefix released history)

/-- The actual receive source derives the output account and owner invariant;
neither output funding nor output freshness is a premise. -/
theorem receive_not_released (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (step : AdmissionCaller.Step cs next msg src w v h k) (member : c ∈ next) :
    ¬ RxHistory.Released h (stamp c.packet) := by
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  have boundary := AdmissionCaller.step_boundary step account (HolderAuxiliary.owner_packets owner) ring
  have after := (OwnerReceive.wgReceive_checked msg src w h owner).choose_spec.2.2
  have actual : runPrefix (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) w h=
      (.ok ((),v),k) := step.1
  rw [actual] at after
  obtain ⟨suffix,history⟩ := AdmissionCaller.step_appends step
  intro released
  have atEnd := released_prefix released history
  exact boundary_not_released boundary after.allocation member atEnd

theorem receive_no_reentry (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (step : AdmissionCaller.Step cs next msg src w v h k)
    (released : RxHistory.Released h (stamp p)) :
    p ∉ next.map Carrier.packet := by
  intro hm
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  exact receive_not_released account physical owner step hc (he.symm ▸ released)

/-- For a newly accepted source occurrence, earlier pending carriers are
excluded by the derived inventory; earlier released carriers are excluded by
the existing lifetime invariant. These are the two conservation alternatives. -/
theorem accepted_fresh (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (step : AdmissionCaller.Step cs next msg src w v h k)
    (accepted : ReceiveEffects.Accepted cs next msg src w.wg v.wg w.ambient v.ambient c)
    (older : old ∈ cs ∨ RxHistory.Released h (stamp old.packet)) :
    c.packet ≠ old.packet := by
  have ledger := ReceiveEffects.accepted_ledger accepted
  rcases older with pending | released
  · obtain ⟨epoch,n,ringHistory,ring⟩ := physical
    obtain ⟨holders,funded,_⟩ := AdmissionCaller.step_boundary step account
      (HolderAuxiliary.owner_packets owner) ring
    have distinct := funded.carriers.inventory.distinct
    rw [ledger,List.map_cons,List.nodup_cons] at distinct
    intro same
    exact distinct.1 (List.mem_map.mpr ⟨old,pending,same.symm⟩)
  · intro same
    apply receive_not_released account physical owner step (c := c)
      (by rw [ledger]; exact List.mem_cons_self)
    simpa only [same] using released

/-- The same theorem at a designated old journal prefix, without any
uniqueness assumption on event values or poll-local occurrence counters. -/
theorem accepted_after_release {old : Carrier} (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (step : AdmissionCaller.Step cs next msg src w v h k)
    (accepted : ReceiveEffects.Accepted cs next msg src w.wg v.wg w.ambient v.ambient c)
    (released : RxHistory.Released earlier (stamp old.packet))
    (position : h=earlier++between) : c.packet ≠ old.packet :=
  accepted_fresh account physical owner step accepted
    (Or.inr (released_prefix released position))

/-- One completed accepted admission contributes exactly one occurrence of
its packet identity to the source-selected ledger. -/
theorem accepted_count (account : Boundary cs loans w.wg)
    (physical : DecryptIteration.Physical w) (owner : OwnerChecks.Inv h w)
    (step : AdmissionCaller.Step cs next msg src w v h k)
    (accepted : ReceiveEffects.Accepted cs next msg src w.wg v.wg w.ambient v.ambient c) :
    (next.map Carrier.packet).count c.packet=1 := by
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  obtain ⟨holders,funded,_⟩ := AdmissionCaller.step_boundary step account
    (HolderAuxiliary.owner_packets owner) ring
  apply funded.carriers.inventory.distinct.count_of_mem
  exact List.mem_map.mpr ⟨c,by rw [ReceiveEffects.accepted_ledger accepted]; exact List.mem_cons_self,rfl⟩

end Leanux.Proofs.WG.Queues.RxCredits.CarrierIdentity
