import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastAllocation
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastPassiveFrames

/-! Fresh native queue admission cannot reintroduce an encryption identity.
The queue-refusal branches preserve the same exclusion, without treating a
refused batch as admitted or silently discarding its disposition. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition
set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-- At the native queue choice, a batch separated from past encryptions can
only extend the live ring by those distinct-from-history identities. -/
theorem enqueue (pid : PeerId) (items : List SkbId)
    (physical : LiveFrontier.Physical w) (before : Inv past active (view w))
    (fresh : Admissible past items (view w)) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((result,v),b)) :
    Inv past active (view v) ∧ Admissible past items (view v) := by
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp
    (LiveFrontier.enqueue_metadata pid items) w a result v b run
  have cursor : v.netIfindexNext = w.netIfindexNext := congrArg AllocationMetadata.nextEpoch metadata
  have fields (e : Device) (endpoint : v.dev = some e) := allocationMetadata_device metadata endpoint
  have old (current : DeviceView) (found : (view v).device = some current) :
      ∃ d e, w.dev = some d ∧ v.dev = some e ∧
        current = ⟨e.ifindex,e.nextSkb,e.encryptQueue.items⟩ ∧
        e.ifindex = d.ifindex ∧ e.nextSkb = d.nextSkb := by
    change v.dev.map (fun d => (⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩ : DeviceView)) = some current at found
    obtain ⟨e,endpoint,equal⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨d,device,same⟩ := fields e endpoint
    exact ⟨d,e,device,endpoint,equal.symm,congrArg DeviceAllocationMetadata.epoch same,
      congrArg DeviceAllocationMetadata.nextPacket same⟩
  have retains : ∀ d e, w.dev = some d → v.dev = some e →
      e.encryptQueue.items ⊆ d.encryptQueue.items ++ [items] := by
    intro d e device endpoint
    obtain ⟨n,h,refines⟩ := physical d device
    have cases := TxRing.enqueue_result pid items w v a b result run
    simp only [TxRing.nativeCell,device,endpoint,Option.map_some] at cases
    rcases cases with ⟨returned,ring⟩ | ⟨_,ring⟩ | ⟨_,ring,_⟩
    · have equal : e.encryptQueue = d.encryptQueue.produce items := congrArg Prod.snd (Option.some.inj ring)
      have cell : TxRing.nativeCell w = some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
      have room := TxRing.enqueue_free pid items cell (returned ▸ run)
      have contents := LiveFrontier.produced_items refines room
      rw [equal,contents]
      exact List.Subset.refl _
    all_goals
      have equal : e.encryptQueue = d.encryptQueue := congrArg Prod.snd (Option.some.inj ring)
      rw [equal]
      exact fun _ member => List.mem_append_left _ member
  refine ⟨⟨before.1,?_⟩,?_⟩
  · intro label member
    obtain ⟨generation,tag,bound,safe⟩ := before.2 label member
    refine ⟨generation,tag,by simpa only [view,cursor] using bound,?_⟩
    intro current found epoch
    obtain ⟨d,e,device,endpoint,rfl,epochs,frontiers⟩ := old current found
    obtain ⟨below,excluded⟩ := safe ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩
      (by simp [view,device]) (epochs.symm.trans epoch)
    refine ⟨by simpa only [frontiers] using below,?_⟩
    intro pending
    obtain ⟨batch,queued,inside⟩ := List.mem_flatten.mp pending
    rcases List.mem_append.mp queued with ring | detached
    · rcases List.mem_append.mp (retains d e device endpoint ring) with oldRing | offered
      · exact excluded (List.mem_flatten.mpr ⟨batch,List.mem_append_left _ oldRing,inside⟩)
      · have same : batch = items := List.mem_singleton.mp offered
        subst batch
        exact fresh ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩ (by simp [view,device]) label member
          (tag.trans (congrArg some (epochs.symm.trans epoch).symm)) inside
    · exact excluded (List.mem_flatten.mpr ⟨batch,List.mem_append_right _ detached,inside⟩)
  · intro current found label member epoch
    obtain ⟨d,e,device,_,rfl,epochs,_⟩ := old current found
    exact fresh ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩ (by simp [view,device]) label member
      (epoch.trans (congrArg some epochs))

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
