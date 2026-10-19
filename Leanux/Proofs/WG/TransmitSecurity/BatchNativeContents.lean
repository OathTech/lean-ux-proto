import Leanux.Proofs.WG.TransmitSecurity.BatchNativeStaging

/-! Empty peer creation or retirement changes optional residency but cannot
change any nonempty TX batch. This frame uses the existing queue-content view. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem contents_frame (before : Inv w) (queues : txQueueContents v = txQueueContents w)
    (material : PacketMaterial.view v = PacketMaterial.view w) : Inv v := by
  intro pid p found items member
  have nonempty : p.txQueue.all ≠ [] := by intro empty; simp [empty] at member
  obtain ⟨old,resident,queue⟩ := queueContents_resident queues found nonempty
  obtain ⟨slot,aligned⟩ := before pid old resident items (queue.symm ▸ member)
  exact ⟨slot,aligned.frame material⟩

theorem contents {action : WG.M α} (queues : SameView txQueueContents action)
    (material : SameView PacketMaterial.view action) : Preserves Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact contents_frame before
    ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp material w a result v b run)

theorem contents_wire {action : WG.M α} (queues : SameView txQueueContents action)
    (wire : SameView txCryptWire action) : Preserves Inv action :=
  contents queues (PacketMaterial.of_packets (wire.factor Prod.snd))

theorem coherent_join {action : WG.M α}
    (physical : Preserves (OccurrenceStack.Ready locals active) action)
    (coherent : Preserves Inv action) : Preserves (Coherent locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp coherent w a result v b before.2 run⟩

theorem coherent_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Coherent locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨OccurrenceStack.ready_store fields before.1,
    (hoare_iff_run_ambient _ _ _).mp (store same) w a result v b before.2 run⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
