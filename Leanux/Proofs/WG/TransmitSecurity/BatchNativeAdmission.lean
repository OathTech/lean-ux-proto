import Leanux.Proofs.WG.TransmitSecurity.BatchNativePackets

/-! Both native enqueue outcomes preserve batch homogeneity. Peer-queue
admission happens before ring refusal, so EPIPE retains the same aligned batch. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem enqueue_material (pid : PeerId) (items : List SkbId) :
    SameView PacketMaterial.view (enqueuePerDeviceAndPeer pid items) := by
  intro initial
  let P := fun w => PacketMaterial.view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have edit (f : Device → Device) (same : ∀ d, (f d).txSkbs = d.txSkbs) :=
    (PacketMaterial.modify_device f same).wp (fun v => v = initial)
  change Preserves P _
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  simp only [branch,invariant,queueDeviceWork]
  repeat' first
    | (allocation_release_head setTxSkb
       exact (PacketMaterial.set_tx _ (fun p => {p with state := .uncrypted}) (fun _ => rfl)).wp (· = initial))
    | (allocation_release_head getPeer; exact (PacketMaterial.read_peer _).wp (· = initial))
    | (allocation_release_head getDev; unfold getDev)
    | (allocation_release_head setPeer; unfold setPeer)
    | (allocation_release_head modifyDev; exact edit _ (fun _ => rfl))
    | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem enqueue (before : Inv w) (fresh : Aligned w pid slot items)
    (a b : Ambient) (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    Inv v ∧ Aligned v pid slot items := by
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (enqueue_material pid items) w a ret v b run
  have fresh' := fresh.frame material
  refine ⟨?_,fresh'⟩
  intro other p found batch member
  have point : handoffTxView v other = some p.txQueue.all := by
    simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found
  rcases enqueue_queue_effect pid items a b run with ⟨_,same⟩ | ⟨_,_,effect⟩
  · rw [same] at point
    obtain ⟨old,resident,queue⟩ := Option.map_eq_some_iff.mp point
    obtain ⟨kid,aligned⟩ := before other old resident batch (queue.symm ▸ member)
    exact ⟨kid,aligned.frame material⟩
  · rw [effect other] at point
    obtain ⟨batches,previous,queue⟩ := Option.map_eq_some_iff.mp point
    obtain ⟨old,resident,oldQueue⟩ := Option.map_eq_some_iff.mp previous
    have split := List.mem_append.mp (queue.symm ▸ member)
    rcases split with previousBatch | newBatch
    · obtain ⟨kid,aligned⟩ := before other old resident batch (oldQueue.symm ▸ previousBatch)
      exact ⟨kid,aligned.frame material⟩
    · by_cases same : other = pid
      · subst other
        simp only [ite_true,List.mem_singleton] at newBatch
        subst batch
        exact ⟨slot,fresh'⟩
      · simp only [same,ite_false,List.not_mem_nil] at newBatch

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
