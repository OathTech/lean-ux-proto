import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastCreationFrames

/-! The historical encryption exclusion survives native staged submission,
including all queue-refusal and cleanup branches. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition
set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-- Native creation preserves separation from all historical encryption
identities on successful admission and every normal refusal/cleanup arm. -/
theorem create_ready (pid : PeerId) (items : List SkbId) :
    Preserves (CreationReady past active items) (createData pid items) := by
  unfold createData
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue_ready pid items)
    | (rx_retention_head enqueuePerPeerTx; exact publish_ready items _)
    | encryption_creation_step items

/-- Actual staged submission acquires, allocates, and offers a fresh batch;
it preserves exclusion of every already encrypted occurrence from pending work. -/
theorem staged_submit (pid kid : Nat) (packets : List DataPacket)
    (ready : LiveFrontier.Ready w) (before : Inv past active (view w))
    (a b : Ambient)
    (run : ((RxCredits.stagedSubmit pid kid packets).run w).run a = .ok ((result,v),b)) :
    LiveFrontier.Ready v ∧ Inv past active (view v) := by
  rw [LiveFrontier.staged_factor] at run
  obtain ⟨items,u,clock,allocated,created⟩ := RxCredits.bind_ok_native run
  have bounded := LiveFrontier.staged_allocated kid packets ready allocated
  obtain ⟨acquiredValue,x,tick,acquired,allocated⟩ := RxCredits.bind_ok_native allocated
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (acquire_view kid) w a acquiredValue x tick acquired
  have fresh := allocate packets (same ▸ before) tick clock allocated
  have completed := (hoare_iff_run_ambient _ _ _).mp (create_ready pid items)
    u clock result v b ⟨bounded,fresh⟩ created
  exact ⟨completed.1.1,completed.2.1⟩

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
