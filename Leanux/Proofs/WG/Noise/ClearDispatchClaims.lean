import Leanux.Proofs.WG.Noise.ClearDispatchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ClearWorkerDispatch
open Leanux Leanux.WG

/-- Normal actual clear-worker dispatch selects a peer from the initial queue
and exposes its initial peer and reference count. Every other optional tag is
unchanged; the selected tag is absent iff that count was one, otherwise zero.
No ownership, pending-work, readiness or successful-body premise is assumed. -/
theorem original_clear_dispatch_tags (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures Env.runOneClearWorker (fun s => s = entry)
      (fun _ final => ∃ pid d p,
        Index.clearWorkerSelected entry = some pid ∧
        entry.wg.device = some d ∧ pid ∈ d.clearWorkQueue ∧
        entry.toSnapshot.peerAt pid = some p ∧ 0 < p.refcount ∧
        ∀ target, final.toSnapshot.tagAt target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else entry.toSnapshot.tagAt target) := by
  intro initial result final pre run
  obtain ⟨pid,d,p,selected,device,queued,resident,positive,tags⟩ :=
    runOneClearWorker_tags initial final result run
  refine ⟨pid,d,p,?_,?_,queued,?_,positive,?_⟩
  · rwa [pre] at selected
  · rw [← pre]
    exact device
  · rw [← pre]
    simpa [Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,
      Campaign2.Snapshot.peerAt,device] using resident
  · intro target
    rw [← pre]
    exact tags target

end Leanux.Proofs.WG.Noise.ClearWorkerDispatch
