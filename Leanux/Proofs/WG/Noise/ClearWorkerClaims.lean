import Leanux.Proofs.WG.Noise.ClearWorkerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ClearWorker
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- All other optional tags are unchanged. The worker's own tag is absent
exactly when its entry peer had its last reference, and zero otherwise.
Normal completion supplies initial residency and a positive reference count;
there is no execution-readiness premise. -/
theorem original_queued_clear_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid) (fun s => s = entry)
      (fun _ final => ∃ p, entry.peerAt pid = some p ∧ 0 < p.refcount ∧
        ∀ target, final.tagAt target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else entry.tagAt target) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [queuedExpiredZeroKeyMaterial,handshakeClear,IndexOwner.peerDeref,
      IndexOwner.peerWord,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [queuedExpiredZeroKeyMaterial,handshakeClear,IndexOwner.peerDeref,
        IndexOwner.peerWord,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := queuedClear_effect pid d p resident g ambient result final after device run
      refine ⟨p,?_,effect.1,?_⟩
      · rw [← pre]
        simp [Campaign2.Snapshot.peerAt,Campaign2.snapshot,Campaign2.core,device,resident]
      · intro target
        rw [← pre]
        simpa [Campaign2.Snapshot.tagAt,Campaign2.Snapshot.peerAt,
          Campaign2.snapshot,Campaign2.core,responseTagMap,device] using effect.2 target


end Leanux.Proofs.WG.Noise.ClearWorker
