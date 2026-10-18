import Leanux.Proofs.WG.Index.HashSlotClearClaims
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryClaims
import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.Noise.ClearWorkerClaims
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Residency and a positive entry reference are consequences of the same
normal whole-worker run, via the existing complete tag-effect theorem. -/
theorem queuedClear_normal_entry (pid : PeerId) (g out : WGWorld)
    (ambient after : Ambient) (result : Unit)
    (run : ((queuedExpiredZeroKeyMaterial pid).run g).run ambient =
      .ok ((result,out),after)) :
    ∃ d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount := by
  obtain ⟨p,found,live,_⟩ := ClearWorker.original_queued_clear_tags pid
    (Campaign2.snapshot g ambient) g ambient result out after rfl run
  cases device : g.dev with
  | none =>
    simp [Campaign2.Snapshot.peerAt,Campaign2.snapshot,Campaign2.core,device] at found
  | some d =>
    exact ⟨d,p,rfl,
      by simpa [Campaign2.Snapshot.peerAt,Campaign2.snapshot,Campaign2.core,device] using found,live⟩

end Leanux.Proofs.WG.Index
