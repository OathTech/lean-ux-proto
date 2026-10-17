import Leanux.Proofs.WG.Index.SessionAllocationEffects
import Leanux.Proofs.WG.Noise.SessionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Apply the exact session effect to the same original execution. The entry
bound supplies allocation freshness; it supplies no slot or lifetime invariant. -/
theorem beginSession_allocation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (bound : KeypairStoreBounded d) :
    Ensures (beginSession pid) (fun w => w.dev = some d)
      (fun ok w => ∃ final, w.dev = some final ∧ KeypairStoreBounded final ∧
        final.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) ∧
        d.keypairs[d.nextKeypairId]? = none) := by
  intro w ambient ok out after pre run
  obtain ⟨final, device, effect⟩ := beginSession_effect pid d p w.keypairCounter
    resident w ambient ok out after ⟨pre, rfl⟩ run
  obtain ⟨bounded, cursor⟩ := sessionEffect_allocation pid d p _ _ ok final bound effect
  exact ⟨final, device, bounded, cursor, store_bound_absent d bound⟩

end Leanux.Proofs.WG.Index
