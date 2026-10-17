import Leanux.Proofs.WG.Index.OwnerCoherenceSessionEffects
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- All normal original session returns preserve hashed-owner coherence under
explicit allocation and rotation freshness. Successful execution supplies the
handshake publication witness; no self-word, positive-peer, or readiness premise
is added. These are local-state obligations, not a reachability invariant. -/
theorem beginSession_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient ok out after pre run
  obtain ⟨final, present, effect⟩ := beginSession_effect pid d p g.keypairCounter
    resident g ambient ok out after ⟨pre.1, rfl⟩ run
  have preserved := sessionEffect_owner_coherent pid d p g.keypairCounter out.keypairCounter
    ok final resident bounded fresh (pre.2 d pre.1) effect
  intro observed observedDevice
  change out.dev = some observed at observedDevice
  rw [present] at observedDevice
  cases observedDevice
  exact preserved

end Leanux.Proofs.WG.Index
