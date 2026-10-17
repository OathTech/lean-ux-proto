import Leanux.Proofs.WG.Index.SessionCoherenceEffects
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.TablePreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The effect and invariant contracts are applied to this same original run. -/
theorem beginSession_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (self : p.handshakeEntryPeer = some pid)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Ensures (beginSession pid) (fun w => w.dev = some d)
      (fun ok w => ∃ final, w.dev = some final ∧ DeviceTablesSafe final ∧
        (ok = true → SessionInstalled pid d p final)) := by
  intro w ambient ok out after pre run
  obtain ⟨final, device, effect⟩ := beginSession_effect pid d p w.keypairCounter
    resident w ambient ok out after ⟨pre, rfl⟩ run
  have tables := (ensures_iff _ _ _).mpr (beginSession_tables pid) w ambient ok out after
    (by intro start present; rw [pre] at present; cases present; exact safe) run
  have finalSafe := tables final device
  refine ⟨final, device, finalSafe, ?_⟩
  intro success
  subst ok
  exact sessionEffect_installed pid d p w.keypairCounter out.keypairCounter final
    self fresh finalSafe effect

end Leanux.Proofs.WG.Index
