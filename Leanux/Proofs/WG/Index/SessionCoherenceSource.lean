import Leanux.Proofs.WG.Index.SessionCoherenceEffects
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.ResponseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The effect and invariant contracts are applied to this same original run. -/
theorem beginSession_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (self : p.handshakeEntryPeer = some pid)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Ensures (beginSession pid) (fun w => w.k.wg = some d)
      (fun ok w => ∃ final, w.k.wg = some final ∧ DeviceTablesSafe final ∧
        (ok = true → SessionInstalled pid d p final)) := by
  intro w ok out pre run
  obtain ⟨final, device, effect⟩ := beginSession_effect pid d p w.k.keypairCounter
    resident w ok out ⟨pre, rfl⟩ run
  have tables := (ensures_iff _ _ _).mpr (beginSession_tables pid) w ok out
    (by intro start present; rw [pre] at present; cases present; exact safe) run
  have finalSafe := tables final device
  refine ⟨final, device, finalSafe, ?_⟩
  intro success
  subst ok
  exact sessionEffect_installed pid d p w.k.keypairCounter out.k.keypairCounter final
    self fresh finalSafe effect

end Leanux.Proofs.WG.Index
