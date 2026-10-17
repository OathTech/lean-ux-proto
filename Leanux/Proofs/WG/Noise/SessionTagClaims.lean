import Leanux.Proofs.WG.Noise.SessionTagSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Actual successful sessions zero only their peer; normal false returns
retain every tag. The accepted old tag is derived from actual execution. -/
theorem beginSession_tagMap_projected (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (beginSession pid) (fun s => s = entry)
      (fun ok after => (∀target, after.tagAt target =
        if ok then if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target
        else entry.tagAt target) ∧
        (ok = true → entry.tagAt pid = some HANDSHAKE_CREATED_RESPONSE ∨
          entry.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE)) := by
  intro g ambient ok final after pre run
  rw [← pre]
  exact beginSession_tagMap pid g.dev g ambient ok final after rfl run

/-- All peer tags at the original handshake-clear boundary. -/
theorem handshakeClear_tagMap_projected (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (handshakeClear pid) (fun s => s = entry)
      (fun _ after => ∀target, after.tagAt target =
        if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) := by
  intro g ambient result final after pre run
  rw [← pre]
  exact handshakeClear_tagMap pid g.dev g ambient result final after rfl run

/-- All peer tags after the original whole expiry operation. -/
theorem expireCurrentPeerKeypairs_tagMap_projected (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun s => s = entry)
      (fun _ after => ∀target, after.tagAt target =
        if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) := by
  intro g ambient result final after pre run
  rw [← pre]
  exact expireCurrentPeerKeypairs_tagMap pid g.dev g ambient result final after rfl run

end Leanux.Proofs.WG.Noise
