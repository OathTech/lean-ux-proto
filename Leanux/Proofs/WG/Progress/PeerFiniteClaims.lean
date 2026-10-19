import Leanux.Proofs.WG.Progress.PeerCreationFiniteCoreSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PeerFinite
open Leanux Leanux.WG

/-- Exact finite precomputation for all entries, including absent peers,
no identity, null curve output and original Stops. -/
theorem original_precompute_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.precomputeStaticStatic pid) (precompute pid) := by
  rw [precompute_source]
  intro g ambient pre
  rfl

/-- Identity installation agrees on every entry and arbitrary private bytes. -/
theorem original_setPrivate_finite (key : Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.setStaticIdentityPrivateKey key) (setPrivate key) := by
  rw [setPrivate_source]
  intro g ambient pre
  rfl

/-- Entry-word/PSK initialization and precomputation retain the same outcome. -/
theorem original_handshakeInit_finite (pid : PeerId) (psk : Option Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.handshakeInit pid psk) (handshakeInit pid psk) := by
  rw [handshakeInit_source]
  intro g ambient pre
  rfl

/-- Full peer creation agrees without assuming allocation success, room in the
device, identity presence, or any successful source return. -/
theorem original_create_finite (key : Key) (psk : Option Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.peerCreate key psk) (create key psk) := by
  rw [create_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.PeerFinite
