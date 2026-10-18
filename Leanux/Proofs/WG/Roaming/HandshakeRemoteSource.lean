import Leanux.Proofs.WG.Roaming.HandshakeRemoteProductClaims
import Leanux.Proofs.WG.Roaming.HandshakeRemoteOtherFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

namespace Product

def observedHandshakeRemotes (msg : List UInt8) (src : SkbSource) :
    Leanux.M HandshakeRemoteReceipt := do
  if messageType msg = MESSAGE_HANDSHAKE_INITIATION then
    return .initiation (← observedInitiationHandshake msg src)
  else if messageType msg = MESSAGE_HANDSHAKE_RESPONSE then
    return .response (← observedResponseHandshake msg src)
  else
    liftWG (receiveHandshakePacket msg src)
    return .other

theorem observedHandshakeRemotes_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedHandshakeRemotes msg src; pure ()) =
      liftWG (receiveHandshakePacket msg src) := by
  unfold observedHandshakeRemotes
  split
  · simpa only [bind_assoc,pure_bind] using observedInitiationHandshake_erase msg src
  · split
    · simpa only [bind_assoc,pure_bind] using observedResponseHandshake_erase msg src
    · simp only [bind_assoc,pure_bind]
      change (liftWG (receiveHandshakePacket msg src) >>= fun x => pure x) = _
      exact bind_pure _


end Product

end Leanux.Proofs.WG.Roaming
