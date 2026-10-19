import Leanux.Proofs.WG.HandshakeSecurity.EmissionAllowedIps
import Leanux.Proofs.WG.TransmitSecurity.EmissionCleanupFrames

/-! Native send-free configuration leaves. Whole set-device, removal and
lifecycle calls remain callback-parametric because their drains can send. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EmissionConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open AuthenticatedEffects TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem precompute (pid : PeerId) : SameView WGWorld.sent (precomputeStaticStatic pid) := by
  sent_frame [precomputeStaticStatic,requireNotPending] using [getPeer_sent_spec,setPeer_sent_spec]

theorem precompute_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (precomputeStaticStatic pid) := (precompute pid).wp P

theorem static_identity (key : Key) : SameView WGWorld.sent (setStaticIdentityPrivateKey key) := by
  sent_frame [setStaticIdentityPrivateKey,requireNotPending,generatePublic] using [EmissionDump.list_spec]

theorem cookie_keys : SameView WGWorld.sent cookiePrecomputeDeviceKeys := by
  sent_frame [cookiePrecomputeDeviceKeys] using []

theorem handshake_init (pid : PeerId) (psk : Option Key) : SameView WGWorld.sent (handshakeInit pid psk) := by
  sent_frame [handshakeInit,IndexOwner.setPeerWord] using [getPeer_sent_spec,setPeer_sent_spec,precompute_spec]

theorem handshake_init_spec (P : List SentDatagram → Prop) (pid : PeerId) (psk : Option Key) :
    Preserves (fun w => P w.sent) (handshakeInit pid psk) := (handshake_init pid psk).wp P

theorem reset_handshake (pid : PeerId) : SameView WGWorld.sent (resetLastSentHandshake pid) := by
  sent_frame [resetLastSentHandshake] using [getPeer_sent_spec,setPeer_sent_spec]

theorem reset_handshake_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (resetLastSentHandshake pid) := (reset_handshake pid).wp P

theorem peer_create (key : Key) (psk : Option Key) : SameView WGWorld.sent (peerCreate key psk) := by
  sent_frame [peerCreate,dstCacheReset,getAmbient,hiddenJiffies] using
    [getPeer_sent_spec,setPeer_sent_spec,handshake_init_spec,reset_handshake_spec]

theorem socket (port : Nat) : SameView WGWorld.sent (socketInit port) := by
  sent_frame [socketInit,Leanux.iputReport] using [EmissionCleanup.reinit_spec]

theorem socket_spec (P : List SentDatagram → Prop) (port : Nat) :
    Preserves (fun w => P w.sent) (socketInit port) := (socket port).wp P

theorem port (port : Nat) : SameView WGWorld.sent (setPort port) := by
  sent_frame [setPort] using [EmissionCleanup.endpoint_spec,socket_spec,EmissionDump.list_spec]

theorem make_dead (pid : PeerId) : SameView WGWorld.sent (peerMakeDead pid) := by
  sent_frame [peerMakeDead] using [EmissionAllowedIps.remove_peer_spec,getPeer_sent_spec,setPeer_sent_spec]

end Leanux.Proofs.WG.HandshakeSecurity.EmissionConfiguration
