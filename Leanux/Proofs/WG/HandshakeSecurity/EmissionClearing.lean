import Leanux.Proofs.WG.HandshakeSecurity.EmissionConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionCompletionFrames

/-! Key clearing and the clear-work leaf preserve pending datagrams. The
send-work drain itself is deliberately outside these leaf contracts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EmissionClearing
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open AuthenticatedEffects TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem handshake (pid : PeerId) : SameView WGWorld.sent (handshakeClear pid) := by
  sent_frame [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,handshakeZero] using
    [getPeer_sent_spec,setPeer_sent_spec,index_sent_spec]

theorem handshake_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (handshakeClear pid) := (handshake pid).wp P

theorem keypairs (pid : PeerId) : SameView WGWorld.sent (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec,EmissionFrames.keypair_put_spec]

theorem keypairs_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (keypairsClear pid) := (keypairs pid).wp P

theorem expire (pid : PeerId) : SameView WGWorld.sent (expireCurrentPeerKeypairs pid) := by
  sent_frame [expireCurrentPeerKeypairs,requireNotPending] using
    [handshake_spec,EmissionConfiguration.reset_handshake_spec,getPeer_sent_spec,getKeypair_sent_spec,setKeypair_sent_spec]

theorem queued_clear (pid : PeerId) : SameView WGWorld.sent (queuedExpiredZeroKeyMaterial pid) := by
  sent_frame [queuedExpiredZeroKeyMaterial] using [handshake_spec,keypairs_spec,peerPut_sent_spec]

theorem queued_clear_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (queuedExpiredZeroKeyMaterial pid) := (queued_clear pid).wp P

theorem clear_work (pid : PeerId) : SameView WGWorld.sent (runFlushedClearWork pid) := by
  sent_frame [runFlushedClearWork] using [queued_clear_spec]

end Leanux.Proofs.WG.HandshakeSecurity.EmissionClearing
