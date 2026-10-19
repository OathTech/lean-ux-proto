import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueSession
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueIngress
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers

/-! Key retirement, timers and flushed handshake work retain the native
handshake input ring. Peer/key removal is allowed by these queue-only frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
set_option pp.structureInstances false
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem clear_endpoint_cell (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  handshake_cell_source [clearPeerEndpointSrc,dstCacheResetNow] using [dstCacheReset_cell]

theorem purge_cell (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  handshake_cell_source [purgeStagedPackets] using []

theorem key_clear_cell (pid : PeerId) : SameView view (keypairsClear pid) := by
  handshake_cell_source [keypairsClear,_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_frame]

theorem handshake_clear_cell (pid : PeerId) : SameView view (handshakeClear pid) := by
  handshake_cell_source [handshakeClear] using [handshakeZero_cell,requireNotPending_cell]

theorem key_expire_cell (pid : PeerId) : SameView view (expireCurrentPeerKeypairs pid) := by
  handshake_cell_source [expireCurrentPeerKeypairs,resetLastSentHandshake] using [setKeypair_cell,handshake_clear_cell,requireNotPending_cell]

theorem timer_cell (pid : PeerId) (timer : PeerTimer) : SameView view (timerCallback pid timer) := by
  cases timer
  all_goals simp only [timerCallback]
  all_goals simp only [expiredRetransmitHandshake,expiredSendKeepalive,
    expiredNewHandshake,expiredZeroKeyMaterial,expiredSendPersistentKeepalive]
  all_goals handshake_cell_source []
    using [delTimer_cell,modPeerTimer_cell,sendKeepalive_cell,sendQueuedHandshakeInitiation_cell,
      clear_endpoint_cell,purge_cell,peerGet_frame,peerPut_frame]

theorem queued_zero_cell (pid : PeerId) : SameView view (queuedExpiredZeroKeyMaterial pid) := by
  handshake_cell_source [queuedExpiredZeroKeyMaterial] using [handshake_clear_cell,key_clear_cell,peerPut_frame]

theorem createInitiation_cell (pid : PeerId) : SameView view (createInitiation pid) := by
  have pub := fun key=>show SameView view _ from (generatePublic_sameWGWorld key).factor view
  have eph := fun copy e ck h=>show SameView view _ from (messageEphemeral_sameWGWorld copy e ck h).factor view
  have dh := fun key ck priv pub=>show SameView view _ from (mixDh_sameWGWorld key ck priv pub).factor view
  have pre := fun ck key=>show SameView view _ from (mixPrecomputedDh_sameWGWorld ck key).factor view
  handshake_cell_source [createInitiation,_private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [pub,eph,dh,pre]

theorem timersHandshakeInitiated_cell (pid : PeerId) : SameView view (timersHandshakeInitiated pid) := by
  have clock := fun site=>show SameView view _ from (callerJiffies_sameWGWorld site).factor view
  have jitter := fun site=>show SameView view _ from (jitterBelowRekeyTimeout_sameWGWorld site).factor view
  have arm := fun pid timer delay caller=>armTimer_cell pid timer delay caller
  handshake_cell_source [timersHandshakeInitiated] using [clock,jitter,modPeerTimerGuard_cell,arm]

theorem sendInitiation_cell (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  have expired := fun d birth age f=>show SameView view _ from (branchExpired_sameWGWorld d birth age f).factor view
  handshake_cell_source [sendHandshakeInitiation] using [expired,createInitiation_cell,
    timersHandshakeInitiated_cell,addMacToPacket_cell,timersTraversal_cell,timersAnyAuthenticatedPacketSent_cell,sendBufferToPeer_cell]

theorem sendWorker_cell (pid : PeerId) : SameView view (handshakeSendWorker pid) := by
  handshake_cell_source [handshakeSendWorker] using [sendInitiation_cell,peerPut_frame]

theorem flushed_send_cell (pid : PeerId) : SameView view (runFlushedSendWork pid) := by
  handshake_cell_source [runFlushedSendWork] using [sendWorker_cell]

theorem flushed_clear_cell (pid : PeerId) : SameView view (runFlushedClearWork pid) := by
  handshake_cell_source [runFlushedClearWork] using [queued_zero_cell]

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
