import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueSend
import Leanux.Proofs.WG.Queues.RxRingHandshake

/-! Native Noise, session, cookie and reply operations retain the handshake
ring. Actual worker pops are proved separately with their selected input. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem cookie_frame {a : Leanux.M α} (ha : SameView productCookieView a) : SameView productView a := by
  apply ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map fun d => d.handshakeQueue)
    productView
  intro w
  simp only [productCookieView, cookieStoreView, cookieView, wgOwnedView,
    wgStoreView, cookieDevice, productView, view, Option.map_map, Function.comp_def]

theorem cookie_native_frame {a : WG.M α} (ha : SameCookie a) : SameView view a := by
  apply ha.of_factor (fun store : WGOwnedView => store.dev.map fun d => d.handshakeQueue)
    view
  intro w
  simp only [cookieView, wgOwnedView, wgStoreView, cookieDevice, view,
    Option.map_map, Function.comp_def]

theorem pubkeyLookup_cell key : SameView view (pubkeyLookup key) := by
  handshake_cell_source [pubkeyLookup] using [peerGetMaybeZero_frame]

theorem consumeInitiation_cell msg : SameView view (consumeInitiation msg) := by
  have h_eph := fun b e ck h => show SameView view _ from ((messageEphemeral_sameWGWorld b e ck h).factor view)
  have h_dh := fun b ck p q => show SameView view _ from ((mixDh_sameWGWorld b ck p q).factor view)
  have h_pre := fun ck p => show SameView view _ from ((mixPrecomputedDh_sameWGWorld ck p).factor view)
  have h_dec := fun a k h => show SameView view _ from ((messageDecrypt_sameWGWorld a k h).factor view)
  handshake_cell_source [consumeInitiation] using [peerPut_frame, h_eph, h_dh, h_pre, h_dec, pubkeyLookup_cell]

theorem consumeResponse_cell msg : SameView view (consumeResponse msg) := by
  have h_eph := fun b e ck h => show SameView view _ from ((messageEphemeral_sameWGWorld b e ck h).factor view)
  have h_dh := fun b ck p q => show SameView view _ from ((mixDh_sameWGWorld b ck p q).factor view)
  have h_dec := fun a k h => show SameView view _ from ((messageDecrypt_sameWGWorld a k h).factor view)
  have h_kdf := fun b c ck d => show SameView view _ from ((Framing.kdf_sameWGWorld b c ck d).factor view)
  have h_out := fun xs i => show SameView view _ from ((Framing.kdfOut_sameWGWorld xs i).factor view)
  handshake_cell_source [consumeResponse] using [peerPut_frame, indexLookup_frame, h_eph, h_dh, h_dec, h_kdf, h_out]

theorem createResponse_cell pid : SameView view (createResponse pid) := by
  have h_pub := fun k => show SameView view _ from ((generatePublic_sameWGWorld k).factor view)
  have h_eph := fun b e ck h => show SameView view _ from ((messageEphemeral_sameWGWorld b e ck h).factor view)
  have h_dh := fun b ck p q => show SameView view _ from ((mixDh_sameWGWorld b ck p q).factor view)
  have h_kdf := fun b c ck d => show SameView view _ from ((Framing.kdf_sameWGWorld b c ck d).factor view)
  have h_out := fun xs i => show SameView view _ from ((Framing.kdfOut_sameWGWorld xs i).factor view)
  handshake_cell_source [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [h_pub, h_eph, h_dh, h_kdf, h_out]

theorem addMacToPacket_cell pid msg : SameView view (addMacToPacket pid msg) := by
  have h_exp := fun d b n f => show SameView view _ from ((branchExpired_sameWGWorld d b n f).factor view)
  handshake_cell_source [addMacToPacket] using [h_exp]

theorem keypairCreate_cell pid : SameView view (keypairCreate pid) := by
  handshake_cell_source [keypairCreate] using [setKeypair_cell]

theorem addNewKeypair_cell pid kp : SameView view (addNewKeypair pid kp) := by
  handshake_cell_source [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_frame]

theorem deriveKeys_cell kp initiator ck : SameView view (deriveKeys kp initiator ck) := by
  have h_kdf := fun b c ck d => show SameView view _ from ((Framing.kdf_sameWGWorld b c ck d).factor view)
  have h_out := fun xs i => show SameView view _ from ((Framing.kdfOut_sameWGWorld xs i).factor view)
  handshake_cell_source [deriveKeys] using [setKeypair_cell, h_kdf, h_out]

theorem handshakeZero_cell pid : SameView view (handshakeZero pid) := by
  handshake_cell_source [handshakeZero] using []

theorem beginSession_cell pid : SameView view (beginSession pid) := by
  handshake_cell_source [beginSession] using [setKeypair_cell, keypairCreate_cell, deriveKeys_cell, handshakeZero_cell, addNewKeypair_cell]

theorem timersSessionDerived_cell pid : SameView view (timersSessionDerived pid) := by
  handshake_cell_source [timersSessionDerived] using [modPeerTimer_cell]

theorem sendBufferToPeer_cell pid bytes : SameView view (sendBufferToPeer pid bytes) := by
  handshake_cell_source [sendBufferToPeer] using [send4_cell, send6_cell]

theorem sendHandshakeResponse_cell pid : SameView view (sendHandshakeResponse pid) := by
  handshake_cell_source [sendHandshakeResponse] using [createResponse_cell, addMacToPacket_cell, beginSession_cell, timersSessionDerived_cell, timersTraversal_cell, timersAnyAuthenticatedPacketSent_cell, sendBufferToPeer_cell]

theorem setPeerEndpointFromSkb_cell pid src : SameView view (setPeerEndpointFromSkb pid src) := by
  have h_ep := fun src => show SameView view _ from (kernel (endpointFromSkb_sameWGStore src))
  handshake_cell_source [setPeerEndpointFromSkb] using [h_ep, setPeerEndpoint_cell]

theorem sendKeepalive_cell pid : SameView view (sendKeepalive pid) := by
  handshake_cell_source [sendKeepalive] using [sendStagedPackets_cell]

theorem cookieMessageConsume_cell msg : SameView view (cookieMessageConsume msg) := by
  handshake_cell_source [cookieMessageConsume] using [peerPut_frame, indexLookup_frame]

theorem sendBufferAsReplyToSkb_cell src bytes : SameView view (sendBufferAsReplyToSkb src bytes) := by
  have h_ep := fun src => show SameView view _ from (kernel (endpointFromSkb_sameWGStore src))
  handshake_cell_source [sendBufferAsReplyToSkb] using [h_ep, send4_cell, send6_cell]

theorem sendHandshakeCookie_cell msg src : SameView view (sendHandshakeCookie msg src) := by
  have h_cookie := fun i src mac => show SameView view _ from (cookie_native_frame (cookieMessageCreate_sameCookie i src mac))
  handshake_cell_source [sendHandshakeCookie] using [h_cookie, sendBufferAsReplyToSkb_cell]

private theorem afterMac_cell msg src loaded mac : SameView view (Cookies.afterMac msg src loaded mac) := by
  handshake_cell_source [Cookies.afterMac] using [peerPut_frame, sendHandshakeCookie_cell, consumeInitiation_cell, consumeResponse_cell, setPeerEndpointFromSkb_cell, sendHandshakeResponse_cell, beginSession_cell, timersSessionDerived_cell, timersHandshakeComplete_cell, sendKeepalive_cell, timersAnyAuthenticatedPacketReceived_cell, timersTraversal_cell]

theorem receiveHandshakePacket_cell msg src : SameView view (receiveHandshakePacket msg src) := by
  have loaded : SameView view Cookies.loadPhase := kernel Cookies.loadPhase_sameStore
  have validate := fun loaded => cookie_native_frame (cookieValidatePacket_sameCookie msg src loaded)
  rw [Cookies.receive_factor]
  handshake_cell_source [] using [cookieMessageConsume_cell, loaded, validate, afterMac_cell]


end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
