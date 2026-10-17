import Leanux.Proofs.WG.Queues.RxRingTx
import Leanux.Proofs.WG.Lifetimes.CookieAccess
import Leanux.Proofs.WG.Cookies.Gate

/-! The handshake worker never admits transport data. These concrete full
RX-cell frames cover its cookie, Noise, session, reply and TX-staging callees.
Malformed types and every original Stop remain executable source outcomes. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem cookie_frame {a : Leanux.M α} (ha : SameView productCookieView a) : SameView cell a := by
  apply ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
    cell
  intro w
  simp only [productCookieView, cookieStoreView, cookieView, wgOwnedView,
    wgStoreView, cookieDevice, cell, Option.map_map, Function.comp_def]

theorem cookie_native_frame {a : WG.M α} (ha : SameCookie a) : SameView nativeCell a := by
  apply ha.of_factor (fun store : WGOwnedView => store.dev.map fun d => (d.ifindex, d.decryptQueue))
    nativeCell
  intro w
  simp only [cookieView, wgOwnedView, wgStoreView, cookieDevice, nativeCell,
    Option.map_map, Function.comp_def]

theorem pubkeyLookup_cell key : SameView nativeCell (pubkeyLookup key) := by
  ring_cell_source [pubkeyLookup] using [peerGetMaybeZero_frame]

theorem consumeInitiation_cell msg : SameView nativeCell (consumeInitiation msg) := by
  have h_eph := fun b e ck h => show SameView nativeCell _ from ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell)
  have h_dh := fun b ck p q => show SameView nativeCell _ from ((mixDh_sameWGWorld b ck p q).factor nativeCell)
  have h_pre := fun ck p => show SameView nativeCell _ from ((mixPrecomputedDh_sameWGWorld ck p).factor nativeCell)
  have h_dec := fun a k h => show SameView nativeCell _ from ((messageDecrypt_sameWGWorld a k h).factor nativeCell)
  ring_cell_source [consumeInitiation] using [peerPut_frame, h_eph, h_dh, h_pre, h_dec, pubkeyLookup_cell]

theorem consumeResponse_cell msg : SameView nativeCell (consumeResponse msg) := by
  have h_eph := fun b e ck h => show SameView nativeCell _ from ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell)
  have h_dh := fun b ck p q => show SameView nativeCell _ from ((mixDh_sameWGWorld b ck p q).factor nativeCell)
  have h_dec := fun a k h => show SameView nativeCell _ from ((messageDecrypt_sameWGWorld a k h).factor nativeCell)
  have h_kdf := fun b c ck d => show SameView nativeCell _ from ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell)
  have h_out := fun xs i => show SameView nativeCell _ from ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell)
  ring_cell_source [consumeResponse] using [peerPut_frame, indexLookup_frame, h_eph, h_dh, h_dec, h_kdf, h_out]

theorem createResponse_cell pid : SameView nativeCell (createResponse pid) := by
  have h_pub := fun k => show SameView nativeCell _ from ((generatePublic_sameWGWorld k).factor nativeCell)
  have h_eph := fun b e ck h => show SameView nativeCell _ from ((messageEphemeral_sameWGWorld b e ck h).factor nativeCell)
  have h_dh := fun b ck p q => show SameView nativeCell _ from ((mixDh_sameWGWorld b ck p q).factor nativeCell)
  have h_kdf := fun b c ck d => show SameView nativeCell _ from ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell)
  have h_out := fun xs i => show SameView nativeCell _ from ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell)
  ring_cell_source [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [h_pub, h_eph, h_dh, h_kdf, h_out]

theorem addMacToPacket_cell pid msg : SameView nativeCell (addMacToPacket pid msg) := by
  have h_exp := fun d b n f => show SameView nativeCell _ from ((branchExpired_sameWGWorld d b n f).factor nativeCell)
  ring_cell_source [addMacToPacket] using [h_exp]

theorem keypairCreate_cell pid : SameView nativeCell (keypairCreate pid) := by
  ring_cell_source [keypairCreate] using [setKeypair_cell]

theorem addNewKeypair_cell pid kp : SameView nativeCell (addNewKeypair pid kp) := by
  ring_cell_source [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_frame]

theorem deriveKeys_cell kp initiator ck : SameView nativeCell (deriveKeys kp initiator ck) := by
  have h_kdf := fun b c ck d => show SameView nativeCell _ from ((Framing.kdf_sameWGWorld b c ck d).factor nativeCell)
  have h_out := fun xs i => show SameView nativeCell _ from ((Framing.kdfOut_sameWGWorld xs i).factor nativeCell)
  ring_cell_source [deriveKeys] using [setKeypair_cell, h_kdf, h_out]

theorem handshakeZero_cell pid : SameView nativeCell (handshakeZero pid) := by
  ring_cell_source [handshakeZero] using []

theorem beginSession_cell pid : SameView nativeCell (beginSession pid) := by
  ring_cell_source [beginSession] using [setKeypair_cell, keypairCreate_cell, deriveKeys_cell, handshakeZero_cell, addNewKeypair_cell]

theorem timersSessionDerived_cell pid : SameView nativeCell (timersSessionDerived pid) := by
  ring_cell_source [timersSessionDerived] using [modPeerTimer_cell]

theorem sendBufferToPeer_cell pid bytes : SameView nativeCell (sendBufferToPeer pid bytes) := by
  ring_cell_source [sendBufferToPeer] using [send4_cell, send6_cell]

theorem sendHandshakeResponse_cell pid : SameView nativeCell (sendHandshakeResponse pid) := by
  ring_cell_source [sendHandshakeResponse] using [createResponse_cell, addMacToPacket_cell, beginSession_cell, timersSessionDerived_cell, timersTraversal_cell, timersAnyAuthenticatedPacketSent_cell, sendBufferToPeer_cell]

theorem setPeerEndpointFromSkb_cell pid src : SameView nativeCell (setPeerEndpointFromSkb pid src) := by
  have h_ep := fun src => show SameView nativeCell _ from (kernel (endpointFromSkb_sameWGStore src))
  ring_cell_source [setPeerEndpointFromSkb] using [h_ep, setPeerEndpoint_cell]

theorem sendKeepalive_cell pid : SameView nativeCell (sendKeepalive pid) := by
  ring_cell_source [sendKeepalive] using [sendStagedPackets_cell]

theorem cookieMessageConsume_cell msg : SameView nativeCell (cookieMessageConsume msg) := by
  ring_cell_source [cookieMessageConsume] using [peerPut_frame, indexLookup_frame]

theorem sendBufferAsReplyToSkb_cell src bytes : SameView nativeCell (sendBufferAsReplyToSkb src bytes) := by
  have h_ep := fun src => show SameView nativeCell _ from (kernel (endpointFromSkb_sameWGStore src))
  ring_cell_source [sendBufferAsReplyToSkb] using [h_ep, send4_cell, send6_cell]

theorem sendHandshakeCookie_cell msg src : SameView nativeCell (sendHandshakeCookie msg src) := by
  have h_cookie := fun i src mac => show SameView nativeCell _ from (cookie_native_frame (cookieMessageCreate_sameCookie i src mac))
  ring_cell_source [sendHandshakeCookie] using [h_cookie, sendBufferAsReplyToSkb_cell]

private theorem afterMac_cell msg src loaded mac : SameView nativeCell (Cookies.afterMac msg src loaded mac) := by
  ring_cell_source [Cookies.afterMac] using [peerPut_frame, sendHandshakeCookie_cell, consumeInitiation_cell, consumeResponse_cell, setPeerEndpointFromSkb_cell, sendHandshakeResponse_cell, beginSession_cell, timersSessionDerived_cell, timersHandshakeComplete_cell, sendKeepalive_cell, timersAnyAuthenticatedPacketReceived_cell, timersTraversal_cell]

theorem receiveHandshakePacket_cell msg src : SameView nativeCell (receiveHandshakePacket msg src) := by
  have loaded : SameView nativeCell Cookies.loadPhase := kernel Cookies.loadPhase_sameStore
  have validate := fun loaded => cookie_native_frame (cookieValidatePacket_sameCookie msg src loaded)
  rw [Cookies.receive_factor]
  ring_cell_source [] using [cookieMessageConsume_cell, loaded, validate, afterMac_cell]

theorem receiveStep_cell  : SameView nativeCell (receiveStep) := by
  ring_cell_source [receiveStep] using [receiveHandshakePacket_cell]

end Leanux.Proofs.WG.Queues.RxRing
