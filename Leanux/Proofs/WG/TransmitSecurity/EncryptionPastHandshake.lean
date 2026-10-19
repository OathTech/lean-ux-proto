import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastHandshakeFrames

/-! Full native handshake receive preserves historical encryption exclusion
through authentication, session creation, keepalive staging and failure cleanup.
Only the stated incoming carrier is assumed; no authenticity premise is needed
for this frame property. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition Keys Socket Maintenance RxCredits
set_option maxHeartbeats 600000

theorem pubkey_lookup (key : Key) : Preserves (Ready past active) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact ready_maybe_get _)
    | encryption_past_handshake_step

private theorem initiation_out (peer ret : Option PeerId) :
    Preserves (Ready past active) (HandshakeLoans.initiationOut peer ret) := by
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_handshake_step

private theorem initiation_tail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Ready past active) (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | receive_crypto (Ready past active)
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | encryption_past_handshake_step

private theorem initiation_lookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Preserves (Ready past active) (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationTail; exact initiation_tail _ _ _ _ _ _)
    | encryption_past_handshake_step

theorem consume_initiation (msg : List UInt8) : Preserves (Ready past active) (consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact initiation_lookup _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
    | receive_crypto (Ready past active)
    | encryption_past_handshake_step

private theorem response_tail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Preserves (Ready past active) (HandshakeLoans.responseTail msg identity pid) := by
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first | receive_crypto (Ready past active) | encryption_past_handshake_step

theorem consume_response (msg : List UInt8) : Preserves (Ready past active) (consumeResponse msg) := by
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact response_tail _ _ _)
    | (rx_retention_head indexLookup; exact ready_index_lookup _ _)
    | encryption_past_handshake_step

theorem cookie_consume (msg : List UInt8) : Preserves (Ready past active) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact ready_index_lookup _ _)
    | encryption_past_handshake_step

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (Ready past active) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact consume_initiation _)
    | (rx_retention_head consumeResponse; exact consume_response _)
    | (rx_retention_head sendHandshakeResponse; exact send_response _)
    | (rx_retention_head beginSession; exact begin_session _)
    | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_from_skb _ _)
    | (rx_retention_head timersSessionDerived; exact ready_frame (LiveFrontier.session_derived _) (EncryptionPast.session_derived _))
    | (rx_retention_head timersHandshakeComplete; exact ready_frame (LiveFrontier.handshake_complete _ _) (EncryptionPast.handshake_complete _ _))
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact ready_frame (LiveFrontier.authenticated_received _) (del_timer _ .newHandshake))
    | (rx_retention_head timersTraversal; exact ready_frame (LiveFrontier.traversal _) (EncryptionPast.traversal _))
    | encryption_past_handshake_step

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (Ready past active) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact cookie_consume _)
    | (rx_retention_head Cookies.loadPhase; exact ready_store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie_ready (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact after_mac _ _ _ _)
    | encryption_past_handshake_step

theorem receive_step : Preserves (Ready past active) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | encryption_past_handshake_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Handshake
