import Leanux.Proofs.WG.Queues.TxLiveRemoval
import Leanux.Proofs.WG.Queues.TxLiveRxCompletion
import Leanux.Proofs.WG.Queues.HandshakeSlots
import Leanux.Proofs.WG.Cookies.Frames

/-! The actual handshake receiver preserves the live TX frontier. Session
construction and response keepalives use their native contracts; acquisition
failure, authentication failure payments, allocation refusal and Stops retain
their source domains. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open RxCredits

theorem maybe_get (peer : Option PeerId) : Preserves Ready (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZero refcountIncNotZero requireNotPending
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' live_socket_step

theorem owner_word (owner : IndexOwner) (peer : Option PeerId) : Preserves Ready (owner.setPeerWord peer) := by
  cases owner <;> unfold IndexOwner.setPeerWord
  all_goals repeat' live_socket_step

private theorem acquire_owner (owner : IndexOwner) : Preserves Ready (Affiliation.acquireOwner owner) :=
  preserves_bind (indexOwner_peerWord_preserves owner Ready) (fun peer =>
    preserves_bind (maybe_get peer) (fun taken =>
      preserves_bind (owner_word owner taken) (fun _ => preserves_pure _)))

theorem index_lookup (kinds : List IndexKind) (index : Nat) : Preserves Ready (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_owner _)
    | (rx_retention_head liftIndex
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveSend.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.index_ready) _)
    | live_socket_step

theorem pubkey_lookup (key : Key) : Preserves Ready (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact maybe_get _)
    | live_socket_step

private theorem initiation_out (peer ret : Option PeerId) :
    Preserves Ready (HandshakeLoans.initiationOut peer ret) := by
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' live_socket_step

private theorem initiation_tail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) :
    Preserves Ready (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | receive_crypto Ready
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | live_socket_step

private theorem initiation_lookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Preserves Ready (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationTail; exact initiation_tail _ _ _ _ _ _)
    | live_socket_step

theorem consume_initiation (msg : List UInt8) : Preserves Ready (consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact initiation_lookup _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
    | receive_crypto Ready
    | live_socket_step

private theorem response_tail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Preserves Ready (HandshakeLoans.responseTail msg identity pid) := by
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first | receive_crypto Ready | live_socket_step

theorem consume_response (msg : List UInt8) : Preserves Ready (consumeResponse msg) := by
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact response_tail _ _ _)
    | (rx_retention_head indexLookup; exact index_lookup _ _)
    | live_socket_step

theorem cookie_consume (msg : List UInt8) : Preserves Ready (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact index_lookup _ _)
    | live_socket_step

private theorem cookie_ready {action : WG.M α} (same : SameCookie action) : Preserves Ready action :=
  fields_ready (same.of_factor
    (fun k : WGOwnedView => k.dev.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def]))

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves Ready (sendHandshakeCookie msg src) :=
  fields_ready ((Cookies.sendHandshakeCookie_frame msg src).of_factor
    (fun k : Option Device × Nat × Nat => k.1.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Function.comp_def]))

theorem endpoint_from_skb (pid : PeerId) (src : SkbSource) : Preserves Ready (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store_ready _ (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveRxCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveRx.endpoint_ready) _ _)
    | live_socket_step

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves Ready (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact consume_initiation _)
    | (rx_retention_head consumeResponse; exact consume_response _)
    | (rx_retention_head sendHandshakeResponse; exact send_response _)
    | (rx_retention_head beginSession; exact begin_session _)
    | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_from_skb _ _)
    | (rx_retention_head timersSessionDerived; exact session_derived _)
    | (rx_retention_head timersHandshakeComplete; exact handshake_complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact authenticated_received _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | live_socket_step

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves Ready (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact cookie_consume _)
    | (rx_retention_head Cookies.loadPhase; exact store_ready _ Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie_ready (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact after_mac _ _ _ _)
    | live_socket_step

theorem receive_step : Preserves Ready WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | live_socket_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
