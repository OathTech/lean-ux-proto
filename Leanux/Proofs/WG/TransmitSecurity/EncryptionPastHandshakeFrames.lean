import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastMaintenance

/-! Cookie and endpoint frames for the historical packet projection. The cookie
mask omits secret/rate-limit fields only; device epoch and TX work remain visible. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition Keys Socket Maintenance
set_option maxHeartbeats 600000

theorem cookie_ready {action : WG.M α} (same : SameCookie action) :
    Preserves (Ready past active) action := by
  apply ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveHandshake.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.cookie_ready) same)
  exact same.of_factor (fun k : WGOwnedView =>
    (⟨k.netIfindexNext,k.dev.map fun d => ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩⟩ : View))
    view (fun w => by simp only [view,cookieView,cookieDevice,wgOwnedView,wgStoreView,
      Option.map_map,Function.comp_def])

theorem reply_buffer (src : SkbSource) (bytes : List UInt8) :
    Preserves (Ready past active) (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact ready_store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head send4; exact socket4 _ _ _ _ _)
    | (rx_retention_head send6; exact socket6 _ _ _ _ _)
    | encryption_past_socket_step

theorem cookie_reply (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready past active) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact preserves_bind (cookie_ready (cookieMessageCreate_sameCookie _ _ _))
    (fun _ => reply_buffer _ _)

theorem endpoint_from_skb (pid : PeerId) (src : SkbSource) :
    Preserves (Ready past active) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact ready_store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact ready_endpoint _ _)
    | encryption_past_socket_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Handshake
