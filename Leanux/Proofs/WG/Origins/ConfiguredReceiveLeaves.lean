import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.Peers.ConfiguredTimers

/-! Concrete configured-cell frames for the remaining receive-side timers,
endpoint updates and cookie replies. Only fields actually absent from the
configured identity projection are omitted; all records and Stops remain. -/
namespace Leanux.Proofs.WG.ConfiguredReceiveLeaves
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredIdentity ConfiguredHandshake

theorem timersSessionDerived_view (pid : PeerId) :
    SameView view (timersSessionDerived pid) :=
  (modPeerTimer_view .timerJiffiesSessionDerived pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())

theorem timersAnyAuthenticatedPacketReceived_view (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketReceived pid) :=
  delTimer_view pid .newHandshake

theorem timersHandshakeComplete_view (pid : PeerId) (site : HiddenSite) :
    SameView view (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s = initial))
    | configured_step initial

theorem timersDataReceived_view (pid : PeerId) :
    SameView view (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head discard
       exact ((modPeerTimer_view .timerJiffiesDataReceived pid .sendKeepalive
         KEEPALIVE_TIMEOUT_TICKS).map (fun _ => ())).wp (fun s => s = initial))
    | (rx_retention_head modPeerTimer; exact (modPeerTimer_view _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

theorem setPeerEndpoint_view (pid : PeerId) (endpoint : Endpoint) :
    SameView view (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold setPeerEndpoint endpointEq WG.andM
  simp (config := {zeta := false}) only [requireNotPending,branch,pure_bind]
  repeat' first
    | (rx_retention_head dstCacheReset; exact (ConfiguredIdentity.cacheReset _).wp (fun s => s = initial))
    | configured_step initial

theorem setPeerEndpointFromSkb_view (pid : PeerId) (src : SkbSource) :
    SameView view (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (ConfiguredIdentity.sameWG (project := id) (endpointFromSkb_sameWGStore _)).wp (fun s => s = initial))
    | (rx_retention_head setPeerEndpoint; exact (setPeerEndpoint_view _ _).wp (fun s => s = initial))
    | configured_step initial

theorem sendBufferAsReplyToSkb_view (src : SkbSource) (bytes : List UInt8) :
    SameView view (sendBufferAsReplyToSkb src bytes) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (ConfiguredIdentity.sameWG (project := id) (endpointFromSkb_sameWGStore _)).wp (fun s => s = initial))
    | (rx_retention_head send4; exact (send4_view _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_view _ _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

theorem cookieMessageCreate_view (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    SameView view (cookieMessageCreate index src mac1) := by
  apply (cookieMessageCreate_sameCookie index src mac1).of_factor
    (fun s : WGOwnedView => s.dev.map state) view
  intro w
  simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,view,state,
    Option.map_map,Function.comp_def]
  rfl

theorem sendHandshakeCookie_view (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact SameView.bind (cookieMessageCreate_view _ _ _)
    (fun bytes => sendBufferAsReplyToSkb_view src bytes)

end Leanux.Proofs.WG.ConfiguredReceiveLeaves
