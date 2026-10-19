import Leanux.Proofs.WG.RetirementSecurity.TxCoverageTimers

/-! Complete native handshake receive and send actors preserve converse TX
ownership; response keepalives use the same original allocation path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
variable {locals : List TxLocalBatch}

theorem call (call : HandshakeCall) : Preserves (TxCoverage locals) call.original := by
  cases call with
  | createInitiation pid => exact create_initiation pid
  | createResponse pid => exact create_response pid
  | consumeInitiation msg => exact consume_initiation msg
  | consumeResponse msg => exact consume_response msg
  | addMac pid msg => exact add_mac pid msg

theorem send_call (call : HandshakeSendCall) : Preserves (TxCoverage locals) call.original := by
  cases call with
  | buffer pid msg => exact send_buffer pid msg
  | sessionDerived pid => exact derived pid
  | initiated pid => exact initiated pid
  | initiation pid => exact send_initiation pid
  | response pid => exact send_response pid
  | worker pid => exact send_worker pid

theorem session_coherent (pid : PeerId) : Preserves (TxCoverage locals) (beginSession pid) :=
  session pid

theorem endpoint (pid : PeerId) (src : SkbSource) :
    Preserves (TxCoverage locals) (setPeerEndpointFromSkb pid src) :=
  contents_wire (OccurrenceHandshake.endpoint_contents pid src) (OccurrenceHandshake.endpoint_wire pid src)

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (TxCoverage locals) (timersHandshakeComplete pid site) :=
  maintenance (.handshakeComplete pid site)

theorem del (pid : PeerId) (timer : PeerTimer) : Preserves (TxCoverage locals) (delTimer pid timer) :=
  maintenance (.deleteTimer pid timer)

theorem traversal (pid : PeerId) : Preserves (TxCoverage locals) (timersTraversal pid) :=
  maintenance (.traversal pid)

theorem cookie_reply (msg : List UInt8) (src : SkbSource) :
    Preserves (TxCoverage locals) (sendHandshakeCookie msg src) := by
  apply wire
  · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => handoffTxView {dev:=s.1}) handoffTxView
      (fun w => by funext pid; simp [handoffTxView,Cookies.noiseView,Cookies.viewOfStore,
        Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def])
  · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => txCryptWire {dev:=s.1}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
        Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem cookie_frame {action : WG.M α} (same : SameCookie action) :
    Preserves (TxCoverage locals) action := by
  apply wire
  · exact same.of_factor
      (fun s : WGOwnedView => handoffTxView {dev:=s.dev}) handoffTxView
      (fun w => by funext pid; simp [handoffTxView,cookieView,cookieDevice,wgOwnedView,
        wgStoreView,Option.bind_map,Function.comp_def])
  · exact same.of_factor
      (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,cookieView,
        cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (TxCoverage locals) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact call (.consumeInitiation _))
    | (rx_retention_head consumeResponse; exact call (.consumeResponse _))
    | (rx_retention_head sendHandshakeResponse; exact send_call (.response _))
    | (rx_retention_head beginSession; exact session_coherent _)
    | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact send_call (.sessionDerived _))
    | (rx_retention_head timersHandshakeComplete; exact handshake_complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del _ _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head peerPut; exact peer_put _)
    | coverage_native_step

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves (TxCoverage locals) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact consume_cookie _)
    | (rx_retention_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact after_mac _ _ _ _)
    | coverage_native_step

theorem receive_step : Preserves (TxCoverage locals) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | coverage_native_step

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
