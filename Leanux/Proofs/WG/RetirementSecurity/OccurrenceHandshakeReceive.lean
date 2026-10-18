import Leanux.Proofs.WG.RetirementSecurity.OccurrenceReadyFrames
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker

/-! Native handshake worker transport, including under-load cookie replies,
response-driven keepalive staging and the real final peer-reference release. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack

theorem send_call (call : HandshakeSendCall) :
    Preserves (Ready locals active) call.original := by
  apply RxPollOccurrences.join call.erases call.allocation
  cases call with
  | buffer pid msg => exact occurrences_queueContents (buffer_wire pid msg) (buffer_contents pid msg)
  | sessionDerived pid => exact occurrences_queueContents (derived_wire pid) (derived_contents pid)
  | initiated pid => exact occurrences_queueContents (initiated_wire pid) (initiated_contents pid)
  | initiation pid => exact occurrences_queueContents (send_initiation_wire pid) (send_initiation_contents pid)
  | response pid => exact occurrences_queueContents (send_response_wire pid) (send_response_contents pid)
  | worker pid => exact occurrences_queueContents (send_worker_wire pid) (send_worker_contents pid)

theorem endpoint_wire (pid : PeerId) (src : SkbSource) :
    SameView txCryptWire (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (cryptWire_store (endpointFromSkb_sameWGStore _)).wp (· = initial))
    | (rx_retention_head setPeerEndpoint; exact (endpoint_cryptWire _ _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem endpoint_contents (pid : PeerId) (src : SkbSource) :
    SameView txQueueContents (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact ((endpointFromSkb_sameWGStore _).of_factor
        (fun s => txQueueContents {dev:=s.dev}) txQueueContents (fun _ => rfl)).wp (· = initial))
    | (rx_retention_head setPeerEndpoint; exact (contents_factor (ownership_queues (endpoint_ownership _ _))).wp (· = initial))
    | occurrence_handshake_contents initial

theorem endpoint (pid : PeerId) (src : SkbSource) :
    Preserves (Ready locals active) (setPeerEndpointFromSkb pid src) :=
  RxPollOccurrences.join (HandshakeReceiveCall.erases (.endpoint pid src))
    (HandshakeReceiveCall.allocation (.endpoint pid src))
    (occurrences_queueContents (endpoint_wire pid src) (endpoint_contents pid src))

theorem cookie_reply (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready locals active) (sendHandshakeCookie msg src) := by
  apply RxPollOccurrences.join (HandshakeReceiveCall.erases (.cookie msg src))
    (HandshakeReceiveCall.allocation (.cookie msg src))
  apply occurrence_passive
  · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => txCryptWire {dev:=s.1}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
        Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
  · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => handoffTxView {dev:=s.1}) handoffTxView
      (fun w => by funext pid; simp [handoffTxView,Cookies.noiseView,Cookies.viewOfStore,
        Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def])

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Ready locals active) (timersHandshakeComplete pid site) :=
  RxPollOccurrences.join (timersHandshakeCompletePrefix_erases pid site)
    (AmbientContracts.drop (timersHandshakeCompletePrefix_spec allocationAmbient (fun _ => True) pid site))
    (occurrence_passive (handshakeComplete_cryptWire pid site)
      (ownership_queues (handshakeComplete_ownership pid site)))

theorem del (pid : PeerId) (timer : PeerTimer) :
    Preserves (Ready locals active) (delTimer pid timer) :=
  RxPollOccurrences.join (delTimerPrefix_erases pid timer)
    (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) pid timer))
    (occurrence_passive (delTimer_cryptWire pid timer) (ownership_queues (delTimer_ownership pid timer)))

theorem traversal (pid : PeerId) : Preserves (Ready locals active) (timersTraversal pid) :=
  RxPollOccurrences.join (timersTraversalPrefix_erases pid)
    (AmbientContracts.drop (timersTraversalPrefix_spec allocationAmbient (fun _ => True) pid))
    (occurrence_passive (timersTraversal_cryptWire pid) (ownership_queues (timersTraversal_ownership pid)))

theorem cookie_frame {action : WG.M α} (same : SameCookie action) :
    Preserves (Ready locals active) action := by
  have wire : SameView txCryptWire action := same.of_factor
    (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
    (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,cookieView,
      cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
  have queues : SameView handoffTxView action := same.of_factor
    (fun s : WGOwnedView => handoffTxView {dev:=s.dev}) handoffTxView
    (fun w => by funext pid; simp [handoffTxView,cookieView,cookieDevice,wgOwnedView,
      wgStoreView,Option.bind_map,Function.comp_def])
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨h,allocated⟩ := before.1
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨⟨h,allocationCookieStable h w v (congrArg WGOwnedView.toWGStoreView view) allocated⟩,
    (hoare_iff_run_ambient _ _ _).mp (occurrence_passive wire queues) w a result v b before.2 run⟩

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (Ready locals active) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact call (.consumeInitiation _))
    | (rx_retention_head consumeResponse; exact call (.consumeResponse _))
    | (rx_retention_head sendHandshakeResponse; exact send_call (.response _))
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact send_call (.sessionDerived _))
    | (rx_retention_head timersHandshakeComplete; exact handshake_complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del _ _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head peerPut; exact RxPollOccurrences.peer_put _)
    | occurrence_ready_step

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready locals active) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume
       exact RxPollOccurrences.join (cookieMessageConsumePrefix_erases _)
         (cookieMessageConsumePrefix_preserves allocationAmbient _)
         (occurrences_queueContents (cookie_consume_wire _) (cookie_consume_contents _)))
    | (rx_retention_head Cookies.loadPhase; exact RxPollOccurrences.store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact after_mac _ _ _ _)
    | occurrence_ready_step

theorem receive_step : Preserves (Ready locals active) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | occurrence_ready_step

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
