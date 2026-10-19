import Leanux.Proofs.WG.RetirementSecurity.TxWorkHandshake

/-! Complete native handshake receive retains fixed TX service obligations,
including response keepalive allocation and final reference cleanup. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem serving_peer_update (pid : PeerId) (f : Peer→Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Serving locals crypt tx) (getPeer pid >>= fun p=>setPeer pid (f p)) := by
  apply serving_join
  · apply passive
    · intro initial; change Preserves (fun w=>txCryptWire w=initial) _
      repeat' crypt_wire_step initial
    · intro initial; change Preserves (fun w=>handoffTxView w=initial) _
      repeat' first
        | (rx_retention_head setPeer
           apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptStagingFrames.«0».Leanux.Proofs.WG.RetirementSecurity.queue_set_saved)
           simp only [queue]
           assumption)
        | crypt_queue_step initial
    · intro initial; change Preserves (fun w=>queued w=initial) _
      repeat' tx_work_step initial
  · exact TxCovered.Native.peer_update pid f stamp queue

theorem serving_peer_update_bind (pid : PeerId) (f : Peer→Peer) (tail : Unit→WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId) (queue : ∀p,(f p).txQueue.all=p.txQueue.all)
    (next : ∀x,Preserves (Serving locals crypt tx) (tail x)) :
    Preserves (Serving locals crypt tx) (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (serving_peer_update pid f stamp queue) next

macro "serving_metadata_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply serving_peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply serving_peer_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact serving_store getDev_sameWGStore)
  | (rx_retention_head modifyDev
     apply serving_join
     · apply service_device <;> intro d <;> rfl
     apply TxCovered.Native.modify_device
     · intro w; unfold identityView Peers.snapshot keypairResidents packetResidents; simp [Option.bind_map,Function.comp_def]
     · intro w; simp [allocationMetadata,deviceAllocationMetadata,Option.map_map,Function.comp_def] <;> rfl
     · intro w; simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def]
     · intro w; funext pid; simp [handoffTxView,Option.bind_map,Function.comp_def])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem handshake_endpoint_work (pid : PeerId) (src : SkbSource) :
    SameView queued (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (store (endpointFromSkb_sameWGStore _)).wp (·=initial))
    | (rx_retention_head setPeerEndpoint; exact (endpoint_work _ _).wp (·=initial))
    | handshake_work_step initial

theorem serving_handshake_endpoint (pid : PeerId) (src : SkbSource) :
    Preserves (Serving locals crypt tx) (setPeerEndpointFromSkb pid src) :=
  serving_join (passive_contents (OccurrenceHandshake.endpoint_wire pid src)
    (OccurrenceHandshake.endpoint_contents pid src) (handshake_endpoint_work pid src))
    (TxCovered.join (OccurrenceHandshake.endpoint pid src) (TxCoverageNative.endpoint pid src))

theorem serving_handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Serving locals crypt tx) (timersHandshakeComplete pid site) :=
  serving_join (passive (handshakeComplete_cryptWire pid site)
    (ownership_queues (handshakeComplete_ownership pid site)) (handshake_complete_work pid site))
    (TxCovered.join (OccurrenceHandshake.handshake_complete pid site) (TxCoverageNative.handshake_complete pid site))

theorem serving_del (pid : PeerId) (timer : PeerTimer) :
    Preserves (Serving locals crypt tx) (delTimer pid timer) :=
  serving_join (passive (delTimer_cryptWire pid timer) (ownership_queues (delTimer_ownership pid timer))
    (delTimer_work pid timer)) (TxCovered.join (OccurrenceHandshake.del pid timer) (TxCoverageNative.del pid timer))

theorem serving_traversal (pid : PeerId) : Preserves (Serving locals crypt tx) (timersTraversal pid) :=
  serving_join (passive (timersTraversal_cryptWire pid) (ownership_queues (timersTraversal_ownership pid))
    (timersTraversal_work pid)) (TxCovered.join (OccurrenceHandshake.traversal pid) (TxCoverageNative.traversal pid))

theorem serving_cookie_reply (msg : List UInt8) (src : SkbSource) :
    Preserves (Serving locals crypt tx) (sendHandshakeCookie msg src) := by
  apply serving_join
  · apply passive
    · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
        (fun s : Option Device × Nat × Nat => txCryptWire {dev:=s.1}) txCryptWire
        (fun w=>by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Cookies.noiseView,
          Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
    · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
        (fun s : Option Device × Nat × Nat => handoffTxView {dev:=s.1}) handoffTxView
        (fun w=>by funext pid; simp [handoffTxView,Cookies.noiseView,Cookies.viewOfStore,
          Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def])
    · exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
        (fun s : Option Device × Nat × Nat => queued {dev:=s.1}) queued
        (fun w=>by simp [queued,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,
          Option.map_map,Function.comp_def])
  · exact TxCovered.join (OccurrenceHandshake.cookie_reply msg src) (TxCoverageNative.cookie_reply msg src)

theorem serving_cookie_frame {action : WG.M α} (same : SameCookie action) :
    Preserves (Serving locals crypt tx) action := by
  apply serving_join
  · apply passive
    · exact same.of_factor (fun s : WGOwnedView=>txCryptWire {dev:=s.dev}) txCryptWire
        (fun w=>by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,cookieView,
          cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
    · exact same.of_factor (fun s : WGOwnedView=>handoffTxView {dev:=s.dev}) handoffTxView
        (fun w=>by funext pid; simp [handoffTxView,cookieView,cookieDevice,wgOwnedView,
          wgStoreView,Option.bind_map,Function.comp_def])
    · exact same.of_factor (fun s : WGOwnedView=>queued {dev:=s.dev}) queued
        (fun w=>by simp [queued,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])
  · exact TxCovered.join (OccurrenceHandshake.cookie_frame same) (TxCoverageNative.cookie_frame same)

theorem serving_after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (Serving locals crypt tx) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact serving_handshake (.consumeInitiation _))
    | (rx_retention_head consumeResponse; exact serving_handshake (.consumeResponse _))
    | (rx_retention_head sendHandshakeResponse; exact serving_handshake_send (.response _))
    | (rx_retention_head beginSession; exact serving_session _)
    | (rx_retention_head sendHandshakeCookie; exact serving_cookie_reply _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact serving_handshake_endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact serving_handshake_send (.sessionDerived _))
    | (rx_retention_head timersHandshakeComplete; exact serving_handshake_complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact serving_del _ _)
    | (rx_retention_head timersTraversal; exact serving_traversal _)
    | (rx_retention_head sendKeepalive; exact serving_keepalive _)
    | (rx_retention_head peerPut; exact serving_peer_put _)
    | serving_metadata_step

theorem serving_cookie_consume (msg : List UInt8) : Preserves (Serving locals crypt tx) (cookieMessageConsume msg) :=
  serving_join (passive_contents (OccurrenceHandshake.cookie_consume_wire msg)
    (OccurrenceHandshake.cookie_consume_contents msg) (cookie_consume_work msg))
    (TxCovered.join (RxPollOccurrences.join (cookieMessageConsumePrefix_erases msg)
      (cookieMessageConsumePrefix_preserves allocationAmbient msg)
      (occurrences_queueContents (OccurrenceHandshake.cookie_consume_wire msg)
        (OccurrenceHandshake.cookie_consume_contents msg))) (TxCoverageNative.consume_cookie msg))

theorem serving_receive (msg : List UInt8) (src : SkbSource) :
    Preserves (Serving locals crypt tx) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact serving_cookie_consume _)
    | (rx_retention_head Cookies.loadPhase; exact serving_store Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact serving_cookie_frame (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact serving_after_mac _ _ _ _)
    | serving_metadata_step

theorem serving_receive_step : Preserves (Serving locals crypt tx) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact serving_receive _ _)
    | serving_metadata_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
