import Leanux.Proofs.WG.Packets.PublicationHandshakeSend
import Leanux.Proofs.WG.Packets.PublicationFrontierPoll
import Leanux.Proofs.WG.Origins.OwnerHandshake

/-! Native handshake reception retains encrypted packet anchors even when
authentication failure pays a peer or a successful session allocates a key.
Only actual normal endpoints are asserted; recorded failures still stop. -/
namespace Leanux.Proofs.WG.PublicationHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationFrontier PublicationCompletion
open OwnerCompletion (geometry)

private theorem framed (a : WG.M α) (shape : SameView geometry a)
    (configured : SameView ConfiguredIdentity.view a) (history : List RxHistory.Event) :
    Preserves (Inv history) a :=
  preserves_of_configured a (shape.factor Prod.snd) configured history

private theorem update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply framed _ ?_ (ConfiguredIdentity.modifyPeer_view pid f same) history
  intro initial
  change Preserves (fun w => geometry w = initial) (getPeer pid >>= fun p => setPeer pid (f p))
  repeat' completion_step initial

private theorem update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (history : List RxHistory.Event) (ht : ∀ x, Preserves (Inv history) (tail x)) :
    Preserves (Inv history) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f same history) ht

private theorem readPeer (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v finalAmbient hi hr
  exact (getPeer_normal pid w v p ambient finalAmbient hr).1 ▸ hi

macro "publication_handshake_step " history:term : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update; intro p; rfl)
  | (receive_update_head Bind.bind
     apply update_bind
     · intro p; rfl
     intro x)
  | (rx_retention_head getDev; exact store_preserves getDev_sameWGStore $history)
  | (rx_retention_head getPeer; exact readPeer _ $history)
  | (rx_retention_head peerPut; exact PublicationFrontier.peerPut_preserves _ $history)
  | (rx_retention_head indexLookup; exact indexLookup_preserves _ _ $history)
  | (rx_retention_head modifyDev
     apply modifyDev_preserves
     all_goals intros; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv $history))
  | (rx_retention_head ite
     apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | routing_tx_step)

private theorem pubkey (key : Key) (history : List RxHistory.Event) :
    Preserves (Inv history) (pubkeyLookup key) := by
  apply framed _ ?_ (ConfiguredReceive.pubkeyLookup_view key) history
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold pubkeyLookup peerGetMaybeZero
  simp (config := {zeta := false}) only [branch,branchCmp,refcountIncNotZero,invariant,unsupported,requireNotPending]
  repeat' completion_step initial

theorem createResponse (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (WG.createResponse pid) := by
  apply framed _ ?_ (ConfiguredReceive.createResponse_view pid) history
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold WG.createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | receive_crypto (fun w => geometry w = initial)
    | publication_geometry_step initial

theorem consumeInitiation (msg : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (WG.consumeInitiation msg) := by
  unfold WG.consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | (rx_retention_head pubkeyLookup; exact pubkey _ history)
    | receive_crypto (Inv history)
    | publication_handshake_step history

theorem consumeResponse (msg : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (WG.consumeResponse msg) := by
  unfold WG.consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | receive_crypto (Inv history)
    | publication_handshake_step history

theorem cookieMessageConsume (msg : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (WG.cookieMessageConsume msg) := by
  unfold WG.cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' publication_handshake_step history

private theorem cookie (a : WG.M α) (frame : SameCookie a) (history : List RxHistory.Event) :
    Preserves (Inv history) a := by
  apply preserves_of_configured a
  · apply frame.of_factor
      (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?))
      RxDisposition.nativeRxStore
    intro w
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,RxDisposition.nativeRxStore,
      Option.map_map,Option.bind_map,Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view
    intro w
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
      ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl

private theorem endpoint (pid : PeerId) (src : SkbSource) (history : List RxHistory.Event) :
    Preserves (Inv history) (setPeerEndpointFromSkb pid src) := by
  apply framed _ ?_ (ConfiguredReceiveLeaves.setPeerEndpointFromSkb_view pid src) history
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (endpointFromSkb_sameWGStore _)).wp (fun s => s = initial))
    | (rx_retention_head setPeerEndpoint
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem reply (src : SkbSource) (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendBufferAsReplyToSkb src bytes) := by
  apply framed _ ?_ (ConfiguredReceiveLeaves.sendBufferAsReplyToSkb_view src bytes) history
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (endpointFromSkb_sameWGStore _)).wp (fun s => s = initial))
    | (rx_retention_head send4; exact (PublicationGeometry.send4_geometry _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (PublicationGeometry.send6_geometry _ _ _ _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem sendCookie (msg : List UInt8) (src : SkbSource) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact preserves_bind (cookie _ (cookieMessageCreate_sameCookie _ _ _) history)
    (fun bytes => reply src bytes history)

private theorem derived (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (timersSessionDerived pid) :=
  framed _ (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry)
    .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ()))
    (ConfiguredReceiveLeaves.timersSessionDerived_view pid) history

private theorem complete (pid : PeerId) (site : HiddenSite) (history : List RxHistory.Event) :
    Preserves (Inv history) (timersHandshakeComplete pid site) :=
  framed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.handshake_geometry) pid site)
    (ConfiguredReceiveLeaves.timersHandshakeComplete_view pid site) history

private theorem traversal (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (timersTraversal pid) :=
  framed _ (PublicationGeometry.timersTraversal_geometry pid)
    (ConfiguredIdentity.timersTraversal_view pid) history

private theorem sent (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (timersAnyAuthenticatedPacketSent pid) :=
  framed _ (PublicationGeometry.timersAnyAuthenticatedPacketSent_geometry pid)
    (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view pid) history

private theorem mac (pid : PeerId) (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (addMacToPacket pid bytes) :=
  framed _ (PublicationGeometry.addMacToPacket_geometry pid bytes)
    (ConfiguredHandshake.addMacToPacket_view pid bytes) history

private theorem send (pid : PeerId) (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendBufferToPeer pid bytes) :=
  framed _ (PublicationGeometry.sendBufferToPeer_geometry pid bytes)
    (ConfiguredHandshake.sendBufferToPeer_view pid bytes) history

private theorem received (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (timersAnyAuthenticatedPacketReceived pid) :=
  framed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid .newHandshake)
    (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view pid) history

private theorem keepalive (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendKeepalive pid) := by
  apply preserves_of_geometry
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold sendKeepalive
    simp (config := {zeta := false}) only [branch,hiddenAlloc]
    repeat' first
      | (rx_retention_head sendStagedPackets
         exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) _).wp (fun s => s = initial))
      | completion_step initial
  · intro initial
    unfold sendKeepalive
    simp (config := {zeta := false}) only [branch,hiddenAlloc]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact sendStagedPackets_peers _ initial)
      | publication_peer_step initial

theorem sendResponse (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head WG.createResponse; exact createResponse _ history)
    | (rx_retention_head addMacToPacket; exact mac _ _ history)
    | (rx_retention_head beginSession; exact PublicationFrontier.beginSession_preserves _ history)
    | (rx_retention_head timersSessionDerived; exact derived _ history)
    | (rx_retention_head timersTraversal; exact traversal _ history)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _ history)
    | (rx_retention_head sendBufferToPeer; exact send _ _ history)
    | publication_handshake_step history

private theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState)
    (history : List RxHistory.Event) : Preserves (Inv history) (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head WG.consumeInitiation; exact consumeInitiation _ history)
    | (rx_retention_head WG.consumeResponse; exact consumeResponse _ history)
    | (rx_retention_head sendHandshakeResponse; exact sendResponse _ history)
    | (rx_retention_head beginSession; exact PublicationFrontier.beginSession_preserves _ history)
    | (rx_retention_head sendHandshakeCookie; exact sendCookie _ _ history)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _ history)
    | (rx_retention_head timersSessionDerived; exact derived _ history)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _ history)
    | (rx_retention_head sendKeepalive; exact keepalive _ history)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _ history)
    | (rx_retention_head timersTraversal; exact traversal _ history)
    | publication_handshake_step history

theorem receiveHandshakePacket (msg : List UInt8) (src : SkbSource) (history : List RxHistory.Event) :
    Preserves (Inv history) (WG.receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.cookieMessageConsume; exact cookieMessageConsume _ history)
    | (rx_retention_head Cookies.loadPhase; exact store_preserves Cookies.loadPhase_sameStore history)
    | (rx_retention_head cookieValidatePacket; exact cookie _ (cookieValidatePacket_sameCookie _ _ _) history)
    | (rx_retention_head Cookies.afterMac; exact afterMac _ _ _ _ history)
    | publication_handshake_step history

theorem receiveStep (history : List RxHistory.Event) :
    Preserves (Inv history) WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.receiveHandshakePacket; exact receiveHandshakePacket _ _ history)
    | publication_handshake_step history

end Leanux.Proofs.WG.PublicationHandshake
