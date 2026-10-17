import Leanux.Proofs.WG.Origins.JointOwnerConfiguration
import Leanux.Proofs.WG.Origins.CurrentReceiveChecks
import Leanux.Proofs.WG.Origins.OwnerWorkers

/-! Owner checks through the actual handshake receive worker. A private
existential session history is used only for native carrier endpoints; the
existing positional current checks independently retain the exact journal. -/
namespace Leanux.Proofs.WG.OwnerHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits Origins OwnerBounds ConfiguredHandshake ConfiguredReceive ConfiguredReceiveLeaves
open Origins.HistorySupport (sensitive)

private def Supported (w : WGWorld) : Prop :=
  ∃ history, CurrentLifecycle.Inv history w ∧ Carrier w

private theorem combine (a : WG.M α)
    (current : ∀ history, Preserves (CurrentLifecycle.Inv history) a)
    (owner : Preserves Carrier a) : Preserves Supported a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  obtain ⟨history,hi,hc⟩ := hi
  exact ⟨history,(hoare_iff_run_ambient _ _ _).mp (current history)
    w ambient result v finalAmbient hi hr,
    (hoare_iff_run_ambient _ _ _).mp owner w ambient result v finalAmbient hc hr⟩

private theorem store (a : WG.M α) (same : SameWGStore a) : Preserves Supported a :=
  combine a (fun history =>
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.store_preserves)
      a same history) (OwnerControls.store a same)

private theorem view (a : WG.M α) (frame : SameView ConfiguredIdentity.view a)
    (material : SameView Origins.view a) (owner : Preserves Carrier a) :
    Preserves Supported a :=
  combine a (fun history => current_preserves a frame (Retaining.of_view material) history) owner

private theorem update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    Preserves Supported (getPeer pid >>= fun p => setPeer pid (f p)) :=
  view _ (ConfiguredIdentity.modifyPeer_view pid f same)
    (SameView.bind (Origins.getPeer_view pid) (fun p => Origins.setPeer_view pid (f p)))
    (preserves_bind (OwnerControls.readPeer pid) (fun p => OwnerControls.writePeer pid (f p)))

private theorem update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (ht : ∀ x, Preserves Supported (tail x)) :
    Preserves Supported (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f same) ht

private theorem modifyDevice (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (material : ∀ d, ((f d).ifindex,(f d).keypairs) = (d.ifindex,d.keypairs))
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (key : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) : Preserves Supported (modifyDev f) :=
  combine _ (fun history =>
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.modifyDev_preserves)
      f configured material history)
    (OwnerControls.modifyDevice f peer key keys rx)

macro "owner_handshake_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update; intro p; rfl)
  | (receive_update_head Bind.bind
     apply update_bind
     · intro p; rfl
     intro x)
  | (rx_retention_head getDev; exact store _ getDev_sameWGStore)
  | (rx_retention_head getPeer
     exact combine _ (fun history =>
       (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.readPeer_preserves) _ history)
       (OwnerControls.readPeer _))
  | (rx_retention_head modifyDev
     apply modifyDevice _ ?_ ?_ ?_ ?_ ?_ ?_
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Supported)
  | routing_tx_step)

private theorem createResponse_owner (pid : PeerId) : Preserves Carrier (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | receive_crypto Carrier
    | owner_control_step

private theorem initiation_owner (msg : List UInt8) : Preserves Carrier (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | (rx_retention_head pubkeyLookup
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerConfiguration.«0».Leanux.Proofs.WG.JointOwnerConfiguration.pubkey_owner) _)
    | receive_crypto Carrier
    | owner_control_step
    | routing_tx_step

private theorem response_owner (msg : List UInt8) : Preserves Carrier (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact OwnerIndex.indexLookup_preserves _ _)
    | receive_crypto Carrier
    | owner_control_step

private theorem consumeCookie_owner (msg : List UInt8) : Preserves Carrier (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact OwnerIndex.indexLookup_preserves _ _)
    | owner_control_step

private theorem endpoint_owner (pid : PeerId) (src : SkbSource) :
    Preserves Carrier (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact OwnerControls.store _ (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact OwnerPeerConfiguration.setPeerEndpoint_preserves _ _)
    | owner_control_step

private theorem cookie_owner (a : WG.M α) (frame : SameCookie a) : Preserves Carrier a := by
  apply OwnerCompletion.preserves_of_frames _
    (Retaining.of_view (Retaining.cookie_material_native a (frame.factor WGOwnedView.toWGStoreView)))
  · apply frame.of_factor
      (fun s : WGOwnedView => (s.dev.map (fun d => (d.ifindex,d.nextPeer,d.nextKeypairId)),
        (s.dev.map Device.ifindex,fun id => s.dev.bind (fun d => d.rxSkbs[id]?)))) OwnerCompletion.geometry
    intro w
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,OwnerCompletion.geometry,rxView,
      Option.map_map,Option.bind_map,Function.comp_def]
  · apply keyEffects_view (allowed := NoPromotion)
    apply frame.of_factor (fun s : WGOwnedView => (s.dev.map Device.ifindex,
      (fun kid => (s.dev.bind (fun d => d.keypairs[kid]?)).map Keypair.peer),
      fun pid => (s.dev.bind (fun d => d.peers[pid]?)).map currentCell)) keyView
    intro w
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,keyView,
      Option.map_map,Option.bind_map,Function.comp_def]
    rfl

private theorem reply_owner (src : SkbSource) (bytes : List UInt8) :
    Preserves Carrier (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact OwnerControls.store _ (endpointFromSkb_sameWGStore _))
    | (rx_retention_head send4; exact OwnerLifecycle.send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact OwnerLifecycle.send6_preserves _ _ _ _ _)
    | owner_control_step

private theorem sendCookie_owner (msg : List UInt8) (src : SkbSource) :
    Preserves Carrier (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact preserves_bind (cookie_owner _ (cookieMessageCreate_sameCookie _ _ _))
    (fun bytes => reply_owner src bytes)

private theorem derived_owner (pid : PeerId) : Preserves Carrier (timersSessionDerived pid) := by
  unfold timersSessionDerived
  apply discard_view_spec id Carrier
  exact OwnerLifecycle.modPeerTimer_preserves _ _ _ _

private theorem complete_owner (pid : PeerId) (site : HiddenSite) :
    Preserves Carrier (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact OwnerLifecycle.delTimer_preserves _ _)
    | owner_control_step

private theorem session (pid : PeerId) : Preserves Supported (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  obtain ⟨history,hi⟩ := hi
  obtain ⟨front,u,middle,_,current,carrier⟩ :=
    OwnerCreation.beginSession_current pid w v result ambient finalAmbient history hi hr
  exact ⟨history ++ [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩],current,carrier⟩

private theorem create (pid : PeerId) : Preserves Supported (createResponse pid) :=
  combine _ (ConfiguredReceive.createResponse_preserves pid) (createResponse_owner pid)

private theorem initiation (msg : List UInt8) : Preserves Supported (consumeInitiation msg) :=
  combine _ (ConfiguredReceive.consumeInitiation_preserves msg) (initiation_owner msg)

private theorem response (msg : List UInt8) : Preserves Supported (consumeResponse msg) :=
  combine _ (ConfiguredReceive.consumeResponse_preserves msg) (response_owner msg)

private theorem consumeCookie (msg : List UInt8) : Preserves Supported (cookieMessageConsume msg) :=
  combine _ (CurrentTraffic.cookieMessageConsume_preserves msg) (consumeCookie_owner msg)

private theorem mac (pid : PeerId) (msg : List UInt8) : Preserves Supported (addMacToPacket pid msg) :=
  view _ (addMacToPacket_view pid msg) (Retaining.addMacToPacket_material pid msg)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.addMacToPacket_preserves) pid msg)

private theorem send (pid : PeerId) (msg : List UInt8) : Preserves Supported (sendBufferToPeer pid msg) :=
  view _ (sendBufferToPeer_view pid msg) (Retaining.sendBufferToPeer_material pid msg)
    (OwnerLifecycle.sendBufferToPeer_preserves pid msg)

private theorem traversal (pid : PeerId) : Preserves Supported (timersTraversal pid) :=
  view _ (ConfiguredIdentity.timersTraversal_view pid) (Retaining.timersTraversal_material pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.traversal_preserves) pid)

private theorem sent (pid : PeerId) : Preserves Supported (timersAnyAuthenticatedPacketSent pid) :=
  view _ (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view pid)
    (Retaining.timersAnyAuthenticatedPacketSent_material pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.sent_preserves) pid)

private theorem derived (pid : PeerId) : Preserves Supported (timersSessionDerived pid) :=
  view _ (timersSessionDerived_view pid) (Retaining.timersSessionDerived_material pid) (derived_owner pid)

private theorem complete (pid : PeerId) (site : HiddenSite) : Preserves Supported (timersHandshakeComplete pid site) :=
  view _ (timersHandshakeComplete_view pid site) (Retaining.timersHandshakeComplete_material pid site)
    (complete_owner pid site)

private theorem endpoint (pid : PeerId) (src : SkbSource) : Preserves Supported (setPeerEndpointFromSkb pid src) :=
  view _ (setPeerEndpointFromSkb_view pid src) (HistorySupport.endpoint_material pid src)
    (endpoint_owner pid src)

private theorem sendCookie (msg : List UInt8) (src : SkbSource) : Preserves Supported (sendHandshakeCookie msg src) :=
  combine _ (fun history => current_preserves _ (sendHandshakeCookie_view msg src)
    (Retaining.of_view (HistorySupport.cookieSend_material msg src)) history) (sendCookie_owner msg src)

private theorem keepalive (pid : PeerId) : Preserves Supported (sendKeepalive pid) :=
  combine _ (CurrentTraffic.sendKeepalive_preserves pid) (OwnerPeerConfiguration.sendKeepalive_preserves pid)

private theorem received (pid : PeerId) : Preserves Supported (timersAnyAuthenticatedPacketReceived pid) :=
  view _ (timersAnyAuthenticatedPacketReceived_view pid) (Retaining.timersAnyAuthenticatedPacketReceived_material pid)
    (OwnerLifecycle.delTimer_preserves pid .newHandshake)

private theorem pay (peer : Option PeerId) : Preserves Supported (peerPut peer) :=
  combine _ (fun history =>
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentReceiveHistory.«0».Leanux.Proofs.WG.CurrentReceiveHistory.pay_preserves) peer history)
    (OwnerConsume.peerPut_preserves peer)

private theorem cookie (a : WG.M α) (frame : SameCookie a) : Preserves Supported a :=
  combine _ (fun history =>
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentReceiveHistory.«0».Leanux.Proofs.WG.CurrentReceiveHistory.cookie_preserves) a frame history)
    (cookie_owner a frame)

private theorem sendResponse (pid : PeerId) : Preserves Supported (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact create _)
    | (rx_retention_head addMacToPacket; exact mac _ _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
    | (rx_retention_head sendBufferToPeer; exact send _ _)
    | owner_handshake_step

private theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves Supported (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact initiation _)
    | (rx_retention_head consumeResponse; exact response _)
    | (rx_retention_head sendHandshakeResponse; exact sendResponse _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head sendHandshakeCookie; exact sendCookie _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head peerPut; exact pay _)
    | owner_handshake_step

private theorem reception (msg : List UInt8) (src : SkbSource) :
    Preserves Supported (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact consumeCookie _)
    | (rx_retention_head Cookies.loadPhase; exact store _ Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie _ (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact afterMac _ _ _ _)
    | owner_handshake_step

private theorem step : Preserves Supported WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact reception _ _)
    | owner_handshake_step

/-- Current identity uses the exact earlier session prefix supplied by the
existing observer contract. Only the carrier endpoint uses the internal
existential, whose session extensions came from actual front receipts. -/
theorem receiveStep : OwnerChecks.Preserves HistoryAdapters.receiveStep := by
  apply OwnerChecks.quiet _ (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentReceiveChecks.«0».Leanux.Proofs.WG.CurrentReceiveChecks.focus_frame)
      _ _ sensitive _ HistoryAdapters.localStep_appends
      (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentReceiveChecks.«0».Leanux.Proofs.WG.CurrentReceiveChecks.step_frame))
    CurrentReceiveChecks.receiveStep HistoryAdapters.receiveStep_preserves
  intro w h hi x v hr
  have native := (HistoryAdapters.receiveStep_erases w h).symm.trans hr
  rw [liftWG_run] at native
  cases hs : (WG.receiveStep.run w.wg).run w.ambient with
  | error e => simp [hs,Except.map] at native
  | ok endpoint =>
    rcases endpoint with ⟨⟨result,u⟩,ambient⟩
    simp only [hs,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    obtain ⟨_,_,carrier⟩ := (hoare_iff_run_ambient _ _ _).mp step
      w.wg w.ambient result u ambient
      ⟨HistorySupport.sessions h,hi.current.2.1,hi.carrier⟩ hs
    exact carrier

theorem receiveIteration : OwnerChecks.Preserves HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) receiveStep
  exact viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) OwnerWorkers.store
    (condResched_sameKernel .receiveWorker)

end Leanux.Proofs.WG.OwnerHandshake
