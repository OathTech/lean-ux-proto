import Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
import Leanux.Proofs.WG.Queues.HandshakeLoans

/-! Native Noise, cookie and response-send leaves retain complete RX cells.
The projection permits the actual peer/key writes and cleanup deletions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportHandshakeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransportCarrier
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem indexLookup (kinds : List IndexKind) (index : Nat) :
    SameView RxDisposition.nativeRxStore (WG.indexLookup kinds index) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact RxCredits.loan_rx ((hoare_iff_run_ambient _ _ _).mp (RxCredits.indexLookup_loan kinds index w)
    w a result v b rfl run)

private theorem choice (p : Prop) [Decidable p] (a b : WG.M α) (P : WGWorld → Prop)
    (ha : Preserves P a) (hb : Preserves P b) : Preserves P (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha
  · exact hb

macro "transport_handshake_frame " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact (TransportPublication.store_rx _ getDev_sameWGStore).wp (· = $initial))
  | (rx_retention_head getPeer; exact (TransportPublication.getPeer_rx _).wp (· = $initial))
  | (rx_retention_head setPeer; exact (TransportPublication.setPeer_rx _ _).wp (· = $initial))
  | (rx_retention_head peerPut; exact (RxCredits.peerPut_rxView _).wp (· = $initial))
  | (rx_retention_head WG.indexLookup; exact (indexLookup _ _).wp (· = $initial))
  | (rx_retention_head pubkeyLookup; exact (TransportConfiguration.pubkey_rx _).wp (· = $initial))
  | (rx_retention_head modifyDev; apply (modifyDev_rx _ ?_ ?_).wp (· = $initial); all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (fun w => RxDisposition.nativeRxStore w = $initial))
  | (rx_retention_head ite; apply choice)
  | routing_tx_step)

theorem consumeInitiation (msg : List UInt8) : SameView RxDisposition.nativeRxStore (WG.consumeInitiation msg) := by
  intro initial
  change Preserves (fun w => RxDisposition.nativeRxStore w = initial) _
  unfold WG.consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | receive_crypto (fun w => RxDisposition.nativeRxStore w = initial)
    | transport_handshake_frame initial

theorem consumeResponse (msg : List UInt8) : SameView RxDisposition.nativeRxStore (WG.consumeResponse msg) := by
  intro initial
  change Preserves (fun w => RxDisposition.nativeRxStore w = initial) _
  unfold WG.consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | receive_crypto (fun w => RxDisposition.nativeRxStore w = initial)
    | transport_handshake_frame initial

theorem createResponse (pid : PeerId) : SameView RxDisposition.nativeRxStore (WG.createResponse pid) := by
  apply SameView.factor (view := OwnerCompletion.geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold WG.createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | receive_crypto (fun w => OwnerCompletion.geometry w = initial)
    | publication_geometry_step initial

theorem cookieConsume (msg : List UInt8) : SameView RxDisposition.nativeRxStore (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w => RxDisposition.nativeRxStore w = initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' transport_handshake_frame initial

theorem cookie (action : WG.M α) (same : SameCookie action) :
    SameView RxDisposition.nativeRxStore action := by
  apply same.of_factor
    (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,RxDisposition.nativeRxStore,
    Option.map_map,Option.bind_map,Function.comp_def]

theorem endpoint (pid : PeerId) (src : SkbSource) :
    SameView RxDisposition.nativeRxStore (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => RxDisposition.nativeRxStore w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (TransportPublication.store_rx _ (endpointFromSkb_sameWGStore _)).wp (· = initial))
    | (rx_retention_head setPeerEndpoint; exact (endpoint_rx _ _).wp (· = initial))
    | transport_handshake_frame initial

theorem reply (src : SkbSource) (bytes : List UInt8) :
    SameView RxDisposition.nativeRxStore (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.factor (view := OwnerCompletion.geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (endpointFromSkb_sameWGStore _)).wp (· = initial))
    | (rx_retention_head send4; exact (PublicationGeometry.send4_geometry _ _ _ _ _).wp (· = initial))
    | (rx_retention_head send6; exact (PublicationGeometry.send6_geometry _ _ _ _ _).wp (· = initial))
    | completion_step initial

theorem sendCookie (msg : List UInt8) (src : SkbSource) :
    SameView RxDisposition.nativeRxStore (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact (cookie _ (cookieMessageCreate_sameCookie _ _ _)).bind (fun bytes => reply src bytes)

theorem derived (pid : PeerId) : SameView RxDisposition.nativeRxStore (timersSessionDerived pid) :=
  (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry)
    .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())).factor Prod.snd

theorem traversal (pid : PeerId) : SameView RxDisposition.nativeRxStore (timersTraversal pid) :=
  (PublicationGeometry.timersTraversal_geometry pid).factor Prod.snd

theorem sent (pid : PeerId) : SameView RxDisposition.nativeRxStore (timersAnyAuthenticatedPacketSent pid) :=
  (PublicationGeometry.timersAnyAuthenticatedPacketSent_geometry pid).factor Prod.snd

theorem mac (pid : PeerId) (bytes : List UInt8) : SameView RxDisposition.nativeRxStore (addMacToPacket pid bytes) :=
  (PublicationGeometry.addMacToPacket_geometry pid bytes).factor Prod.snd

theorem send (pid : PeerId) (bytes : List UInt8) : SameView RxDisposition.nativeRxStore (sendBufferToPeer pid bytes) :=
  (PublicationGeometry.sendBufferToPeer_geometry pid bytes).factor Prod.snd

theorem received (pid : PeerId) : SameView RxDisposition.nativeRxStore (timersAnyAuthenticatedPacketReceived pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid .newHandshake).factor Prod.snd

end Leanux.Proofs.WG.AuthenticatedEffects.TransportHandshakeFrames
