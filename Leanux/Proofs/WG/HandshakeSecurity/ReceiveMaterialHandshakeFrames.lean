import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialWorkerFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialHandshakeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportHandshakeFrames

/-! Native handshake paths retain received-packet allocation certificates.
Successful session derivation uses the fresh numeric frontier; existing cells
retain their core even when reference cleanup removes other keys. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.HandshakeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins.Retaining RetirementSecurity AuthenticatedEffects
open ResidentMaterial (core_of_same lower_frame)
open ResidentMaterial.NativeFrames (lower_index_lookup lower_pubkey lower_owner_geometry)
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem index (action : IndexM α) : Preserves (Bounded h) (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table hi device
  constructor
  · intro out atOut id packet stored
    cases atOut
    simpa only [Inv,Certificate,packetStamp,pool,device,Option.bind_some,Option.map_some] using hi.1 d device id packet stored
  · intro out atOut slot key stored
    cases atOut
    exact hi.2 d device slot key stored

theorem index_lookup (kinds : List IndexKind) (id : Nat) : Preserves (Bounded h) (indexLookup kinds id) :=
  bounded_frame (TransportHandshakeFrames.indexLookup kinds id)
    (core_of_same (indexLookup_core kinds id)) (fun _ => lower_index_lookup kinds id)

theorem pubkey (key : Key) : Preserves (Bounded h) (pubkeyLookup key) :=
  bounded_frame (TransportConfiguration.pubkey_rx key)
    (core_of_same (pool_of_material (pubkeyLookup_material key))) (fun _ => lower_pubkey key)

macro "receive_handshake_leaf" : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact index_lookup _ _)
  | (rx_retention_head pubkeyLookup; exact pubkey _)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head endpointFromSkb; exact bounded_store (endpointFromSkb_sameWGStore _))
  | (allocation_release_lift_from IndexM; exact index _)
  | (rx_retention_head ite
     apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | receive_crypto (Bounded _)
  | receive_bounded_native_step)

theorem initiation (msg : List UInt8) : Preserves (Bounded h) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first | receive_handshake_leaf | split
  all_goals
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite)
    all_goals repeat' receive_handshake_leaf

theorem response (msg : List UInt8) : Preserves (Bounded h) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first | receive_handshake_leaf | split

theorem create_response (pid : PeerId) : Preserves (Bounded h) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | receive_handshake_leaf | split

theorem cookie_consume (msg : List UInt8) : Preserves (Bounded h) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first | receive_handshake_leaf | split

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : Preserves (Bounded h) action := by
  apply bounded_frame
  · exact TransportHandshakeFrames.cookie action same
  · apply core_of_same
    exact same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
      (fun w => by funext kid; simp [pool,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def])
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => ResidentMaterial.cursor {dev:=s.dev}) ResidentMaterial.cursor
      (fun w => by simp [ResidentMaterial.cursor,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Bounded h) (sendHandshakeCookie msg src) := by
  apply bounded_frame
  · exact TransportHandshakeFrames.sendCookie msg src
  · apply core_of_same
    exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => pool {dev:=s.1}) pool
      (fun w => by funext kid; simp [pool,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def])
  · intro bound
    apply lower_frame
    exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => ResidentMaterial.cursor {dev:=s.1}) ResidentMaterial.cursor
      (fun w => by simp [ResidentMaterial.cursor,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Function.comp_def])

theorem mac (pid : PeerId) (bytes : List UInt8) : Preserves (Bounded h) (addMacToPacket pid bytes) :=
  bounded_frame (TransportHandshakeFrames.mac pid bytes)
    (core_of_same (pool_of_material (addMacToPacket_material pid bytes)))
    (fun _ => lower_owner_geometry (PublicationGeometry.addMacToPacket_geometry pid bytes))

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : Preserves (Bounded h) (sendBufferToPeer pid bytes) :=
  bounded_frame (TransportHandshakeFrames.send pid bytes)
    (core_of_same (pool_of_material (sendBufferToPeer_material pid bytes)))
    (fun _ => lower_owner_geometry (PublicationGeometry.sendBufferToPeer_geometry pid bytes))

theorem derived (pid : PeerId) : Preserves (Bounded h) (timersSessionDerived pid) :=
  bounded_frame (TransportHandshakeFrames.derived pid)
    (core_of_same (pool_of_material (timersSessionDerived_material pid)))
    (fun _ => lower_owner_geometry
      (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry)
        .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())))

theorem traversal (pid : PeerId) : Preserves (Bounded h) (timersTraversal pid) :=
  bounded_frame (TransportHandshakeFrames.traversal pid)
    (core_of_same (pool_of_material (timersTraversal_material pid)))
    (fun _ => lower_owner_geometry (PublicationGeometry.timersTraversal_geometry pid))

theorem del (pid : PeerId) (timer : PeerTimer) : Preserves (Bounded h) (delTimer pid timer) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer).factor Prod.snd)
    (core_of_same (pool_of_material (delTimer_material pid timer)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer))

theorem endpoint_skb (pid : PeerId) (src : SkbSource) : Preserves (Bounded h) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact bounded_endpoint _ _)
    | receive_handshake_leaf

macro "receive_handshake_frame" : tactic => `(tactic| first
  | (rx_retention_head beginSession; exact bounded_session _)
  | (rx_retention_head createResponse; exact create_response _)
  | (rx_retention_head addMacToPacket; exact mac _ _)
  | (rx_retention_head sendBufferToPeer; exact send_buffer _ _)
  | (rx_retention_head timersSessionDerived; exact derived _)
  | (rx_retention_head timersTraversal; exact traversal _)
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact del _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del _ _)
  | (rx_retention_head timersHandshakeComplete; exact bounded_complete _ _)
  | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
  | (rx_retention_head consumeInitiation; exact initiation _)
  | (rx_retention_head consumeResponse; exact response _)
  | (rx_retention_head cookieMessageConsume; exact cookie_consume _)
  | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_skb _ _)
  | (rx_retention_head Cookies.loadPhase; exact bounded_store Cookies.loadPhase_sameStore)
  | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
  | (rx_retention_head WG.orM; unfold WG.orM WG.andM; simp only [branch])
  | (rx_retention_head WG.andM; unfold WG.andM; simp only [branch])
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head hiddenClock64; exact hoare_liftAmbient (AmbientM.hiddenClock64 _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | receive_handshake_leaf)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.HandshakeFrames
