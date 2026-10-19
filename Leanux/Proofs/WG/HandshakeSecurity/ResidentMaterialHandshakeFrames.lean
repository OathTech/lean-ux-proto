import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialNativeWorkers
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHandshakeFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeReceive

/-! Handshake callbacks preserve older TX allocation cores. Source index
acquisition may clear a nullable owner word; it cannot alter the sending core. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins.Retaining RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem index (action : IndexM α) : Preserves (Inv h) (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table hi device
  intro out atOut id packet stored
  cases atOut
  simpa only [pool,device,Option.bind_some] using hi d device id packet stored

theorem lower_acquire_owner (owner : IndexOwner) :
    Preserves (Lower bound) (Affiliation.acquireOwner owner) := by
  apply lower_frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have same := (Affiliation.acquireOwner_acquisition owner w v result a b run).facts.2
  have projected := congrArg (fun s => s.map Affiliation.State.nextKey) same
  cases owner <;> simpa only [cursor,Affiliation.view,Affiliation.state,
    Affiliation.State.setWord,Option.map_map,Function.comp_def] using projected

theorem lower_index_lookup (kinds : List IndexKind) (id : Nat) :
    Preserves (Lower bound) (indexLookup kinds id) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
    kinds id _ (lower_index _) lower_acquire_owner

theorem index_lookup (kinds : List IndexKind) (id : Nat) : Preserves (Inv h) (indexLookup kinds id) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceHandshake.index_lookup_wire kinds id))
    (core_of_same (indexLookup_core kinds id)) (fun _ => lower_index_lookup kinds id)

theorem lower_pubkey (key : Key) : Preserves (Lower bound) (pubkeyLookup key) := by
  unfold pubkeyLookup peerGetMaybeZero
  simp (config := {zeta := false}) only [branch,branchCmp,refcountIncNotZero,requireNotPending,invariant,unsupported]
  repeat' resident_lower_step

theorem pubkey (key : Key) : Preserves (Inv h) (pubkeyLookup key) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceHandshake.pubkey_lookup_wire key))
    (core_of_same (pool_of_material (pubkeyLookup_material key))) (fun _ => lower_pubkey key)

macro "resident_handshake_leaf" : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact index_lookup _ _)
  | (rx_retention_head pubkeyLookup; exact pubkey _)
  | (allocation_release_lift_from IndexM; exact index _)
  | (rx_retention_head ite
     apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | receive_crypto (Inv _)
  | resident_poll_frame)

theorem initiation (msg : List UInt8) : Preserves (Inv h) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first | resident_handshake_leaf | split
  all_goals
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite)
    all_goals repeat' resident_handshake_leaf

theorem response (msg : List UInt8) : Preserves (Inv h) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first | resident_handshake_leaf | split

theorem create_response (pid : PeerId) : Preserves (Inv h) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | resident_handshake_leaf | split

theorem cookie_consume (msg : List UInt8) : Preserves (Inv h) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first | resident_handshake_leaf | split

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : Preserves (Inv h) action := by
  apply frame
  · apply PacketOrigins.snapshot_wire
    exact same.of_factor (fun s : WGOwnedView => txCryptWire {dev:=s.dev}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,cookieView,
        cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
  · apply core_of_same
    exact same.of_factor (fun s : WGOwnedView => pool {dev:=s.dev}) pool
      (fun w => by funext kid; simp [pool,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def])
  · intro bound
    apply lower_frame
    exact same.of_factor (fun s : WGOwnedView => cursor {dev:=s.dev}) cursor
      (fun w => by simp [cursor,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Preserves (Inv h) (sendHandshakeCookie msg src) := by
  apply frame
  · apply PacketOrigins.snapshot_wire
    exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => txCryptWire {dev:=s.1}) txCryptWire
      (fun w => by simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
        Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
  · apply core_of_same
    exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => pool {dev:=s.1}) pool
      (fun w => by funext kid; simp [pool,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.bind_map,Function.comp_def])
  · intro bound
    apply lower_frame
    exact (Cookies.sendHandshakeCookie_frame msg src).of_factor
      (fun s : Option Device × Nat × Nat => cursor {dev:=s.1}) cursor
      (fun w => by simp [cursor,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,Option.map_map,Function.comp_def])

theorem mac (pid : PeerId) (bytes : List UInt8) : Preserves (Inv h) (addMacToPacket pid bytes) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceKeys.add_mac_wire pid bytes))
    (core_of_same (pool_of_material (addMacToPacket_material pid bytes)))
    (fun _ => lower_owner_geometry (PublicationGeometry.addMacToPacket_geometry pid bytes))

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : Preserves (Inv h) (sendBufferToPeer pid bytes) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceHandshake.buffer_wire pid bytes))
    (core_of_same (pool_of_material (sendBufferToPeer_material pid bytes)))
    (fun _ => lower_owner_geometry (PublicationGeometry.sendBufferToPeer_geometry pid bytes))

theorem derived (pid : PeerId) : Preserves (Inv h) (timersSessionDerived pid) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceHandshake.derived_wire pid))
    (core_of_same (pool_of_material (timersSessionDerived_material pid)))
    (fun _ => lower_owner_geometry
      (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry)
        .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())))

theorem traversal (pid : PeerId) : Preserves (Inv h) (timersTraversal pid) :=
  frame (PacketOrigins.snapshot_wire (timersTraversal_cryptWire pid))
    (core_of_same (pool_of_material (timersTraversal_material pid)))
    (fun _ => lower_owner_geometry (PublicationGeometry.timersTraversal_geometry pid))

theorem del (pid : PeerId) (timer : PeerTimer) : Preserves (Inv h) (delTimer pid timer) :=
  frame (PacketOrigins.snapshot_wire (delTimer_cryptWire pid timer))
    (core_of_same (pool_of_material (delTimer_material pid timer)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer))

theorem endpoint_skb (pid : PeerId) (src : SkbSource) : Preserves (Inv h) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | resident_poll_frame

macro "resident_handshake_frame" : tactic => `(tactic| first
  | (rx_retention_head beginSession; exact session _)
  | (rx_retention_head createResponse; exact create_response _)
  | (rx_retention_head addMacToPacket; exact mac _ _)
  | (rx_retention_head sendBufferToPeer; exact send_buffer _ _)
  | (rx_retention_head timersSessionDerived; exact derived _)
  | (rx_retention_head timersTraversal; exact traversal _)
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact del _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del _ _)
  | (rx_retention_head timersHandshakeComplete; exact complete _ _)
  | (rx_retention_head sendHandshakeCookie; exact cookie_reply _ _)
  | (rx_retention_head consumeInitiation; exact initiation _)
  | (rx_retention_head consumeResponse; exact response _)
  | (rx_retention_head cookieMessageConsume; exact cookie_consume _)
  | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_skb _ _)
  | (rx_retention_head Cookies.loadPhase; exact store Cookies.loadPhase_sameStore)
  | (rx_retention_head cookieValidatePacket; exact cookie_frame (cookieValidatePacket_sameCookie _ _ _))
  | (rx_retention_head WG.orM; unfold WG.orM WG.andM; simp only [branch])
  | (rx_retention_head WG.andM; unfold WG.andM; simp only [branch])
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head hiddenClock64; exact hoare_liftAmbient (AmbientM.hiddenClock64 _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | resident_handshake_leaf)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
