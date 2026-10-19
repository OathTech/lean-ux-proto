import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialBoundsFrames
import Leanux.Proofs.WG.RetirementSecurity.RxCompletionWireFrames

/-! Native receive completion frames for older TX key material. Confirmation
may delete an old key; only surviving references retain material obligations. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins Origins.Retaining RxCredits

theorem lower_owner_geometry {action : WG.M α}
    (same : SameView OwnerCompletion.geometry action) : Preserves (Lower bound) action := by
  apply lower_frame
  apply same.of_factor (fun obs => obs.1.map (fun fields => fields.2.2)) cursor
  intro w
  simp only [cursor,OwnerCompletion.geometry,Option.map_map,Function.comp_def]

theorem confirmation_core (pid : PeerId) (kid : KeypairId) :
    CoreRetains (receivedWithKeypair pid kid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Responder.Retains initial (pool w))
    (Q := fun _ w => Responder.Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Responder.Retains.refl _
  unfold receivedWithKeypair
  material_lower
  repeat' first
    | (index_material_head keypairPut; exact (keypairPut_core _ _).wp initial)
    | core_traffic (Responder.Retains initial)

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    Preserves (Inv h) (receivedWithKeypair pid kid) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.confirmation_cryptWire pid kid))
    (confirmation_core pid kid)
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid))

theorem endpoint (pid : PeerId) (ep : Endpoint) : Preserves (Inv h) (setPeerEndpoint pid ep) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.endpoint_cryptWire pid ep))
    (core_of_same (pool_of_material (setPeerEndpoint_material pid ep)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep))

theorem complete (pid : PeerId) (site : HiddenSite) : Preserves (Inv h) (timersHandshakeComplete pid site) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.handshakeComplete_cryptWire pid site))
    (core_of_same (pool_of_material (timersHandshakeComplete_material pid site)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.handshake_geometry) pid site))

theorem lower_prepare (pid : PeerId) (pkt : RxPacket) : Preserves (Lower bound) (prepareRest pid pkt) := by
  unfold prepareRest timersAnyAuthenticatedPacketReceived WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keepKeyFreshRx
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.fresh_geometry) _))
    | (allocation_release_head delTimer
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) _ _))
    | (allocation_release_head timersTraversal
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.traversal_geometry) _))
    | (allocation_release_head timersDataReceived
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.dataReceived_geometry) _))
    | (allocation_release_head updateRxStats
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.stats_geometry) _ _))
    | (allocation_release_head dishonest
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.dishonest_geometry) _))
    | (allocation_release_head inetEcnDecapsulate
       exact lower_frame ((inetEcnDecapsulate_sameWGStore _ _ _).of_factor
         (fun s : WGStoreView => cursor {dev := s.dev}) cursor (fun _ => rfl)))
    | resident_lower_step

theorem prepare (pid : PeerId) (pkt : RxPacket) : Preserves (Inv h) (prepareRest pid pkt) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.prepareRest_cryptWire pid pkt))
    (core_of_same (prepareRest_core pid pkt)) (fun _ => lower_prepare pid pkt)

theorem lower_finish (pid : PeerId) (ready : Packets.RxReady) :
    Preserves (Lower bound) (Packets.rxFinish pid ready) := by
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head lookupSrc
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.lookup_geometry) _ _))
    | (allocation_release_head updateRxStats
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.stats_geometry) _ _))
    | (allocation_release_head dishonest
       exact lower_owner_geometry ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.dishonest_geometry) _))
    | resident_lower_step

theorem finish (pid : PeerId) (ready : Packets.RxReady) : Preserves (Inv h) (Packets.rxFinish pid ready) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.finishRx_cryptWire pid ready))
    (core_of_same (rxFinish_core pid ready)) (fun _ => lower_finish pid ready)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
