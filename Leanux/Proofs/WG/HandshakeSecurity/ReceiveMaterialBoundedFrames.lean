import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialKeyBounds

/-! Concrete native frames carry RX certificates and only the key-slot bound
needed at preparation. Reference disposal may delete keys; no survival premise
or reference-account invariant is introduced. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Responder Origins.Retaining

theorem bounded_join {action : WG.M α} (material : Preserves (Inv h) action)
    (bounds : Preserves KeyBounds action) : Preserves (Bounded h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp material w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp bounds w a result v b before.2 run⟩

theorem bounded_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Bounded h) action :=
  bounded_frame (AuthenticatedEffects.TransportPublication.store_rx action same)
    (ResidentMaterial.core_of_same (same.of_factor
      (fun s => pool {dev := s.dev}) pool (fun _ => rfl)))
    (fun _ => ResidentMaterial.lower_frame (same.of_factor
      (fun s => ResidentMaterial.cursor {dev := s.dev}) ResidentMaterial.cursor (fun _ => rfl)))

theorem key_bounds_store {action : WG.M α} (same : SameWGStore action) :
    Preserves KeyBounds action :=
  key_bounds_frame (ResidentMaterial.core_of_same (same.of_factor
    (fun s => pool {dev := s.dev}) pool (fun _ => rfl)))
    (fun _ => ResidentMaterial.lower_frame (same.of_factor
      (fun s => ResidentMaterial.cursor {dev := s.dev}) ResidentMaterial.cursor (fun _ => rfl)))

theorem key_bounds_counter (kid : KeypairId) (nonce : Nat) :
    Preserves KeyBounds (counterValidate kid nonce) :=
  key_bounds_frame (ResidentMaterial.core_of_same (counter_core kid nonce))
    (fun _ => ResidentMaterial.NativeFrames.lower_slot_fields
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotPoll.«0».Leanux.Proofs.WG.CurrentSlots.counter_fields) kid nonce))

theorem key_bounds_endpoint (pid : PeerId) (ep : Endpoint) :
    Preserves KeyBounds (setPeerEndpoint pid ep) :=
  key_bounds_frame (ResidentMaterial.core_of_same (pool_of_material (setPeerEndpoint_material pid ep)))
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep))

theorem key_bounds_key_put (kid : Option KeypairId) (now : Bool) :
    Preserves KeyBounds (keypairPut kid now) :=
  key_bounds_frame (keypairPut_core kid now)
    (fun _ => ResidentMaterial.lower_metadata ((keypairPut_rest kid now).factor (fun rest => rest.2.2)))

theorem key_bounds_read_peer (pid : PeerId) : Preserves KeyBounds (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Peers.getPeer_current pid w v result a b run).1 ▸ before

theorem key_bounds_set_peer (pid : PeerId) (peer : Peer) : Preserves KeyBounds (setPeer pid peer) :=
  key_bounds_frame (ResidentMaterial.core_of_same (pool_of_material (modifyDev_material _ (fun _ => rfl))))
    (fun _ => ResidentMaterial.lower_metadata (setPeer_metadata pid peer))

theorem key_bounds_peer_put (pid : Option PeerId) : Preserves KeyBounds (peerPut pid) :=
  key_bounds_frame (ResidentMaterial.core_of_same (pool_of_material (peerPut_material pid)))
    (fun _ => ResidentMaterial.lower_metadata (peerPut_metadata pid))

theorem bounded_counter (kid : KeypairId) (nonce : Nat) :
    Preserves (Bounded h) (counterValidate kid nonce) :=
  bounded_join (counter kid nonce) (key_bounds_frame
    (ResidentMaterial.core_of_same (counter_core kid nonce))
    (fun _ => ResidentMaterial.NativeFrames.lower_slot_fields
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotPoll.«0».Leanux.Proofs.WG.CurrentSlots.counter_fields) kid nonce)))

theorem bounded_confirmation (pid : PeerId) (kid : KeypairId) :
    Preserves (Bounded h) (receivedWithKeypair pid kid) :=
  bounded_join (confirmation pid kid) (key_bounds_frame
    (ResidentMaterial.NativeFrames.confirmation_core pid kid)
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid)))

theorem bounded_endpoint (pid : PeerId) (ep : Endpoint) :
    Preserves (Bounded h) (setPeerEndpoint pid ep) :=
  bounded_join (endpoint pid ep) (key_bounds_frame
    (ResidentMaterial.core_of_same (pool_of_material (setPeerEndpoint_material pid ep)))
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep)))

theorem bounded_key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Bounded h) (keypairPut kid now) :=
  bounded_join (key_put kid now) (key_bounds_frame (keypairPut_core kid now)
    (fun _ => ResidentMaterial.lower_metadata ((keypairPut_rest kid now).factor (fun rest => rest.2.2))))

theorem bounded_read_peer (pid : PeerId) : Preserves (Bounded h) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Peers.getPeer_current pid w v result a b run).1 ▸ before

theorem bounded_set_peer (pid : PeerId) (peer : Peer) : Preserves (Bounded h) (setPeer pid peer) :=
  bounded_join (set_peer pid peer) (key_bounds_frame
    (ResidentMaterial.core_of_same (pool_of_material (modifyDev_material _ (fun _ => rfl))))
    (fun _ => ResidentMaterial.lower_metadata (setPeer_metadata pid peer)))

theorem bounded_peer_put (pid : Option PeerId) : Preserves (Bounded h) (peerPut pid) :=
  bounded_join (peer_put pid) (key_bounds_frame
    (ResidentMaterial.core_of_same (pool_of_material (peerPut_material pid)))
    (fun _ => ResidentMaterial.lower_metadata (peerPut_metadata pid)))

theorem key_bounds_skb (action : SkbM α) : Preserves KeyBounds (liftSkb action) :=
  key_bounds_frame (ResidentMaterial.core_of_same
    ((ResidentMaterial.skb_allocation_view action).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame
      ((ResidentMaterial.skb_allocation_view action).factor (fun fields => fields.2.1)))

theorem bounded_read_rx (id : SkbId) : Preserves (Bounded h) (getRxSkb id) :=
  bounded_join (read_rx id) (key_bounds_skb _)

theorem bounded_free_rx (id : SkbId) : Preserves (Bounded h) (freeRxSkb id) :=
  bounded_join (free_rx id) (key_bounds_skb _)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
