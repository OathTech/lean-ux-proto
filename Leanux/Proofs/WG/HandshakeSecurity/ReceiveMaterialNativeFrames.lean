import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialCarrier
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialPollFrames

/-! Native poll and confirmation frames for the RX allocation certificate.
Key disposal retains only surviving cells; no forward residency is assumed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder Origins.Retaining

theorem frame {action : WG.M α}
    (packets : SameView RxDisposition.nativeRxStore action)
    (keys : CoreRetains action)
    (frontier : ∀ bound, Preserves (ResidentMaterial.Lower bound) action) :
    Preserves (Inv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have rx := (ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run
  have core := (ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run
  apply before.retains
  · intro id pkt resident _
    exact ⟨by simpa only [rx] using resident,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst rx)⟩
  · intro d e hd he
    have lower := (hoare_iff_run_ambient _ _ _).mp (frontier d.nextKeypairId)
      w a result v b (by simp [ResidentMaterial.Lower,ResidentMaterial.cursor,hd]) run
    simpa [ResidentMaterial.Lower,ResidentMaterial.cursor,he] using lower
  · intro _ _ slot _ value resident
    exact core slot value resident

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv h) action :=
  frame (TransportPublication.store_rx action same)
    (ResidentMaterial.core_of_same (same.of_factor
      (fun s => pool {dev := s.dev}) pool (fun _ => rfl)))
    (fun _ => ResidentMaterial.lower_frame (same.of_factor
      (fun s => ResidentMaterial.cursor {dev := s.dev}) ResidentMaterial.cursor (fun _ => rfl)))

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Inv h) (counterValidate kid nonce) :=
  frame (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.counter_geometry) kid nonce).factor Prod.snd)
    (ResidentMaterial.core_of_same (counter_core kid nonce))
    (fun _ => ResidentMaterial.NativeFrames.lower_slot_fields
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotPoll.«0».Leanux.Proofs.WG.CurrentSlots.counter_fields) kid nonce))

theorem endpoint (pid : PeerId) (ep : Endpoint) : Preserves (Inv h) (setPeerEndpoint pid ep) :=
  frame (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep).factor Prod.snd)
    (ResidentMaterial.core_of_same (pool_of_material (setPeerEndpoint_material pid ep)))
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep))

theorem confirmation (pid : PeerId) (kid : KeypairId) : Preserves (Inv h) (receivedWithKeypair pid kid) :=
  frame (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid).factor Prod.snd)
    (ResidentMaterial.NativeFrames.confirmation_core pid kid)
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid))

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves (Inv h) (keypairPut kid now) :=
  frame (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) kid now).factor Prod.snd)
    (keypairPut_core kid now)
    (fun _ => ResidentMaterial.lower_metadata ((keypairPut_rest kid now).factor (fun rest => rest.2.2)))

theorem read_peer (pid : PeerId) : Preserves (Inv h) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Peers.getPeer_current pid w v result a b run).1 ▸ before

theorem set_peer (pid : PeerId) (peer : Peer) : Preserves (Inv h) (setPeer pid peer) :=
  frame (TransportPublication.setPeer_rx pid peer)
    (ResidentMaterial.core_of_same (pool_of_material (modifyDev_material _ (fun _ => rfl))))
    (fun _ => ResidentMaterial.lower_metadata (setPeer_metadata pid peer))

theorem peer_put (pid : Option PeerId) : Preserves (Inv h) (peerPut pid) :=
  frame (RxCredits.peerPut_rxView pid)
    (ResidentMaterial.core_of_same (pool_of_material (peerPut_material pid)))
    (fun _ => ResidentMaterial.lower_metadata (peerPut_metadata pid))

theorem read_rx (id : SkbId) : Preserves (Inv h) (getRxSkb id) :=
  frame (TransportPublication.getRxSkb_rx id)
    (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.getRx id)).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame
      ((ResidentMaterial.skb_allocation_view (SkbStore.getRx id)).factor (fun fields => fields.2.1)))

theorem free_rx (id : SkbId) : Preserves (Inv h) (freeRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨cells,stamps,_,_⟩ := PublicationFrontier.freeRxSkb_frame id w v a b run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ResidentMaterial.skb_allocation_view (SkbStore.freeRx id)) w a () v b run
  have cores := congrArg Prod.fst fields
  have frontier := congrArg (fun fields => fields.2.1) fields
  dsimp only [ResidentMaterial.allocationView] at cores frontier
  apply before.retains (fun slot pkt resident _ => ⟨cells slot pkt resident,stamps slot⟩)
  · intro d e hd he
    have same : e.nextKeypairId = d.nextKeypairId := by
      simpa only [ResidentMaterial.allocationView,ResidentMaterial.cursor,hd,he,Option.map_some,Option.some.injEq] using frontier
    exact Nat.le_of_eq same.symm
  · intro _ _ slot _ core resident
    rw [←cores]
    exact resident

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
