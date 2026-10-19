import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialNativeFrames

/-! Native staging refusal and publication retain the conditional sending-key
binding of every surviving TX packet. Allocating fresh packets is treated by
the separate admission contract, never as a frame. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

macro "resident_lower_step" : tactic => `(tactic| first
  | (allocation_release_head getDev
     exact lower_frame (getDev_sameWGStore.of_factor
       (fun store : WGStoreView => store.dev.map (·.nextKeypairId)) cursor (fun _ => rfl)))
  | (allocation_release_head modifyDev; exact lower_metadata (metadata_modifyDev _ (fun _ => rfl)))
  | (allocation_release_head peerGet; exact lower_metadata (peerGet_metadata _))
  | (allocation_release_head peerPut; exact lower_metadata (peerPut_metadata _))
  | (allocation_release_head branchExpired; exact lower_frame ((branchExpired_sameWGWorld _ _ _ _).factor cursor))
  | (allocation_release_head ForIn.forIn
     apply list_view_spec cursor (fun cell => ∀ front, cell = some front → _ ≤ front)
     intro x acc
     change Preserves (Lower _) _)
  | material_cursor_step)

theorem lower_queued (pid : PeerId) (retry : Bool) :
    Preserves (Lower bound) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' resident_lower_step

theorem lower_no_key (pid : PeerId) (packets : List WG.Packet)
    (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Lower bound) (stagedOutNokey pid packets kid invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation; exact lower_queued _ _)
    | resident_lower_step

theorem no_key (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Inv h) (stagedOutNokey pid packets kid invalid) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.noKey_cryptWire pid packets kid invalid))
    (stagedOutNokey_core pid packets kid invalid) (fun _ => lower_no_key pid packets kid invalid)

macro "resident_staging_step" : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact read_peer _)
  | (rx_retention_head getTxSkb; exact read_packet _)
  | (rx_retention_head getKeypair; exact read_key _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head setPeer; exact set_peer _ _)
  | (rx_retention_head setTxSkb; exact write_packet _ _ (fun _ => rfl))
  | (rx_retention_head freeTxSkb; exact free_packet _)
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head keypairGet; exact key_get _)
  | (rx_retention_head keypairPut; exact key_put _ _)
  | (rx_retention_head modifyDev
     exact modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv _); intro x b; change Preserves (Inv _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)

theorem enqueue (pid : PeerId) (items : List SkbId) :
    Preserves (Inv h) (enqueuePerDeviceAndPeer pid items) := by
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  simp only [branch,invariant,queueDeviceWork]
  repeat' resident_staging_step

theorem create (pid : PeerId) (items : List SkbId) : Preserves (Inv h) (createData pid items) := by
  unfold createData
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue _ _)
    | (rx_retention_head enqueuePerPeerTx; exact ResidentMaterial.publish _ _)
    | resident_staging_step

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
