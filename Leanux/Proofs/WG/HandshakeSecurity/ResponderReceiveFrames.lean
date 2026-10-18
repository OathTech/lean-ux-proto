import Leanux.Proofs.WG.HandshakeSecurity.ResponderRetention
import Leanux.Proofs.WG.HandshakeSecurity.ResponderNativeClaims
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationInitialized

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes Queues.RxCredits

theorem authorization_of_frames {a : WG.M α} (keys : SameView pool a)
    (slots : KeyEffects NoPromotion a) (confirmed : List Nat) : Preserves (Authorized confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b entry run
  apply entry.retain ((KeyEffects.iff_run_ambient _ _).mp slots w amb result v b run)
  have same := (hoare_iff_run_ambient _ _ _).mp (keys (pool w)) w amb result v b rfl run
  rw [same]
  exact Retains.refl _

theorem keepKeyFreshRx_core (pid : PeerId) : SameView pool (keepKeyFreshRx pid) := by
  intro initial
  unfold keepKeyFreshRx
  material_lower
  repeat' first
    | (index_material_head sendQueuedHandshakeInitiation; exact (queued_core _ _).wp (fun p => p = initial))
    | core_traffic (fun p => p = initial)

theorem prepareRest_core (pid : PeerId) (pkt : RxPacket) : SameView pool (prepareRest pid pkt) := by
  intro initial
  unfold prepareRest
  material_lower
  repeat' first
    | traffic_join
    | (index_material_head keepKeyFreshRx; exact (keepKeyFreshRx_core _).wp (fun p => p = initial))
    | (index_material_head timersAnyAuthenticatedPacketReceived; exact (pool_of_material (timersAnyAuthenticatedPacketReceived_material _)).wp (fun p => p = initial))
    | (index_material_head timersTraversal; exact (pool_of_material (timersTraversal_material _)).wp (fun p => p = initial))
    | (index_material_head timersDataReceived; exact (pool_of_material (timersDataReceived_material _)).wp (fun p => p = initial))
    | (index_material_head updateRxStats; exact (pool_of_material (updateRxStats_material _ _)).wp (fun p => p = initial))
    | (index_material_head dishonest; exact (pool_of_material (dishonest_material _)).wp (fun p => p = initial))
    | (index_material_head inetEcnDecapsulate; exact (pool_of_material (sameView_of_sameWG (project := id) (inetEcnDecapsulate_sameWGStore _ _ _))).wp (fun p => p = initial))
    | core_traffic (fun p => p = initial)

theorem rxFinish_core (pid : PeerId) (ready : Packets.RxReady) : SameView pool (Packets.rxFinish pid ready) := by
  apply pool_of_material
  intro initial
  unfold Packets.rxFinish Packets.rxAfterLookup
  material_lower
  repeat' first
    | (index_material_head lookupSrc; exact (lookupSrc_material _ _).wp (fun p => p = initial))
    | (index_material_head updateRxStats; exact (updateRxStats_material _ _).wp (fun p => p = initial))
    | (index_material_head dishonest; exact (dishonest_material _).wp (fun p => p = initial))
    | traffic_basic (fun p => p = initial)

theorem endpoint_authorized (pid : PeerId) (ep : Endpoint) (confirmed : List Nat) :
    Preserves (Authorized confirmed) (setPeerEndpoint pid ep) :=
  authorization_of_frames (pool_of_material (setPeerEndpoint_material pid ep))
    (control_keyEffects (project := id) (allowed := NoPromotion) (setPeerEndpoint_control pid ep)) confirmed

/-- Every native operation after confirmation retains the responder history
invariant, including staged sends, receive timers, source routing and drops. -/
theorem afterConfirmation_authorized (pid : PeerId) (pkt : RxPacket) (accepted : Bool)
    (confirmed : List Nat) : Preserves (Authorized confirmed) (Confirmation.afterConfirmation pid pkt accepted) := by
  have timer := authorization_of_frames
    (pool_of_material (timersHandshakeComplete_material pid .walltimeLastHandshakeData))
    (control_keyEffects (project := id) (allowed := NoPromotion)
      (timersHandshakeComplete_control pid .walltimeLastHandshakeData)) confirmed
  have rest := authorization_of_frames (prepareRest_core pid pkt)
    (prepareRest_keyEffect (allowed := NoPromotion) pid pkt) confirmed
  have finish := fun ready => authorization_of_frames (rxFinish_core pid ready)
    (keyEffects_view (project := id) (allowed := NoPromotion) (rxFinish_keyView pid ready)) confirmed
  unfold Confirmation.afterConfirmation
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .doneReceivedNew accepted) (Authorized confirmed))
  intro yes
  split
  · apply preserves_bind timer
    intro _
    apply preserves_bind (sendStagedPackets_authorized pid confirmed)
    intro _
    apply preserves_bind rest
    intro ready
    cases ready with
    | none => exact preserves_pure _
    | some r => exact finish r
  · apply preserves_bind rest
    intro ready
    cases ready with
    | none => exact preserves_pure _
    | some r => exact finish r

/-- A completed actual consumer carries responder authorization from entry,
adding the actual confirmed allocation at the native receipt before its suffix.
Authentication and initialized caller transport are supplied separately. -/
theorem completed_consumer_authorized (H1 : H1ResponderCurrentEdges)
    (confirmed : List Nat) (r : Queues.RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool)
    (cut : Confirmation.SourceCut r c) (entry : Authorized confirmed r.run.before) :
    Authorized (confirmed ++ confirmedAt c.before r.packet.keypair c.value) r.run.after := by
  have endpoint := (hoare_iff_run_ambient _ _ _).mp
    (endpoint_authorized r.peer r.endpoint confirmed) _ _ _ _ _ entry cut.1
  have promoted := confirmation_authorized H1 r.peer r.packet.keypair confirmed
    c.before c.after c.ambientBefore c.ambientAfter c.value endpoint cut.2.1
  exact (hoare_iff_run_ambient _ _ _).mp
    (afterConfirmation_authorized r.peer r.packet c.value _) _ _ _ _ _ promoted cut.2.2

end Leanux.Proofs.WG.HandshakeSecurity.Responder
