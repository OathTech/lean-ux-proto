import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionNapi
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverWorkerFrames

/-! Packet workers retain pending allocation identities. These frames use
native C1 packet/slot access and source factors; no confirmation history is
assumed and no new session-transition contract is introduced. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins

/-- Per-native-call TX publication retention. At C2 pin
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`, this is the operational component
of `Noise.PendingCrypt.enqueue_native`: `PendingTickets.retained_of_staging_ordinary`
with `Index.enqueuePerPeerTx_staging` and the unchanged C1 key snapshot.
The statement has no confirmation-history argument. -/
structure H1PublicationFrame : Prop where
  publication : ∀ item state, ProjectedAction view Retained (enqueuePerPeerTx item state)

theorem Carrier.publication (frames : H1PublicationFrame) (item : List SkbId) (state : PacketState)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (enqueuePerPeerTx item state) :=
  Carrier.from_retained (Responder.DriverCuts.carrier_publication item state)
    (frames.publication item state) confirmed

theorem Carrier.key_read (kid : KeypairId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b hi run
  exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ hi

theorem decrypt_frame (pkt : RxPacket) : SameView view (decryptPacket pkt) := by
  intro initial
  let P := fun w => view w = initial
  have read (kid : KeypairId) : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi run
    exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ hi
  have invalid : Preserves P (do
      let k ← getKeypair pkt.keypair
      setKeypair pkt.keypair {k with receiving := {k.receiving with isValid := false}}
      Pure.pure (none : Option RxPacket)) := by
    simpa only [bind_assoc] using preserves_bind
      ((modify_key pkt.keypair (fun k => {k with receiving := {k.receiving with isValid := false}})
        (fun _ => rfl)).wp (fun p => p = initial))
      (fun _ => (preserves_pure (none : Option RxPacket) : Preserves P _))
  change Preserves P _
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) P)
  intro noKey
  cases noKey with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (read pkt.keypair)
    intro key
    apply preserves_bind ((Origins.receiveReject_sameWGWorld key).wp P)
    intro rejected
    cases rejected with
    | true => exact invalid
    | false => exact (Origins.receiveTail_sameWGWorld pkt key).wp P

theorem Carrier.decrypt (pkt : RxPacket) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (decryptPacket pkt) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_decrypt pkt) (decrypt_frame pkt) confirmed

theorem publish_frame (id : SkbId) (state : PacketState) : SameView view (RxWorkers.publishSource id state) := by
  apply frame (CurrentSlots.publish_fields id state)
  have deref (owner : IndexOwner) : Keypairs.SameSnapshot owner.peerDeref :=
    fun initial => indexOwner_peerDeref_preserves owner (fun w => Keypairs.snapshot w = initial)
  snapshot_source [RxWorkers.publishSource] using [deref,Keypairs.WGFrames.peerGet_sameSnapshot,
    Keypairs.WGFrames.getPeer_sameSnapshot,Keypairs.WGFrames.setPeer_sameSnapshot]
  exact deref _

theorem Carrier.rx_publish (id : SkbId) (state : PacketState) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (RxWorkers.publishSource id state) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_rx_publish id state) (publish_frame id state) confirmed

theorem Carrier.prepare_worker (confirmed : List Nat) :
    Preserves (Carrier confirmed) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact Carrier.decrypt _ confirmed)
    | (rx_retention_head RxWorkers.publishSource; exact Carrier.rx_publish _ _ confirmed)
    | (rx_retention_head getDev; exact Carrier.store confirmed getDev_sameWGStore)
    | (rx_retention_head setRxSkb; exact Carrier.skb confirmed _)
    | pending_carrier_poll_step (), confirmed

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
