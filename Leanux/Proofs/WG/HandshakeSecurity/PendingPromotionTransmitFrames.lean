import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionPacketFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTimerFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins

/-- Native pending projection facts at C2 pin
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`, with no history premise. -/
structure H1TransmitFrames : Prop where
  /-- `Noise.PendingTickets.send4_cached_frame`. -/
  send4 : ∀ pid ep bytes ds exactRx, SameView view (WG.send4 ep (some pid) bytes ds exactRx)
  /-- `Noise.PendingTickets.send6_cached_frame`. -/
  send6 : ∀ pid ep bytes ds exactRx, SameView view (WG.send6 ep (some pid) bytes ds exactRx)
  /-- `Noise.PendingTickets.timersDataSent_frame`. -/
  dataSent : ∀ pid, SameView view (timersDataSent pid)
  /-- `Noise.PendingTickets.sendQueuedHandshakeInitiation_retained`. -/
  queued : ∀ pid retry, ProjectedAction view Retained (sendQueuedHandshakeInitiation pid retry)

theorem Carrier.send4 (frames : H1TransmitFrames) (pid : PeerId) (ep : Endpoint)
    (bytes : List UInt8) (ds : Nat) (exactRx : Bool) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (WG.send4 ep (some pid) bytes ds exactRx) :=
  Carrier.bounds confirmed
    (ResidentMaterial.bounds_join (ConfiguredRemoval.frame (ConfiguredHandshake.send4_view _ _ _ _ _))
      (CurrentSlots.TxSource.send4_preserves _ _ _ _ _))
    (frame_preserves (frames.send4 pid ep bytes ds exactRx) confirmed)

theorem Carrier.send6 (frames : H1TransmitFrames) (pid : PeerId) (ep : Endpoint)
    (bytes : List UInt8) (ds : Nat) (exactRx : Bool) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (WG.send6 ep (some pid) bytes ds exactRx) :=
  Carrier.bounds confirmed
    (ResidentMaterial.bounds_join (ConfiguredRemoval.frame (ConfiguredHandshake.send6_view _ _ _ _ _))
      (CurrentSlots.TxSource.send6_preserves _ _ _ _ _))
    (frame_preserves (frames.send6 pid ep bytes ds exactRx) confirmed)

theorem Carrier.send_skb (frames : H1TransmitFrames) (pid : PeerId) (bytes : List UInt8)
    (ds : Nat) (confirmed : List Nat) : Preserves (Carrier confirmed) (sendSkbToPeer pid bytes ds) := by
  have count (ret : Bool) : Preserves (Carrier confirmed) (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + bytes.length}
      Pure.pure ret) := by
    simpa only [bind_assoc] using
      preserves_bind (Carrier.modify_peer confirmed pid
        (fun p => {p with txBytes := p.txBytes + bytes.length}) (fun _ => rfl) (fun _ => rfl))
        (fun _ => (preserves_pure ret : Preserves (Carrier confirmed) (Pure.pure ret : WG.M Bool)))
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | env_operation_fact count
    | (rx_retention_head WG.send4; exact Carrier.send4 frames _ _ _ _ _ confirmed)
    | (rx_retention_head WG.send6; exact Carrier.send6 frames _ _ _ _ _ confirmed)
    | pending_carrier_poll_step (), confirmed

theorem Carrier.data_sent (frames : H1TransmitFrames) (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (timersDataSent pid) :=
  Carrier.bounds confirmed
    (ResidentMaterial.bounds_join
      (ConfiguredRemoval.frame
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.dataSent_view) pid))
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTransmit.«0».Leanux.Proofs.WG.CurrentSlots.TxSource.dataSent_preserves) pid))
    (frame_preserves (frames.dataSent pid) confirmed)

theorem Carrier.queued (frames : H1TransmitFrames) (pid : PeerId) (retry : Bool) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (sendQueuedHandshakeInitiation pid retry) :=
  Carrier.from_retained (Responder.DriverCuts.carrier_queued pid retry) (frames.queued pid retry) confirmed

theorem Carrier.fresh (frames : H1TransmitFrames) (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact Carrier.queued frames _ _ confirmed)
    | (rx_retention_head getKeypair; exact Carrier.key_read _ confirmed)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Carrier confirmed))
    | pending_carrier_poll_step (), confirmed

theorem Carrier.data_done (frames : H1TransmitFrames) (handshake : H1PendingHandshakeFrames)
    (pid : PeerId) (item : List SkbId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (createDataDone pid item) := by
  let P := Carrier confirmed
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := Carrier.skb confirmed a
  have traversal : Preserves P (timersTraversal pid) :=
    Carrier.from_frame (Responder.DriverCuts.carrier_traversal pid) (handshake.traversal pid) confirmed
  have authenticated : Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    Carrier.from_frame (Responder.DriverCuts.carrier_sent pid) (handshake.sent pid) confirmed
  have send (bytes : List UInt8) (ds : Nat) : Preserves P (sendSkbToPeer pid bytes ds) :=
    Carrier.send_skb frames pid bytes ds confirmed
  have dataSent : Preserves P (timersDataSent pid) := Carrier.data_sent frames pid confirmed
  have fresh : Preserves P (keepKeyFresh pid) := Carrier.fresh frames pid confirmed
  change Preserves P _
  routing_tx_source [createDataDone] using [traversal,authenticated,send,dataSent,fresh,skb,ambient]

theorem Carrier.tx_step (frames : H1TransmitFrames) (handshake : H1PendingHandshakeFrames) (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := Carrier confirmed
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (liftSkb a) := Carrier.skb confirmed a
  have complete (item : List SkbId) : Framing.Preserves P (createDataDone pid item) := Carrier.data_done frames handshake pid item confirmed
  have key (kp : Option KeypairId) : Framing.Preserves P (keypairPut kp false) := Carrier.key_put confirmed kp false
  have put : Framing.Preserves P (peerPut (some pid)) := Carrier.peer_put confirmed (some pid)
  have dispose (item : List SkbId) (kp : KeypairId) : Framing.Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have update (f : Peer → Peer) (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
      (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
      Framing.Preserves P (do let p ← getPeer pid; setPeer pid (f p)) := Carrier.modify_peer confirmed pid f same configured
  have drop : Framing.Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => rfl) (fun _ => rfl)
  have body (first : Option (List SkbId)) : Framing.Preserves P (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [skb, ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases head : item.head? with
          | none => simp only [head]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [head]
            apply preserves_bind (skb (SkbStore.getTx headId))
            intro packet
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete, dispose, ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (hoare_consequence (Carrier.get_peer confirmed pid) (fun _ hi => hi) (fun _ _ hi => hi.1))
  intro p
  apply preserves_bind (Carrier.store confirmed (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first, queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => rfl) (fun _ => rfl)) (fun _ => body first)

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
