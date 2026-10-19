import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveEncrypt

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.send4; exact send4 _ _ _ _ _ history)
    | (rx_retention_head WG.send6; exact send6 _ _ _ _ _ history)
    | archive_timer_step history

theorem fresh_tx (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _ history)
    | archive_timer_step history

theorem data_done (pid : PeerId) (item : List SkbId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (createDataDone pid item) := by
  unfold createDataDone WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact traversal _ history)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _ history)
    | (rx_retention_head timersDataSent; exact data_sent _ history)
    | (rx_retention_head sendSkbToPeer; exact send_skb _ _ _ history)
    | (rx_retention_head keepKeyFresh; exact fresh_tx _ history)
    | archive_timer_step history

theorem tx_step_frame (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := StateInv history
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (liftSkb a) := TimestampArchive.skb a history
  have complete (item : List SkbId) : Framing.Preserves P (createDataDone pid item) := data_done pid item history
  have key (kp : Option KeypairId) : Framing.Preserves P (keypairPut kp false) := key_put kp false history
  have put : Framing.Preserves P (peerPut (some pid)) := peer_put (some pid) history
  have dispose (item : List SkbId) (kp : KeypairId) : Framing.Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have update (f : Peer → Peer)
      (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp) :
      Framing.Preserves P (do let p ← getPeer pid; setPeer pid (f p)) := update_peer pid f same history
  have drop : Framing.Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => ⟨rfl,rfl⟩)
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
  apply preserves_bind (read_peer pid history)
  intro p
  apply preserves_bind (frame_store history _ (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first, queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => ⟨rfl,rfl⟩)) (fun _ => body first)

theorem tx_iteration (pid : PeerId) :
    ProductPreserves (TransmitSecurity.Driver.txIterObserved TimestampDriver.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1)
    (product_native _ (tx_step_frame pid)) (resched _ _)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
