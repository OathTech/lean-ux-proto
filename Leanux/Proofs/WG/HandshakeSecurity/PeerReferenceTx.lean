import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEncrypt

/-! Native completion and final disposal preserve positive resident peers. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat)  :
    Framing.Preserves (Inv) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.send4; exact send4 _ _ _ _ _)
    | (rx_retention_head WG.send6; exact send6 _ _ _ _ _)
    | peer_reference_timer_step

theorem fresh_tx (pid : PeerId)  :
    Framing.Preserves (Inv) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | peer_reference_timer_step

theorem data_done (pid : PeerId) (item : List SkbId)  :
    Framing.Preserves (Inv) (createDataDone pid item) := by
  unfold createDataDone WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
    | (rx_retention_head timersDataSent; exact data_sent _)
    | (rx_retention_head sendSkbToPeer; exact send_skb _ _ _)
    | (rx_retention_head keepKeyFresh; exact fresh_tx _)
    | peer_reference_timer_step

theorem tx_step_frame (pid : PeerId)  :
    Framing.Preserves (Inv) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := Inv
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (liftSkb a) := PeerReference.skb a
  have complete (item : List SkbId) : Framing.Preserves P (createDataDone pid item) := data_done pid item
  have key (kp : Option KeypairId) : Framing.Preserves P (keypairPut kp false) := key_put kp false
  have put : Framing.Preserves P (peerPut (some pid)) := peer_put (some pid)
  have dispose (item : List SkbId) (kp : KeypairId) : Framing.Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have update (f : Peer → Peer)
      (same : ∀ p, 0 < p.refcount → 0 < (f p).refcount) :
      Framing.Preserves P (do let p ← getPeer pid; setPeer pid (f p)) := update_peer pid f same
  have drop : Framing.Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ positive => positive)
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
  apply preserves_bind (read_peer pid)
  intro p
  apply preserves_bind (store (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first, queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ positive => positive)) (fun _ => body first)

theorem tx_iteration (pid : PeerId) :
    ProductPreserves (TransmitSecurity.Driver.txIterObserved ExchangeDriver.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1)
    (product_native _ (tx_step_frame pid)) (resched _ _)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
