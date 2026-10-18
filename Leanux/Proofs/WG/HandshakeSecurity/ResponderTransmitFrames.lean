import Leanux.Proofs.WG.HandshakeSecurity.ResponderAuditedHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits

theorem readKey_native (kid : KeypairId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b entry run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ entry

theorem sendSkb_native (pid : PeerId) (bytes : List UInt8) (ds : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4
       exact sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send4_view) _ _ _ _ _)
         (CurrentSlots.TxSource.send4_preserves _ _ _ _ _) confirmed)
    | (rx_retention_head send6
       exact sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send6_view) _ _ _ _ _)
         (CurrentSlots.TxSource.send6_preserves _ _ _ _ _) confirmed)
    | responder_handshake_step confirmed

-- Keep the optional jiffies argument explicit when pinning C1's private frame.
macro "responder_arm_frame" : term => do
  let n := Lean.mkCIdent (normalizePinnedName `_private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.armTimer_view)
  `(term| @$n)

theorem dataSent_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (timersDataSent pid) := by
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (History.Native confirmed))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (History.Native confirmed))
    | (rx_retention_head armTimer
       exact sendView_native (responder_arm_frame _ _ _ _)
         (CurrentSlots.armTimer_preserves _ _ _ _) confirmed)
    | responder_handshake_step confirmed


theorem fresh_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch, branchCmp, invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_native _ _ confirmed)
    | (rx_retention_head getKeypair; exact readKey_native _ confirmed)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (History.Native confirmed))
    | responder_handshake_step confirmed

theorem createDataDone_native (pid : PeerId) (item : List SkbId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (createDataDone pid item) := by
  let P := History.Native confirmed
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := native_skb a confirmed
  have traversal : Preserves P (timersTraversal pid) :=
    sendView_native ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersTraversal_view) pid)
      (CurrentSlots.timersTraversal_preserves pid) confirmed
  have authenticated : Preserves P (timersAnyAuthenticatedPacketSent pid) := delTimer_native pid .sendKeepalive confirmed
  have send (bytes : List UInt8) (ds : Nat) : Preserves P (sendSkbToPeer pid bytes ds) := sendSkb_native pid bytes ds confirmed
  have dataSent : Preserves P (timersDataSent pid) := dataSent_native pid confirmed
  have fresh : Preserves P (keepKeyFresh pid) := fresh_native pid confirmed
  change Preserves P _
  routing_tx_source [createDataDone] using [traversal, authenticated, send, dataSent, fresh, skb, ambient]

/-- The native TX worker changes no responder authorization except by deleting
already authorized obligations. This frames execution; it does not yet connect
each resident TX packet to its earlier staging-selection witness. -/
theorem txStep_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := History.Native confirmed
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := native_skb a confirmed
  have complete (item : List SkbId) : Preserves P (createDataDone pid item) := createDataDone_native pid item confirmed
  have key (kp : Option KeypairId) : Preserves P (keypairPut kp false) := keypairPut_native kp false confirmed
  have put : Preserves P (peerPut (some pid)) := peerPut_native (some pid) confirmed
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have update (f : Peer → Peer) (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) :
      Preserves P (do let p ← getPeer pid; setPeer pid (f p)) := peerUpdate_native pid f same confirmed
  have drop : Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => rfl)
  have body (first : Option (List SkbId)) : Preserves P (TxDisposition.bodySource pid first) := by
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
  apply preserves_bind (readPeer_native pid confirmed)
  intro p
  apply preserves_bind (native_store (prevQueuePeek_sameWGStore p.txQueue) confirmed)
  intro out
  rcases out with ⟨first, queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => rfl)) (fun _ => body first)

theorem txIter_native (pid : PeerId) (need : Leanux.M Bool) (confirmed : List Nat)
    (reschedule : Preserves (AuditedFrames.State confirmed) need) :
    Preserves (AuditedFrames.State confirmed) (txIter pid need) := by
  let P := AuditedFrames.State confirmed
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product _ _ (txStep_native pid confirmed)
  have effect {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  change Preserves P _
  routing_tx_source [txIter, workerIter] using [step, reschedule, effect]

theorem Joint.txIteration (pid : PeerId) :
    Joint.Preserves (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  Joint.from_global _ (PublicationJoint.txIteration pid)
    (Global.mixed _ _ (txIterPrefix_erases pid (erasesPrefix_lift _))
      (fun confirmed => txIter_native pid _ confirmed (native_product_store (condResched_sameKernel _) confirmed)))

end Leanux.Proofs.WG.HandshakeSecurity.Responder
