import Leanux.Proofs.WG.Origins.OwnerEncrypt
import Leanux.Proofs.WG.Origins.OwnerLifecycle
import Leanux.Proofs.WG.Origins.CurrentEnvironment

/-! Native TX completion retains the receiving-owner carrier, including
partial release and failed source guards. The iteration callback retains its
arbitrary actual product domain under an explicit preservation contract. -/
namespace Leanux.Proofs.WG.OwnerTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerControls
open Origins.HistorySupport (sensitive)

theorem sendQueuedHandshakeInitiation_preserves (pid : PeerId) (retry : Bool) :
    Preserves Carrier (sendQueuedHandshakeInitiation pid retry) :=
  OwnerCompletion.preserves_of_frames _ (Origins.Retaining.sendQueuedHandshakeInitiation_material pid retry)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.sendQueued_geometry) pid retry)
    (queued_keyEffect (allowed := NoPromotion) pid retry)

private theorem sendSkb_preserves (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves Carrier (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head send4; exact OwnerLifecycle.send4_preserves _ _ _ _ _)
    | (allocation_release_head send6; exact OwnerLifecycle.send6_preserves _ _ _ _ _)
    | owner_control_step

private theorem dataSent_preserves (pid : PeerId) : Preserves Carrier (timersDataSent pid) := by
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Carrier)
    | (allocation_release_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp Carrier)
    | (allocation_release_head armTimer
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.armTimer_preserves) _ _ _ _)
    | owner_control_step

private theorem fresh_preserves (pid : PeerId) : Preserves Carrier (keepKeyFresh pid) := by
  have read (key : KeypairId) : Preserves Carrier (getKeypair key) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (allocation_release_head getKeypair; exact read _)
    | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp Carrier)
    | (allocation_release_head sendQueuedHandshakeInitiation; exact sendQueuedHandshakeInitiation_preserves _ _)
    | owner_control_step

theorem createDataDone_preserves (pid : PeerId) (item : List SkbId) :
    Preserves Carrier (createDataDone pid item) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves Carrier (monadLift a : WG.M α) := hoare_liftAmbient a Carrier
  have read (id : SkbId) : Preserves Carrier (getTxSkb id) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.skb) _
      ((getTx_protect id).of_factor (fun v => v.2.1) _ (fun _ => rfl))
  have traversal : Preserves Carrier (timersTraversal pid) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.traversal_preserves) pid
  have authenticated : Preserves Carrier (timersAnyAuthenticatedPacketSent pid) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerLifecycle.«0».Leanux.Proofs.WG.OwnerLifecycle.sent_preserves) pid
  have send (bytes : List UInt8) (ds : Nat) : Preserves Carrier (sendSkbToPeer pid bytes ds) := sendSkb_preserves _ _ _
  have dataSent : Preserves Carrier (timersDataSent pid) := dataSent_preserves pid
  have fresh : Preserves Carrier (keepKeyFresh pid) := fresh_preserves pid
  routing_tx_source [createDataDone] using [read,traversal,authenticated,send,dataSent,fresh,ambient]

theorem txStep_preserves (pid : PeerId) : Preserves Carrier (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  have ambient {α : Type} (a : AmbientM α) : Preserves Carrier (monadLift a : WG.M α) := hoare_liftAmbient a Carrier
  have read (id : SkbId) : Preserves Carrier (getTxSkb id) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.skb) _
      ((getTx_protect id).of_factor (fun v => v.2.1) _ (fun _ => rfl))
  have free (id : SkbId) : Preserves Carrier (freeTxSkb id) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.skb) _
      ((freeTx_protect id).of_factor (fun v => v.2.1) _ (fun _ => rfl))
  have complete (item : List SkbId) : Preserves Carrier (createDataDone pid item) := createDataDone_preserves _ _
  have key (kp : Option KeypairId) : Preserves Carrier (keypairPut kp false) := OwnerCreation.keypairPut_preserves _ _
  have put : Preserves Carrier (peerPut (some pid)) := OwnerConsume.peerPut_preserves _
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves Carrier (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [free,key,put]
  have update (f : Peer → Peer) : Preserves Carrier (do let p ← getPeer pid; setPeer pid (f p)) :=
    preserves_bind (readPeer pid) (fun p => writePeer pid (f p))
  have drop : Preserves Carrier (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _
  have body (first : Option (List SkbId)) : Preserves Carrier (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [read,ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none => simp only [hh]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (read headId)
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete,dispose,ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (readPeer pid)
  intro p
  apply preserves_bind (store _ (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first,queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue})) (fun _ => body first)

theorem txIter_preserves (pid : PeerId) (need : Leanux.M Bool)
    (hn : Preserves (fun w : World => Carrier w.wg) need) :
    Preserves (fun w : World => Carrier w.wg) (txIter pid need) := by
  let P := fun w : World => Carrier w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product)
      _ (txStep_preserves pid)
  have needSpec : Preserves P need := hn
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,needSpec,ambient]

theorem txIteration (pid : PeerId) :
    OwnerChecks.Preserves (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) := by
  apply OwnerChecks.quiet _ (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.txIteration) pid
  · exact RxHistory.mixed_preserves
      ((pinned_const _private.Leanux.Proofs.WG.Queues.RxActivationHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.tx_allocation) pid)
  · intro w h hi result v hr
    apply (hoare_iff_run _ _ _).mp (txIter_preserves pid _
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.product_store)
        _ (condResched_sameKernel _))) w result v hi.carrier
    exact ((RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _)) w h).symm.trans hr)

end Leanux.Proofs.WG.OwnerTransmit
