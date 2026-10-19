import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerQueue

/-! Queued initiation uses actual native decisions, one queue receipt and a
counted peer repayment. Every prefix is composed on the same accounted ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier HandshakeSecurity.StagedDisposal

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem carrier_safe (before : Carrier debts locals h w a) : CompleteProduct.Safe h := by
  obtain ⟨ledger,before⟩ := before
  exact ⟨debts,.accounted ledger locals h w before⟩

theorem carrier_native (action : WG.M α) (frame : SameView StagedEntry.view action) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (liftWGPrefix action) (fun _=>Carrier debts locals) :=
  single (CompletePassive.native CompleteProduct.Safe
    (fun ledger h w before=>⟨debts,.accounted ledger locals h w before⟩) action frame)
    (fun _ _ _ before=>carrier_safe before) (fun _ _ _ _=>Or.inl rfl)

theorem carrier_ambient (action : AmbientM α) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (liftWGPrefix (monadLift action : WG.M α))
      (fun _=>Carrier debts locals) :=
  carrier_native _ (fun initial=>hoare_liftAmbient action (fun w=>StagedEntry.view w=initial))

theorem carrier_pure (value : α) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (pure value) (fun _=>Carrier debts locals) :=
  StateEnsures.pure value (fun _ _ _ before=>before)

theorem carrier_update (pid : PeerId) (f : Peer→Peer) (next : Unit→WGPrefix CausalJournal.Event α)
    (same : ∀ p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
    (tail : ∀ value,StateEnsures (Carrier debts locals) CompleteProduct.Safe (next value)
      (fun _=>Carrier debts locals)) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe
      (liftWGPrefix (getPeer pid) >>= fun p=>liftWGPrefix (setPeer pid (f p)) >>= next)
      (fun _=>Carrier debts locals) := by
  simpa only [Queued.lift_bind,bind_assoc] using
    StateEnsures.bind (carrier_native _ (Queued.update pid f same)) tail

theorem queue_append (pid : PeerId) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (effects.append pid) (fun _=>Carrier debts locals) := by
  apply single (CompleteTimer.append CompleteProduct.Safe
    (fun ledger h w before=>⟨debts,.accounted ledger locals h w before⟩) pid)
    (fun _ _ _ before=>carrier_safe before)
  intro w a h before
  obtain ⟨ledger,before⟩ := before
  obtain ⟨performed,_,_⟩ := Queued.append_total before.entry pid a
  exact Or.inr ⟨_,congrArg Prod.snd performed⟩

theorem queue_after_reset (pid : PeerId) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe (TimerQueue.afterReset pid)
      (fun _=>Carrier debts locals) := by
  unfold TimerQueue.afterReset
  apply StateEnsures.bind (carrier_native _ (Queued.read pid))
  intro peer
  apply StateEnsures.bind (carrier_native _
    ((branchExpired_sameWGWorld .queuedNotExpired peer.lastSentHandshake REKEY_TIMEOUT (!·)).factor StagedEntry.view))
  intro recent
  split
  · exact carrier_pure ()
  · apply StateEnsures.bind (carrier_ambient (AmbientM.branch .queuedDead peer.isDead))
    intro dead
    split
    · exact carrier_pure ()
    · apply StateEnsures.bind (carrier_native _ (Queued.acquire pid))
      intro ignored
      apply StateEnsures.bind (carrier_ambient (AmbientM.peekQueuedUnit .sendWorker pid))
      intro selected
      apply StateEnsures.bind (carrier_ambient
        (AmbientM.branch .queuedAlreadyQueued (peer.handshakePending && !selected)))
      intro pending
      split
      · exact StateEnsures.bind (Disposal.original (some pid) CompleteProduct.Safe
          (fun ledger h w before=>⟨debts,.accounted ledger locals h w before⟩)) (fun _=>carrier_pure ())
      · apply carrier_update pid (fun p=>{p with handshakePending:=true}) _ (fun _=>⟨rfl,rfl,rfl⟩)
        intro ignored
        exact StateEnsures.bind (carrier_ambient (AmbientM.recordQueued .sendWorker pid))
          (fun _=>queue_append pid)

theorem queued (pid : PeerId) (retry : Bool) :
    StateEnsures (Carrier debts locals) CompleteProduct.Safe
      (Effects.queuedWith effects peerRelease pid retry) (fun _=>Carrier debts locals) := by
  unfold Effects.queuedWith
  apply StateEnsures.bind (carrier_ambient (AmbientM.branch .queuedNotRetry !retry))
  intro resetting
  dsimp only
  split
  · have update := carrier_native (debts:=debts) (locals:=locals) _ (Queued.update pid
      (fun p=>{p with timerHandshakeAttempts:=0}) (fun _=>⟨rfl,rfl,rfl⟩))
    simpa only [TimerQueue.afterReset,Queued.lift_bind,bind_assoc,CausalJournal.effects,CausalEffects.ops,TimerEffects.observed] using
      StateEnsures.bind update (fun _=>queue_after_reset pid)
  · exact queue_after_reset pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
