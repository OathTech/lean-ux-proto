import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointCanonical

/-! Both retry modes follow the native borrow/install/repayment branches.
The queue write and its actual receipt are separate source points. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open HandshakeSecurity.StagedDisposal

noncomputable def afterResetShape (pid : PeerId) : Shape (liftWGObserver (TimerQueue.afterReset pid)) := by
  unfold TimerQueue.afterReset
  apply stateBindShape _ _ (.leaf (.native (.base (.basic (.peer pid)))))
  intro peer
  apply stateBindShape _ _ (.native (.expired .queuedNotExpired peer.lastSentHandshake REKEY_TIMEOUT (!·)))
  intro recent
  split
  · exact .pure ()
  · apply stateBindShape _ _ (.leaf (.native (.base (.basic (.branch .queuedDead peer.isDead)))))
    intro dead
    split
    · exact .pure ()
    · apply stateBindShape _ _ (.native (.acquire pid))
      intro ignored
      apply stateBindShape _ _ (.leaf (.native (.base (.ambient (AmbientM.peekQueuedUnit .sendWorker pid)))))
      intro selected
      apply stateBindShape _ _ (.leaf (.native (.base (.basic (.branch .queuedAlreadyQueued (peer.handshakePending && !selected))))))
      intro pending
      split
      · exact stateBindShape _ _ (.child (.release (some pid))) (fun _ => .pure ())
      · apply updateThenShape pid (fun p => {p with handshakePending := true}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
        intro ignored
        exact stateBindShape _ _ (.leaf (.native (.base (.ambient (AmbientM.recordQueued .sendWorker pid)))))
          (fun _ => appendShape pid)

noncomputable def queuedShape (pid : PeerId) (retry : Bool) :
    Shape (liftWGObserver (Effects.queuedWith effects peerRelease pid retry)) := by
  apply Shape.marked (.queued pid retry)
  unfold Effects.queuedWith
  apply stateBindShape _ _ (.leaf (.native (.base (.basic (.branch .queuedNotRetry !retry)))))
  intro resetting
  dsimp only
  split
  · have update : Shape (liftWGObserver (liftWGPrefix (do
        setPeer pid {(← getPeer pid) with timerHandshakeAttempts := 0}))) :=
      .leaf (.native (.base (.update pid (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => ⟨rfl,rfl,rfl⟩))))
    simpa only [TimerQueue.afterReset,bind_assoc,CausalJournal.effects,CausalEffects.ops,TimerEffects.observed,
      liftWGObserver_bind,Queued.lift_bind] using
      stateBindShape _ _ update (fun _ => afterResetShape pid)
  · exact afterResetShape pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
