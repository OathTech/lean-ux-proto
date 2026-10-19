import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerQueue

/-! Both native queued-initiation modes retain entry and terminal converse
on the same successor ledger. The actual repayment uses its counted paired
source contract even though this helper creates no new staged packet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTimerQueue
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier CompletePassive HandshakeSecurity.StagedDisposal
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List CausalJournal.Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem after_reset (pid : PeerId) :
    CompletePassive.Checked debts locals Safe (TimerQueue.afterReset pid) := by
  unfold TimerQueue.afterReset
  apply bind_checked Safe (CompletePassive.native Safe accountSafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (CompletePassive.native Safe accountSafe _
    ((branchExpired_sameWGWorld .queuedNotExpired peer.lastSentHandshake REKEY_TIMEOUT (!·)).factor StagedEntry.view))
  intro recent
  split
  · exact pure_checked Safe accountSafe ()
  · apply bind_checked Safe (CompletePassive.ambient Safe accountSafe (AmbientM.branch .queuedDead peer.isDead))
    intro dead
    split
    · exact pure_checked Safe accountSafe ()
    · apply bind_checked Safe (CompletePassive.native Safe accountSafe _ (Queued.acquire pid))
      intro ignored
      apply bind_checked Safe (CompletePassive.ambient Safe accountSafe (AmbientM.peekQueuedUnit .sendWorker pid))
      intro selected
      apply bind_checked Safe (CompletePassive.ambient Safe accountSafe
        (AmbientM.branch .queuedAlreadyQueued (peer.handshakePending && !selected)))
      intro pending
      split
      · exact bind_checked Safe (CompleteSource.original (some pid) Safe accountSafe)
          (fun _ => pure_checked Safe accountSafe ())
      · apply update_bind Safe accountSafe pid (fun p => {p with handshakePending := true})
          _ (fun _ => ⟨rfl,rfl,rfl⟩)
        intro ignored
        apply bind_checked Safe (CompletePassive.ambient Safe accountSafe (AmbientM.recordQueued .sendWorker pid))
        intro ignored
        exact CompleteTimer.append Safe accountSafe pid

theorem queued (pid : PeerId) (retry : Bool) : CompletePassive.Checked debts locals Safe
    (Effects.queuedWith effects peerRelease pid retry) := by
  unfold Effects.queuedWith
  apply bind_checked Safe (CompletePassive.ambient Safe accountSafe (AmbientM.branch .queuedNotRetry !retry))
  intro resetting
  dsimp only
  split
  · have update := CompletePassive.native Safe accountSafe _ (Queued.update pid
      (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => ⟨rfl,rfl,rfl⟩))
    simpa only [TimerQueue.afterReset,Queued.lift_bind,bind_assoc,CausalJournal.effects,CausalEffects.ops,TimerEffects.observed] using
      bind_checked Safe update (fun _ => after_reset Safe accountSafe pid)
  · exact after_reset Safe accountSafe pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTimerQueue
