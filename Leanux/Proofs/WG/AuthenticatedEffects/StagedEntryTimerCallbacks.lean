import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerQueue
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPurgeSource

/-! Actual new-handshake and retransmit timer callbacks compose native
maintenance with counted purge and queued-initiation source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerCallbacks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open SourcePassive HandshakeSecurity.StagedDisposal
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List CausalJournal.Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem new_handshake (pid : PeerId) : Checked debts locals Safe
    (Driver.timerObserved CausalJournal.hooks pid .newHandshake) := by
  change Checked debts locals Safe (Effects.newHandshakeWith effects peerRelease pid)
  unfold Effects.newHandshakeWith
  exact bind_checked Safe (SourcePassive.native Safe entrySafe _ (EndpointFrames.clear pid))
    (fun _ => TimerQueue.queued Safe entrySafe pid false)

/-- Every actual retransmit branch retains entry accounting: give-up uses
its counted purge receipt, while retry uses its actual queued-work source. -/
theorem retransmit (pid : PeerId) : Checked debts locals Safe
    (Driver.timerObserved CausalJournal.hooks pid .retransmitHandshake) := by
  change Checked debts locals Safe (Effects.retransmitWith effects peerRelease stagedPurge pid)
  unfold Effects.retransmitWith
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (SourcePassive.ambient Safe entrySafe (AmbientM.branchCmp .retransmitGiveUp
    (peer.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) peer.timerHandshakeAttempts MAX_TIMER_HANDSHAKES))
  intro exhausted
  split
  · apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (TimerFrames.delete pid .sendKeepalive))
    intro ignored
    apply bind_checked Safe (Purge.checked pid Safe entrySafe)
    intro ignored
    apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.read pid))
    intro peer
    apply bind_checked Safe (SourcePassive.ambient Safe entrySafe
      (AmbientM.branch .retransmitZeroKeyNotPending !(peer.timerPending .zeroKeyMaterial)))
    intro pending
    split
    · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
      exact bind_checked Safe (fixed Safe entrySafe (fun _ => TimerObserved.modify_timer
        .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS))
        (fun _ => pure_checked Safe entrySafe ())
    · exact pure_checked Safe entrySafe ()
  · apply TimerQueue.update_bind Safe entrySafe pid
      (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (EndpointFrames.clear pid))
    intro ignored
    exact TimerQueue.queued Safe entrySafe pid true

private theorem keepalive (pid : PeerId)
    (staging : Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.keepaliveObserved CausalJournal.hooks pid) := by
  unfold Driver.keepaliveObserved
  apply bind_checked Safe (Source.keepalive pid Safe entrySafe)
  intro ready
  cases ready
  · exact pure_checked Safe entrySafe ()
  · exact staging

theorem send_keepalive (pid : PeerId)
    (staging : Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid .sendKeepalive) := by
  change Checked debts locals Safe (TimerEffects.expiredKeepaliveWith effects
    (Driver.keepaliveObserved CausalJournal.hooks) pid)
  unfold TimerEffects.expiredKeepaliveWith
  apply bind_checked Safe (keepalive Safe entrySafe pid staging)
  intro ignored
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (SourcePassive.ambient Safe entrySafe
    (AmbientM.branch .keepaliveNeedAnother peer.timerNeedAnotherKeepalive))
  intro needed
  split
  · apply TimerQueue.update_bind Safe entrySafe pid
      (fun p => {p with timerNeedAnotherKeepalive := false}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    exact bind_checked Safe (fixed Safe entrySafe (fun _ => TimerObserved.modify_timer
      .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS))
      (fun _ => pure_checked Safe entrySafe ())
  · exact pure_checked Safe entrySafe ()

theorem persistent (pid : PeerId)
    (staging : Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid .persistentKeepalive) := by
  change Checked debts locals Safe (TimerEffects.persistentWith effects
    (Driver.keepaliveObserved CausalJournal.hooks) pid)
  unfold TimerEffects.persistentWith
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (SourcePassive.ambient Safe entrySafe
    (AmbientM.branch .persistentKeepaliveInterval (peer.persistentKeepaliveInterval != 0)))
  intro enabled
  split
  · exact keepalive Safe entrySafe pid staging
  · exact pure_checked Safe entrySafe ()

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerCallbacks
