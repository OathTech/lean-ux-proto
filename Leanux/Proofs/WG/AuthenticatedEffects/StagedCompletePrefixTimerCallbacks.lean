import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTimerQueue
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryZeroTimer

/-! Actual new-handshake and retransmit timer callbacks compose native
maintenance with counted purge and queued-initiation source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.TimerCallbacks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
open HandshakeSecurity.StagedDisposal
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List CausalJournal.Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem new_handshake (pid : PeerId) : Checked debts locals Safe
    (Driver.timerObserved CausalJournal.hooks pid .newHandshake) := by
  change Checked debts locals Safe (Effects.newHandshakeWith effects peerRelease pid)
  unfold Effects.newHandshakeWith
  exact bind_checked Safe (Passive.native Safe accountSafe _ (EndpointFrames.clear pid))
    (fun _ => TimerQueue.queued Safe accountSafe pid false)

/-- Every actual retransmit branch retains paired accounting: give-up uses
its counted purge receipt, while retry uses its actual queued-work source. -/
theorem retransmit (pid : PeerId) : Checked debts locals Safe
    (Driver.timerObserved CausalJournal.hooks pid .retransmitHandshake) := by
  change Checked debts locals Safe (Effects.retransmitWith effects peerRelease stagedPurge pid)
  unfold Effects.retransmitWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branchCmp .retransmitGiveUp
    (peer.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) peer.timerHandshakeAttempts MAX_TIMER_HANDSHAKES))
  intro exhausted
  split
  · apply bind_checked Safe (Passive.native Safe accountSafe _ (TimerFrames.delete pid .sendKeepalive))
    intro ignored
    apply bind_checked Safe (Disposal.purge pid Safe accountSafe)
    intro ignored
    apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
    intro peer
    apply bind_checked Safe (Passive.ambient Safe accountSafe
      (AmbientM.branch .retransmitZeroKeyNotPending !(peer.timerPending .zeroKeyMaterial)))
    intro pending
    split
    · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
      exact bind_checked Safe (Timer.modify_timer Safe accountSafe
        .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)
        (fun _ => pure_checked Safe accountSafe ())
    · exact pure_checked Safe accountSafe ()
  · apply Passive.update_bind Safe accountSafe pid
      (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    apply bind_checked Safe (Passive.native Safe accountSafe _ (EndpointFrames.clear pid))
    intro ignored
    exact TimerQueue.queued Safe accountSafe pid true

theorem send_keepalive (pid : PeerId)
    (keepalive : Checked debts locals Safe (Driver.keepaliveObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid .sendKeepalive) := by
  change Checked debts locals Safe (TimerEffects.expiredKeepaliveWith effects
    (Driver.keepaliveObserved CausalJournal.hooks) pid)
  unfold TimerEffects.expiredKeepaliveWith
  apply bind_checked Safe keepalive
  intro ignored
  apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (Passive.ambient Safe accountSafe
    (AmbientM.branch .keepaliveNeedAnother peer.timerNeedAnotherKeepalive))
  intro needed
  split
  · apply Passive.update_bind Safe accountSafe pid
      (fun p => {p with timerNeedAnotherKeepalive := false}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    exact bind_checked Safe (Timer.modify_timer Safe accountSafe
      .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)
      (fun _ => pure_checked Safe accountSafe ())
  · exact pure_checked Safe accountSafe ()

theorem persistent (pid : PeerId)
    (keepalive : Checked debts locals Safe (Driver.keepaliveObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid .persistentKeepalive) := by
  change Checked debts locals Safe (TimerEffects.persistentWith effects
    (Driver.keepaliveObserved CausalJournal.hooks) pid)
  unfold TimerEffects.persistentWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (Passive.ambient Safe accountSafe
    (AmbientM.branch .persistentKeepaliveInterval (peer.persistentKeepaliveInterval != 0)))
  intro enabled
  split
  · exact keepalive
  · exact pure_checked Safe accountSafe ()

/-- All five actual timer callbacks retain paired accounting. The actual
keepalive source is a visible input contract until its admission/staging
composition is supplied; no fixture cause or terminal quietness is assumed. -/
theorem callback (pid : PeerId) (timer : PeerTimer)
    (keepalive : Checked debts locals Safe (Driver.keepaliveObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.timerObserved CausalJournal.hooks pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit Safe accountSafe pid
  | sendKeepalive => exact send_keepalive Safe accountSafe pid keepalive
  | newHandshake => exact new_handshake Safe accountSafe pid
  | zeroKeyMaterial => exact Passive.native Safe accountSafe _ (ZeroTimer.frame pid)
  | persistentKeepalive => exact persistent Safe accountSafe pid keepalive

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.TimerCallbacks
