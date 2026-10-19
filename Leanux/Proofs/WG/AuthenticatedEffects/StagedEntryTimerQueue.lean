import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFinish

/-! Both retry modes of the actual queued-initiation helper retain entry
accounting. Its repayment uses the original counted release contract rather
than a birth-only or unconditional native frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerQueue
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open SourcePassive HandshakeSecurity.StagedDisposal
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List CausalJournal.Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem update_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WGPrefix CausalJournal.Event α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ value, Checked debts locals Safe (next value)) :
    Checked debts locals Safe (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next) := by
  simpa only [bind_assoc] using bind_checked Safe
    (fixed Safe entrySafe (fun _ => Passive.update pid f same)) tail

theorem append (pid : PeerId) : Checked debts locals Safe (effects.append pid) := by
  apply fixed Safe entrySafe
  intro ledger w a h entry
  obtain ⟨performed,_,kept⟩ := Queued.append_total entry pid a
  change runPrefix ((effects.append pid).run w) a h = _ at performed
  rw [performed]
  exact ⟨[_],rfl,⟨_,kept⟩,kept⟩

def afterReset (pid : PeerId) : WGPrefix CausalJournal.Event Unit := do
  let peer ← effects.step (getPeer pid)
  if ← effects.step (branchExpired .queuedNotExpired peer.lastSentHandshake REKEY_TIMEOUT (!·)) then return
  if ← effects.step (branch .queuedDead peer.isDead) then return
  effects.step (peerGet pid)
  if ← effects.step (branch .queuedAlreadyQueued (peer.handshakePending && !(← effects.step (peekQueuedUnit .sendWorker pid)))) then
    peerRelease (some pid)
    return
  effects.step (setPeer pid {(← effects.step (getPeer pid)) with handshakePending := true})
  effects.step (recordQueued .sendWorker pid)
  effects.append pid

theorem after_reset (pid : PeerId) : Checked debts locals Safe (afterReset pid) := by
  unfold afterReset
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.read pid))
  intro peer
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _
    ((branchExpired_sameWGWorld .queuedNotExpired peer.lastSentHandshake REKEY_TIMEOUT (!·)).factor StagedEntry.view))
  intro recent
  split
  · exact pure_checked Safe entrySafe ()
  · apply bind_checked Safe (SourcePassive.ambient Safe entrySafe (AmbientM.branch .queuedDead peer.isDead))
    intro dead
    split
    · exact pure_checked Safe entrySafe ()
    · apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (Queued.acquire pid))
      intro ignored
      apply bind_checked Safe (SourcePassive.ambient Safe entrySafe (AmbientM.peekQueuedUnit .sendWorker pid))
      intro selected
      apply bind_checked Safe (SourcePassive.ambient Safe entrySafe
        (AmbientM.branch .queuedAlreadyQueued (peer.handshakePending && !selected)))
      intro pending
      split
      · exact bind_checked Safe (Source.release (some pid) Safe entrySafe)
          (fun _ => pure_checked Safe entrySafe ())
      · apply update_bind Safe entrySafe pid (fun p => {p with handshakePending := true})
          _ (fun _ => ⟨rfl,rfl,rfl⟩)
        intro ignored
        apply bind_checked Safe (SourcePassive.ambient Safe entrySafe (AmbientM.recordQueued .sendWorker pid))
        intro ignored
        exact append Safe entrySafe pid


theorem queued (pid : PeerId) (retry : Bool) : Checked debts locals Safe
    (Effects.queuedWith effects peerRelease pid retry) := by
  unfold Effects.queuedWith
  apply bind_checked Safe (SourcePassive.ambient Safe entrySafe (AmbientM.branch .queuedNotRetry !retry))
  intro resetting
  dsimp only
  split
  · have update := fixed Safe entrySafe (fun _ => Passive.update pid
      (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => ⟨rfl,rfl,rfl⟩))
    simpa only [afterReset,bind_assoc,CausalJournal.effects,CausalEffects.ops,TimerEffects.observed] using
      bind_checked Safe update (fun _ => after_reset Safe entrySafe pid)
  · exact after_reset Safe entrySafe pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerQueue
