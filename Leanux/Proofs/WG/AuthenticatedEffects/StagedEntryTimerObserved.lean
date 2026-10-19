import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive

/-! Actual timer-effect callers preserve full indexed local accounting.
Every Stop retains a full Entry witness at its reached history; the arm and
modifier source modules additionally expose their connected native cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Passive
variable {ledger : Ledger} {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Checked ledger debts locals (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  apply bind_checked (Passive.native _ ((callerJiffies_sameWGWorld site).factor StagedEntry.view))
  intro clock
  apply bind_checked (Passive.native _ (TimerFrames.guard pid))
  intro ready
  split
  · exact bind_checked (arm pid timer delay clock) (fun _ => pure_checked true)
  · exact pure_checked false

theorem derived (pid : PeerId) : Checked ledger debts locals (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact bind_checked (modify_timer _ _ _ _) (fun _ => pure_checked ())

theorem traversal (pid : PeerId) : Checked ledger debts locals (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  apply bind_checked (Passive.native _ (Queued.read pid))
  intro p
  apply bind_checked (ambient (AmbientM.branchCmp .traversalKeepalive
    (p.persistentKeepaliveInterval != 0) p.persistentKeepaliveInterval 0))
  intro ready
  split
  · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    exact bind_checked (modify_timer _ _ _ _) (fun _ => pure_checked ())
  · exact pure_checked ()

theorem sent (pid : PeerId) : Checked ledger debts locals (TimerEffects.dataSentWith effects pid) := by
  unfold TimerEffects.dataSentWith
  apply bind_checked (Passive.native _ (Queued.read pid))
  intro p
  apply bind_checked (ambient (AmbientM.branch .timersDataSentNotPending !(p.timerPending .newHandshake)))
  intro ready
  split
  · apply bind_checked (Passive.native _ ((callerJiffies_sameWGWorld _).factor StagedEntry.view))
    intro clock
    apply bind_checked (Passive.native _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor StagedEntry.view))
    intro jitter
    apply bind_checked (Passive.native _ (TimerFrames.guard pid))
    intro alive
    split
    · exact arm _ _ _ _
    · exact pure_checked ()
  · exact pure_checked ()

theorem initiated (pid : PeerId) : Checked ledger debts locals (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  apply bind_checked (Passive.native _ ((callerJiffies_sameWGWorld _).factor StagedEntry.view))
  intro clock
  apply bind_checked (Passive.native _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor StagedEntry.view))
  intro jitter
  apply bind_checked (Passive.native _ (TimerFrames.guard pid))
  intro alive
  split
  · exact arm _ _ _ _
  · exact pure_checked ()

theorem received (pid : PeerId) : Checked ledger debts locals (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  apply bind_checked (Passive.native _ (TimerFrames.store getDev_sameWGStore))
  intro d
  apply bind_checked (ambient (AmbientM.branch .timersDataReceivedRunning d.running))
  intro running
  split
  · apply bind_checked (Passive.native _ (Queued.read pid))
    intro p
    apply bind_checked (ambient (AmbientM.branch .timersDataReceivedNotPending !(p.timerPending .sendKeepalive)))
    intro ready
    split
    · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
      exact bind_checked (modify_timer _ _ _ _) (fun _ => pure_checked ())
    · exact update pid (fun p => {p with timerNeedAnotherKeepalive := true}) (fun _ => ⟨rfl,rfl,rfl⟩)
  · exact pure_checked ()

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerObserved
