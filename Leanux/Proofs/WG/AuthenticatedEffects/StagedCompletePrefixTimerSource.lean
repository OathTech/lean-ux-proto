import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSingle
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerSource

/-! Timer receipts preserve paired accounting because their actual events
carry neither a staged birth nor a terminal demand. Every native guard and
arm retains the same ledger; queued repayment is handled separately. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Timer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    Passive.Checked debts locals Safe (effects.arm pid timer delay clock) := by
  intro w a h before
  exact receipt Safe accountSafe _
    (fun run => .armed ⟨CausalScope.current scope? h,pid,timer,delay,clock,run⟩)
    (Passive.native Safe accountSafe _ (TimerFrames.arm pid timer delay clock))
    (fun _ => rfl) (fun _ _ => rfl) w a h before

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Passive.Checked debts locals Safe (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ ((callerJiffies_sameWGWorld site).factor StagedEntry.view))
  intro clock
  apply bind_checked Safe (Passive.native Safe accountSafe _ (TimerFrames.guard pid))
  intro ready
  split
  · exact bind_checked Safe (arm Safe accountSafe pid timer delay clock) (fun _ => pure_checked Safe accountSafe true)
  · exact pure_checked Safe accountSafe false

theorem derived (pid : PeerId) :
    Passive.Checked debts locals Safe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact bind_checked Safe (modify_timer Safe accountSafe _ _ _ _) (fun _ => pure_checked Safe accountSafe ())

theorem traversal (pid : PeerId) :
    Passive.Checked debts locals Safe (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
  intro p
  apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branchCmp .traversalKeepalive
    (p.persistentKeepaliveInterval != 0) p.persistentKeepaliveInterval 0))
  intro ready
  split
  · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    exact bind_checked Safe (modify_timer Safe accountSafe _ _ _ _) (fun _ => pure_checked Safe accountSafe ())
  · exact pure_checked Safe accountSafe ()

theorem initiated (pid : PeerId) :
    Passive.Checked debts locals Safe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ ((callerJiffies_sameWGWorld _).factor StagedEntry.view))
  intro clock
  apply bind_checked Safe (Passive.native Safe accountSafe _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor StagedEntry.view))
  intro jitter
  apply bind_checked Safe (Passive.native Safe accountSafe _ (TimerFrames.guard pid))
  intro alive
  split
  · exact arm Safe accountSafe _ _ _ _
  · exact pure_checked Safe accountSafe ()

theorem append (pid : PeerId) : Passive.Checked debts locals Safe (effects.append pid) := by
  apply Staging.single (CompleteTimer.append Safe accountSafe pid)
  · intro h w a before
    obtain ⟨ledger,accounted⟩ := before
    exact accountSafe ledger h w accounted
  · intro w a h before
    obtain ⟨ledger,accounted⟩ := before
    obtain ⟨performed,_,_⟩ := Queued.append_total accounted.entry pid a
    exact Or.inr ⟨_,congrArg Prod.snd performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Timer
