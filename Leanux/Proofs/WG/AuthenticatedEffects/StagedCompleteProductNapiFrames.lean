import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls
import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryFrames
import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit

/-! Exact erasure and native allocation frames for paired NAPI composition.
The erased endpoint supplies no event-history fact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership

theorem native_allocated_product {observer : PrefixM LifetimeEvent α} {native : Leanux.M α}
    (erases : ErasesPrefix observer native)
    (keeps : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe observer) :
    Preserves (fun w : World => Allocated w.wg) native := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v before run
  obtain ⟨history,account⟩ := before
  obtain ⟨suffix,extended,safe,post⟩ := keeps w history account
  have observed := (erases w history).trans run
  rw [observed] at post
  exact ⟨_,post⟩

theorem softirq_erases : ErasesPrefix (Driver.softirqObserved hooks) Env.napiSoftirq := by
  apply EncryptionHistory.projected_erases (Driver.softirq_projects hooks_projects)
  apply EncryptionHistory.projected_erases (Driver.softirq_projects Journal.hooks_projects)
  rw [Driver.nonce_softirqObserved_eq]
  exact Nonce.softirqObserved_erases

theorem inline_erases : ErasesPrefix (Driver.inlinePollObserved hooks) Env.pollScheduledInline := by
  apply EncryptionHistory.projected_erases (Driver.inline_projects hooks_projects)
  apply EncryptionHistory.projected_erases (Driver.inline_projects Journal.hooks_projects)
  rw [Driver.nonce_inlinePollObserved_eq]
  exact Nonce.inlinePollObserved_erases

theorem irq_exit_erases : ErasesPrefix (Driver.irqExitObserved hooks) Env.napiIrqExit := by
  apply EncryptionHistory.projected_erases (Driver.irqExit_projects hooks_projects)
  apply EncryptionHistory.projected_erases (Driver.irqExit_projects Journal.hooks_projects)
  rw [Driver.nonce_irqExitObserved_eq]
  exact Nonce.irqExitObserved_erases

theorem timer_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (Driver.timerObserved hooks pid timer) (timerCallback pid timer) := by
  apply NestedPeerRelease.projects_erases old? (Driver.timer_projects hooks_projects pid timer)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.timer_projects Journal.hooks_projects pid timer)
  rw [Driver.nonce_timerObserved_eq]
  exact Nonce.timerObserved_erases pid timer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
