import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdmissionChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionDisposal

/-! The original queue-admission prefix ending at its peer-queue write.
The false result is the actual full-queue refusal. The true result precedes
all later CPU, ring and scheduling choices. No new journal event is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation

def queueInstallPrefix (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Bool := do
  let some peer ← QueueHandoff.focused (QueueHandoff.before pid items) | return false
  QueueHandoff.focused (QueueHandoff.install pid peer items)
  return true

def queueInstallTail (items : List SkbId) (installed : Bool) : PrefixM CausalJournal.Event Int := do
  let ret ← if installed then QueueHandoff.focused (QueueHandoff.after items) else pure (-WG.ENOSPC)
  QueueHandoff.focused (QueueHandoff.offered items ret)

/-- Queue publication occurs at the original install, before the original
ring tail. This equality preserves actual stopped histories and event positions. -/
theorem queue_install_factor (pid : PeerId) (items : List SkbId) :
    Admission.actualOps.enqueue pid items =
      (queueInstallPrefix pid items >>= queueInstallTail items) := by
  rw [QueueHandoff.actual_enqueue]
  simp only [QueueHandoff.enqueueFocused,queueInstallPrefix,bind_assoc]
  congr 1
  funext candidate
  cases candidate <;> simp only [pure_bind,bind_assoc,queueInstallTail,Bool.false_eq_true,↓reduceIte]

theorem queue_installed_tail (items : List SkbId) :
    queueInstallTail items true = (do
      let ret ← QueueHandoff.focused (QueueHandoff.after items)
      QueueHandoff.focused (QueueHandoff.offered items ret)) := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
