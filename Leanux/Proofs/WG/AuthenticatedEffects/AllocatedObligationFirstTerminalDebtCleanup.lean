import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSupport
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalCleanup
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationNativeCleanupFrames

/-! Ordinary cleanup consumes the exact resident terminal debt at its actual
source callback. Mixed uniqueness derives the no-pending-alias fact; neither a
terminal-drop receipt nor an extra incoming Unused premise is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- The actual completion free discharges the identified cleanup debt while
keeping its first terminal result. Every remaining cell is still covered by
a pending ticket or terminal debt, with mixed uniqueness preserved. -/
theorem cleanup_debt (skb : SkbId) (w v : World)
    (history suffix : List CausalJournal.Event)
    (performed : runPrefix (cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (support : Support births history ledger debts w.wg)
    (debt : CleanupDebt) (member : debt ∈ debts)
    (origin : Origin history debt.position debt.ordinal generation skb value)
    (epoch : Packets.epoch w.wg = some generation) :
    let afterDebts := forgetFreedCell history generation skb debts
    Staged.Obligations.Step ledger ledger ∧
      Support births (history ++ suffix) ledger afterDebts v.wg ∧
      (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧ debt ∉ afterDebts ∧
      PacketMaterial.view v.wg skb = none := by
  dsimp only
  have native := (cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨resident,mixed,covered,cleanup,terminal,removed⟩ := cleanup_native_mixed native
    support.valid support.mixed support.resident support.covered support.cleanup debt member origin epoch
  have after : Support births history ledger (forgetFreedCell history generation skb debts) v.wg :=
    ⟨⟨resident,covered,cleanup,mixed⟩,support.valid⟩
  exact ⟨.refl ledger,after.append suffix,terminal,removed,
    (native_free_views skb w v native).2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
