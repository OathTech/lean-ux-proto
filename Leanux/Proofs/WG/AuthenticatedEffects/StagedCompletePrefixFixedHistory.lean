import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixQuiet

/-! A fixed ledger's receipt scan restricts to earlier positions. This rule
also requires an old Accounted entry and a birth-free suffix before it yields
prefix safety. It cannot roll back an arbitrary final ledger or identify an
existential snapshot with a native execution cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.FixedHistory
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal StagedTerminalComplete

theorem complete_prefix (complete : Complete (history++suffix) ledger) (n : Nat) :
    Complete (history++suffix.take n) ledger := by
  have split : Scan 0 ((history++suffix.take n)++suffix.drop n) ledger := by
    simpa only [Complete,List.append_assoc,List.take_append_drop] using complete
  exact (scan_append.mp split).1

/-- Every new logical prefix uses the original ledger and snapshot, with
fresh complete-scan evidence restricted to that precise position. Native
interval correspondence is a separate obligation. -/
theorem cuts (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w→Safe h)
    (before : CompleteCarrier.Accounted history ledger debts locals w)
    (births : ∀ event∈suffix, birthPackets event=[])
    (complete : Complete (history++suffix) ledger) : Cuts Safe history suffix := by
  intro n _
  apply accountSafe ledger _ w
  exact ⟨Queued.Inv.history before.entry (suffix.take n)
    (fun event member=>births event (List.mem_of_mem_take member)),complete_prefix complete n⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.FixedHistory
