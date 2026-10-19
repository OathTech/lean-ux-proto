import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalFrames

/-! Local physical coverage and its immutable history projection. Recorded
keeps exact allocation occurrences on stopped prefixes; it deliberately does
not assert a physical World exists at a PrefixT error endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- The source-local name shares the parent's physical carrier exactly. -/
abbrev Physical := TransmitSecurity.Staged.Obligations.Physical

/-- Every tracked fixed ticket names an earlier exact native allocation;
this history fact is weaker than continued physical ownership. -/
def Recorded (history : List CausalJournal.Event) (ledger : Ledger)
    (debts : List CleanupDebt) : Prop :=
  ∀ ticket position ordinal, Tracked ledger debts ticket position ordinal →
    ∃ generation id value, Origin history position ordinal generation id value

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
