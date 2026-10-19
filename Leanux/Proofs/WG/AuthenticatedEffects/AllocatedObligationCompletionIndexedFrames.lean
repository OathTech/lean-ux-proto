import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexed

/-! Passive completion actions preserve the explicit semantic entry indices.
History extension is restricted to actual suffixes that introduce no births. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

theorem Owned.append (before : Owned context phase history ledger debts w)
    (suffix : List CausalJournal.Event) (quiet : ∀ event ∈ suffix, birthPackets event = []) :
    Owned context phase (history ++ suffix) ledger debts w :=
  ⟨before.cursor.append suffix,before.entry.views suffix quiet rfl rfl rfl rfl rfl rfl,
    (births_quiet_suffix history suffix quiet).trans before.domain⟩

theorem Owned.same_view (before : Owned context phase history ledger debts w)
    (same : StagedEntry.view v.wg = StagedEntry.view w.wg) :
    Owned context phase history ledger debts v :=
  ⟨before.cursor,before.entry.same_view same,before.domain⟩

theorem focus_births (encode : E → CausalJournal.Event) (decode : CausalJournal.Event → Option E)
    (quiet : ∀ event, birthPackets (encode event) = []) (action : PrefixM E α)
    (w : World) (history : List CausalJournal.Event) :
    births (runPrefix (focusPrefix encode decode action) w history).2 = births history := by
  change births (history ++ List.map encode _) = births history
  apply births_quiet_suffix
  intro event member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact quiet original

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
