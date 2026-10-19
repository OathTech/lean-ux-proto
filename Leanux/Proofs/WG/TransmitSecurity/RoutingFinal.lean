import Leanux.Proofs.WG.TransmitSecurity.RoutingReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Actual routing-admission receipts survive the exact final causal projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal.RoutingHistory
open Leanux Leanux.Proofs.Logged AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [← history]
  exact initialized trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.Journal.RoutingHistory
