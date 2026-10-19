import Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournalOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Exact history projection transfers socket byte readiness to the final
causal journal without discarding any event before a stopped execution. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
open Leanux Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [← history]
  exact Scheduler.initialized trace placeholders

end Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
