import Leanux.Proofs.WG.TransmitSecurity.BatchJournalOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! The exact old-history projection transports initialized head/packet agreement to the
final causal journal of the same source driver, retaining stopped prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchJournal
open Leanux Leanux.Proofs.Logged
open AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [← history]
  exact Scheduler.initialized trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.BatchJournal
