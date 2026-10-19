import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Staged plaintext provenance survives the exact final causal projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchPayload
open Leanux Leanux.Proofs.Logged AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [← history]
  exact initialized trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.BatchPayload
