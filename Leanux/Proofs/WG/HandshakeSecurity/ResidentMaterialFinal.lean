import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Exact source-event projection carries initialized packet/key material
certificates into the final causal journal, including stopped prefixes. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [←history]
  exact initialized trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
