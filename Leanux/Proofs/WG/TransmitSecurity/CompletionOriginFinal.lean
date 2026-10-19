import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! The final causal journal retains allocation ancestry at the actual
completion-entry position, including prefixes before a later Stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [←history]
  exact initialized trace placeholders

theorem final_completion (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (pid : PeerId) (items : List SkbId)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.old (.disposition (.completion pid items)) :: post) :
    CompletionOrigin.Certificate (pre.filterMap CausalJournal.old?) items := by
  have old := congrArg (List.filterMap CausalJournal.old?) position
  simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?] at old
  exact final_initialized trace placeholders (pre.filterMap CausalJournal.old?)
    (.disposition (.completion pid items)) (post.filterMap CausalJournal.old?) old

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
