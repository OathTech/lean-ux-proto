import Leanux.Proofs.WG.Progress.RecordSuffixModel

/-! A retained record suffix is strict when its contents changed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux

theorem tail_strict_of_changed {records : List HiddenRecord}
    {remaining : Option (List HiddenRecord)}
    (tail : Tail records remaining) (changed : remaining ≠ some records) :
    StrictTail records remaining := by
  obtain ⟨rest,stored,suffix⟩ := tail
  refine ⟨rest,stored,suffix,?_⟩
  by_cases shorter : rest.length < records.length
  · exact shorter
  · have same : rest=records := suffix.eq_of_length_le (by omega)
    exact False.elim (changed (stored.trans (congrArg some same)))


end Leanux.Proofs.WG.Progress.RecordSuffix
