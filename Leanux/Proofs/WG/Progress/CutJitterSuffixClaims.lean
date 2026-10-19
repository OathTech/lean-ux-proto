import Leanux.Proofs.WG.Progress.CutJitterSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.TimerDiscipline
/-- Exact cut-site execution leaves a suffix on normal return. Allocation
refusal and malformed streams retain their existing errors. -/
theorem cutSites_record_suffix (sites : List HiddenSite) (records : List HiddenRecord) :
    Campaign2.Ensures (skipCutSites sites : WG.M (List Nat))
      (fun s => s.ambient.hidden = some records)
      (fun _ s => Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden = some records at pre
  exact (hoare_iff_run _ _ _).mp (native_skipCutSites records sites g)
    a (value,after) b (pre ▸ tail_self records) run

/-- Either original timer jitter site consumes a strict record suffix whenever
it returns normally, including rejected draws and skipped passive records. -/
theorem jitter_record_decrease (site : JitterSite) (records : List HiddenRecord) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site.hiddenSite)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => StrictTail records s.ambient.hidden) := by
  intro g a value after b pre run
  exact (hoare_iff_run _ _ _).mp (jitter_strict site records g) a (value,after) b pre run
end Leanux.Proofs.WG.Progress.RecordSuffix
