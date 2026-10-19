import Leanux.Proofs.WG.Progress.TimerCallbackSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal suffix effects for every original timer callback and
strict record decrease for its actual environment section wrapper. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem timerCallback_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (timerCallback_retains records pid timer g)
    a (value,after) b (pre ▸ tail_self records) run

theorem timerSection_record_decrease (records : List HiddenRecord)
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Product.Ensures (Env.runTimerSection worker (liftWG (timerCallback pid timer)))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (timerSection_strict records worker pid timer)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
