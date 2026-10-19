import Leanux.Proofs.WG.Progress.TransmitRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result record contracts for original transmit operations.
Stops have no final-state claim. These results do not establish termination,
normal return, recordless-mode progress, or completion-guard success. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem createDataDone_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (item : List SkbId) :
    Campaign2.Ensures (createDataDone pid item)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (createDataDone_retains records pid item g)
    a (value,after) b (pre ▸ tail_self records) run

theorem txStep_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (txStep pid)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (txStep_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem cryptAhead_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Product.Ensures (Env.cryptAhead pid)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (cryptAhead_retains records pid)
    w value after (pre ▸ tail_self records) run

theorem txActivation_record_effect (a : Activation) (worker : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.iter a)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        (result=.yielded→StrictTail records s.ambient.hidden)) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (txActivation_iteration a worker records)
    w value after pre run

theorem txActivation_record_strict (a : Activation) (worker : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (txActivation_strict a worker records)
    w value after pre run

end Leanux.Proofs.WG.Progress.RecordSuffix
