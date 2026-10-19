import Leanux.Proofs.WG.Progress.StagingSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-return record suffixes for actual queueing and staging. These are partial-correctness contracts, not callback termination or scheduler completion claims. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing
theorem queued_record_suffix (records : List HiddenRecord) (worker : Worker) (pid : PeerId) :
    Campaign2.Ensures (recordQueued worker pid : WG.M Unit)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (native_recordQueued records worker pid g) a (value,after) b kept run

theorem peek_queued_record_suffix (records : List HiddenRecord) (worker : Worker) (pid : PeerId) :
    Campaign2.Ensures (peekQueuedUnit worker pid : WG.M Bool)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (native_peekQueued records worker pid g) a (value,after) b kept run

theorem device_work_record_suffix (records : List HiddenRecord) (worker : Worker) :
    Campaign2.Ensures (queueDeviceWork worker : WG.M Unit)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (native_queueDeviceWork records worker g) a (value,after) b kept run

theorem queued_initiation_record_suffix (records : List HiddenRecord) (pid : PeerId) (retry : Bool) :
    Campaign2.Ensures (sendQueuedHandshakeInitiation pid retry)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (queuedInitiation_retains records pid retry g) a (value,after) b kept run

theorem staged_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendStagedPackets pid)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (staged_retains records pid g) a (value,after) b kept run

theorem keepalive_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendKeepalive pid)
      (fun s=>s.ambient.hidden = some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  have kept : Tail records a.hidden := by
    change a.hidden = some records at pre
    rw [pre]
    exact tail_self records
  exact (hoare_iff_run _ _ _).mp (keepalive_retains records pid g) a (value,after) b kept run

end Leanux.Proofs.WG.Progress.RecordSuffix
