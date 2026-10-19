import Leanux.Proofs.WG.Progress.DecryptSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-return record-suffix contracts. Errors retain their original semantics; no successful-return or activation-fuel adequacy assertion is made here. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem hiddenAlloc_record_suffix (records : List HiddenRecord) (site : AllocSite) :
    Campaign2.Ensures (hiddenAlloc site : WG.M Bool)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  exact (hoare_iff_run _ _ _).mp (native_alloc records site g) a (value,after) b
    (by change a.hidden = some records at pre; rw [pre]; exact tail_self records) run

theorem decryptPacket_record_suffix (records : List HiddenRecord) (pkt : RxPacket) :
    Campaign2.Ensures (decryptPacket pkt)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  exact (hoare_iff_run _ _ _).mp (decryptPacket_retains records pkt g) a (value,after) b
    (by change a.hidden = some records at pre; rw [pre]; exact tail_self records) run

theorem publish_record_suffix (records : List HiddenRecord) (id : SkbId) (state : PacketState) :
    Campaign2.Ensures (Queues.RxWorkers.publishSource id state)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  exact (hoare_iff_run _ _ _).mp (publish_retains records id state g) a (value,after) b
    (by change a.hidden = some records at pre; rw [pre]; exact tail_self records) run

theorem prepare_record_suffix (records : List HiddenRecord) :
    Campaign2.Ensures Queues.RxWorkers.prepareSource
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  exact (hoare_iff_run _ _ _).mp (prepare_retains records g) a (value,after) b
    (by change a.hidden = some records at pre; rw [pre]; exact tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
