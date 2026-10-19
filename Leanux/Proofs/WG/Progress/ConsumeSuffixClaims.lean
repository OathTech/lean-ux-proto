import Leanux.Proofs.WG.Progress.ConsumeSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Normal-result suffix measures for actual receive completion. These claims imply neither that the operation returns nor that a worker or the driver completes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem consumeDataDone_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Campaign2.Ensures (consumeDataDone pid pkt ep)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (consumeDataDone_retains records pid pkt ep g)
    a (value,after) b (pre ▸ tail_self records) run

theorem consumeDataDone_product_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Campaign2.Product.Ensures (liftWG (consumeDataDone pid pkt ep))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp
    (native_product records _ (consumeDataDone_retains records pid pkt ep))
    w value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
