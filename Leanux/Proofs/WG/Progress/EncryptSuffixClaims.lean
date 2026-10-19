import Leanux.Proofs.WG.Progress.EncryptSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result suffix facts for actual encryption and publication.
No successful return, packet delivery or whole-worker termination is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Queues

theorem encryptPacket_record_suffix (records : List HiddenRecord) (key : KeypairId) (pkt : DataPacket) :
    Campaign2.Product.Ensures (encryptPacket Env.checksumHelp key pkt)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (encryptPacket_retains records key pkt)
    w value after (pre ▸ tail_self records) run

theorem encryptPublish_record_suffix (records : List HiddenRecord) (item : List SkbId) (state : PacketState) :
    Campaign2.Ensures (enqueuePerPeerTx item state)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (encryptPublish_retains records item state g)
    a (value,after) b (pre ▸ tail_self records) run

theorem encryptTail_record_suffix (records : List HiddenRecord) (item : Option (List SkbId)) :
    Campaign2.Product.Ensures (RxWorkers.encryptTailSource item)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (encryptTail_retains records item)
    w value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
