import Leanux.Proofs.WG.Progress.DeliverySuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-return suffix preservation, with all original callbacks
discharged. No strict decrease, successful return or termination is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem deliverSent_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.deliverSent
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (deliverSent_retains records)
    w value after (pre ▸ tail_self records) run

theorem runCryptWorkers_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runCryptWorkers
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (runCryptWorkers_retains records)
    w value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
