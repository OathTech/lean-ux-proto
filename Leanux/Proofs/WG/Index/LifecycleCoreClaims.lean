import Leanux.Proofs.WG.Index.LifecycleDeviceSource
import Leanux.Proofs.WG.Index.ConfigurationCoreBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem lifecycle_create_index (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) :
    Campaign2.Ensures wgCreate (View.ConfigurationInput cs loans)
      (fun _ => View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (LifecycleIndex.create_entry cs loans)
      w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem lifecycle_open_index (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) :
    Campaign2.Ensures wgOpen (View.ConfigurationInput cs loans)
      (fun _ => View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (LifecycleIndex.open_entry cs loans)
      w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem lifecycle_up_index (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) :
    Campaign2.Ensures wgUp (View.ConfigurationInput cs loans)
      (fun _ => View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (LifecycleIndex.up_entry cs loans)
      w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem lifecycle_stop_index (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) :
    Campaign2.Ensures wgStop (View.ConfigurationInput cs loans)
      (fun _ => View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (LifecycleIndex.stop_entry cs loans)
      w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem lifecycle_down_index (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) :
    Campaign2.Ensures wgDown (View.ConfigurationInput cs loans)
      (fun _ => View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (LifecycleIndex.down_entry cs loans)
      w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run)

/-- Every normally completed original destruction has no device and hence no
index entries, independently of its supplied initial state. No completion is
asserted for paths rejected by the original operation. -/
theorem lifecycle_destruct_index :
    Campaign2.Ensures wgDestruct (fun _ => True)
      (fun _ s => s.wg.device=none ∧ View.IndexCore s) := by
  intro w a result v b pre run
  have post := LifecycleIndex.destruct_core w a result v b pre run
  exact ⟨post.1,post.2⟩

end Leanux.Proofs.WG.Index
