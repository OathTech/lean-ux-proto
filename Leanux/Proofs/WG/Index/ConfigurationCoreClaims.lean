import Leanux.Proofs.WG.Index.ConfigurationCoreBridge
import Leanux.Proofs.WG.Index.ConfigurationDeviceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits
open Queues.RxCredits.DurableHolders

/-- Every normal result of the original mixed device setter preserves its
supplied account, configuration, slot and index package. Errno results retain
the original preceding updates and cleanup; success is not assumed. -/
theorem wgSetDevice_index (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Campaign2.Ensures (wgSetDevice attrs) (View.ConfigurationInput cs loans)
      (fun _=>View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  apply (configurationInput_snapshot cs loans v b).mpr
  exact (hoare_iff_run_ambient _ _ _).mp (ConfigurationIndex.device_entry cs loans attrs)
    w a result v b ((configurationInput_snapshot cs loans w a).mp pre) run

end Leanux.Proofs.WG.Index
