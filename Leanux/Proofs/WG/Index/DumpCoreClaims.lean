import Leanux.Proofs.WG.Index.DumpDispatchSource
import Leanux.Proofs.WG.Index.ConfigurationCoreBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem dump_device_index (cs : Ledger) (loans : Reservations) (ref : DeviceRef) :
    Campaign2.Ensures (wgGetDevice ref) (View.ConfigurationInput cs loans)
      (fun _=>View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (DumpCore.device_entry cs loans ref) w a result v b
      ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem dump_start_index (cs : Ledger) (loans : Reservations) (fd : Nat) (ref : DeviceRef) :
    Campaign2.Ensures (netlinkDumpStart fd ref) (View.ConfigurationInput cs loans)
      (fun _=>View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (DumpCore.start_entry cs loans fd ref) w a result v b
      ((configurationInput_snapshot cs loans w a).mp pre) run)

theorem dump_receive_index (cs : Ledger) (loans : Reservations) (fd : Nat) :
    Campaign2.Ensures (netlinkRecvmsg fd) (View.ConfigurationInput cs loans)
      (fun _=>View.ConfigurationInput cs loans) := by
  intro w a result v b pre run
  exact (configurationInput_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (DumpCore.receive_entry cs loans fd) w a result v b
      ((configurationInput_snapshot cs loans w a).mp pre) run)

end Leanux.Proofs.WG.Index
