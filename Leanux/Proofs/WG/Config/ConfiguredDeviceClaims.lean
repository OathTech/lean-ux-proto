import Leanux.Proofs.WG.Config.ConfiguredDeviceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- Projected mixed-setter contract. Address shape is required only of actual
parsed list members; no final representation, residency or readiness is assumed. -/
theorem original_device (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    Campaign2.Ensures (wgSetDevice attrs) (ProjectedEntry cs loans) (fun _=>ProjectedEntry cs loans) := by
  intro g a result v b pre run
  exact (entry_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (device_entry cs loans attrs shape)
      g a result v b ((entry_snapshot cs loans g a).mp pre) run)


end Leanux.Proofs.WG.Config.OwnerConfiguration
