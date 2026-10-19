import Leanux.Proofs.WG.Progress.MaintenanceFiniteSource
import Leanux.Proofs.WG.Noise.DriverTagEnvironmentFactors
import Leanux.Proofs.WG.Queues.JointDelete

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.LifecycleFinite
open Leanux Leanux.WG

/-- Original environment down, using the concrete finite native stop/drain
callback. The actual idle checks, routing notifications and all Stops remain. -/
def envDown : Leanux.M Int :=
  Noise.DriverTags.Environment.envDownWith (fun {_} a => a) Env.requireIdleDevice
    (liftWG MaintenanceFinite.down)

theorem envDown_source : Env.wgDown = envDown := by
  rw [Noise.DriverTags.Environment.envDown_factor, MaintenanceFinite.down_source]
  rfl


/-- Actual environment deletion with finite down and destruction callbacks.
The stepped-dump and idle checks remain the original native guards. -/
def envDelete : Leanux.M Int :=
  Configuration.envDeleteWith (fun {_} a => a) Env.requireIdleDevice
    (liftWG MaintenanceFinite.down) (liftWG MaintenanceFinite.destruct)

theorem envDelete_source : Env.wgDelete = envDelete := by
  rw [Configuration.envDelete_factor, MaintenanceFinite.down_source, MaintenanceFinite.destruct_source]
  rfl

end Leanux.Proofs.WG.Progress.LifecycleFinite
