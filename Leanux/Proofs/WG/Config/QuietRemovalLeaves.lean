import Leanux.Proofs.WG.Config.QuietRemovalSource
import Leanux.Proofs.WG.Config.QuietRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem decrementPeerCount_returns (d : Device) (positive : 0 < d.numPeers) :
    Returns decrementPeerCount (fun w => w.dev = some d)
      (fun _ w => w.dev = some { d with numPeers := d.numPeers - 1 }) := by
  intro g ambient device
  refine ⟨(), {g with dev := some {d with numPeers := d.numPeers - 1}}, ambient, ?_, rfl⟩
  have nonzero : d.numPeers ≠ 0 := by omega
  simp [decrementPeerCount, getDev, device, nonzero, modifyDev]
  rfl

end Leanux.Proofs.WG.Config
