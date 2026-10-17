import Leanux.Proofs.WG.Noise.FreshLifecycleFrames
import Leanux.Proofs.WG.Noise.RotationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Ordered rotation may release aliased keys, but does not write another
peer's slot record. No key residency or release-readiness premise is added. -/
theorem rotationRun_other_peer {actor tracked : PeerId} {d final : Device}
    {actions : List RotationAction} (different : actor ≠ tracked)
    (steps : RotationRun actor d actions final) :
    final.peers[tracked]? = d.peers[tracked]? := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih =>
    simpa [rotationWriteDevice,Std.TreeMap.getElem?_insert,different] using ih
  | put d middle final key rest release tail ih =>
    rw [ih,clearPut_peers release]

/-- Clearing another peer does not write the tracked peer, even if the two
peers' key slots alias and the actual release erases a key. -/
theorem clearRun_other_peer {actor tracked : PeerId} {d final : Device}
    {slots : List ClearSlot} (different : actor ≠ tracked)
    (steps : ClearRun actor d slots final) :
    final.peers[tracked]? = d.peers[tracked]? := by
  induction steps with
  | nil => rfl
  | cons d slot p middle final rest resident put tail ih =>
    rw [ih,clearPut_peers put]
    simp [clearWrite,Std.TreeMap.getElem?_insert,different]

end Leanux.Proofs.WG.Noise
