import Leanux.Proofs.WG.Progress.MaintenanceFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.MaintenanceFinite
open Leanux Leanux.WG

/-! Exact finite evaluation includes every original guard, hidden Stop and
bounded-loop exhaustion. No normal-result or callback premise is imposed. -/

theorem original_send_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.runFlushedSendWork pid) (send pid) := by
  rw [send_source]
  intro g ambient pre
  rfl

theorem original_drain_finite (upTo : Option PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.drainHandshakeSendWq upTo) (drain upTo) := by
  rw [drain_source]
  intro g ambient pre
  rfl

theorem original_timersStop_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.timersStop pid) (timersStop pid) := by
  rw [timersStop_source]
  intro g ambient pre
  rfl

theorem original_afterDead_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.peerRemoveAfterDead pid) (afterDead pid) := by
  rw [afterDead_source]
  intro g ambient pre
  rfl

theorem original_remove_finite (peer : Option PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.peerRemove peer) (remove peer) := by
  rw [remove_source]
  intro g ambient pre
  rfl

theorem original_removeAll_finite  :
    Campaign2.AgreesOn (fun _ => True) (WG.peerRemoveAll) (removeAll) := by
  rw [removeAll_source]
  intro g ambient pre
  rfl

theorem original_destruct_finite  :
    Campaign2.AgreesOn (fun _ => True) (WG.wgDestruct) (destruct) := by
  rw [destruct_source]
  intro g ambient pre
  rfl

theorem original_stop_finite  :
    Campaign2.AgreesOn (fun _ => True) (WG.wgStop) (stop) := by
  rw [stop_source]
  intro g ambient pre
  rfl

theorem original_down_finite  :
    Campaign2.AgreesOn (fun _ => True) (WG.wgDown) (down) := by
  rw [down_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.MaintenanceFinite
