import Leanux.Proofs.WG.TimerDiscipline.RetrySelectedFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- A following worker's actual normal return excludes the selected-unit give-up
case. This derives the entry attempt bound without assuming it. -/
theorem fireSelected_send_limit (pid : PeerId) (we : WheelEntry) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (selected afterTimer final : World) (device : selected.wg.dev = some d)
    (timerRun : (fireWheelSelected .timerRetransmit pid .retransmitHandshake we).run selected = .ok ((), afterTimer))
    (sendRun : Env.runOneSendWorker.run afterTimer = .ok ((), final)) :
    p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES := by
  by_cases limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES
  · exact limit
  apply False.elim
  have above : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts := by omega
  have queue := fireSelected_giveUp_empty pid we d p resident empty above
    selected () afterTimer device timerRun
  cases hd : afterTimer.wg.dev with
  | none => simp [hd] at queue
  | some out =>
    have emptied : out.sendWorkQueue = [] := by simpa [hd] using queue
    exact sendDispatch_nonempty out afterTimer () final hd sendRun emptied

end Leanux.Proofs.WG.TimerDiscipline
