import Leanux.Env
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Initial record and actual wheel selection only. No successful dispatch,
record sufficiency, readiness, or logical-expiry premise is included. -/
def FirstTimerSelected (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry)
    (entry : Campaign2.Product.Snapshot) : Prop :=
  ∃ d site, entry.wg.device = some d ∧
    (entry.ambient.hidden.bind fun rs =>
      (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)) = some site ∧
    timerSectionOf site = some worker ∧ worker ≠ .clearPeerWorker ∧
    TimerWheel.nextDue d jPass = some (pid, timer, we)

end Leanux.Proofs.WG.TimerDiscipline
