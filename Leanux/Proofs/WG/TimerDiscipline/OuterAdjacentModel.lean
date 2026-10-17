import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- A qualifying adjacent pair receives the original retry certificate at its
actual two turn exits. This is conditional on the observed branch/queue shape,
not a claim that every timer history decomposes into pairs. -/
def OuterAdjacentRetryPair (jPass : UInt64) (left right : OuterTimerTurnReceipt) : Prop :=
  ∀ (d after : Device) (pid : PeerId) (we : WheelEntry),
    left.before.wg.device = some d → d.sendWorkQueue = [] →
    outerTimerChoice jPass left.before = some ⟨.timerRetransmit,pid,.retransmitHandshake,we⟩ →
    (right.before.ambient.hidden.bind fun rs =>
      (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)) =
        some (HiddenSite.sectionStart .sendWorker).info.id →
    right.before.wg.device = some after → after.sendWorkQueue.isEmpty = false →
    ∃ observation,
      RetryDispatchCertificate d ⟨pid,we,left.control.2⟩ observation right.after ∧
      observation.afterTimer = left.after ∧
      left.unit = observation.timer.map (fun (value,final) =>
        (some ⟨⟨.timerRetransmit,pid,.retransmitHandshake,we⟩,value.2.2⟩,final))


end Leanux.Proofs.WG.TimerDiscipline
