import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnModel
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- The first actual selected unit is followed by the unchanged outer
continuation, with exact success/error agreement on the full Product view. -/
theorem runTimers_first_timer_agrees (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) :
    Campaign2.Product.AgreesOn (FirstTimerSelected jPass worker pid timer we)
      (Env.runTimers jPass) (firstTimerSelectedSource jPass worker pid timer we) := by
  intro initial pre
  obtain ⟨d, site, device, nextSite, sectionMatch, notClear, selected⟩ := pre
  exact congrArg Campaign2.Product.observeResult
    (runTimers_first_timer_run jPass worker pid timer we initial d site
      device nextSite sectionMatch notClear selected)

end Leanux.Proofs.WG.TimerDiscipline
