import Leanux.Proofs.WG.TimerDiscipline.RecordedSourceClaims
import Leanux.Proofs.WG.TimerDiscipline.ArmingSourceClaims
import Leanux.Proofs.WG.TimerDiscipline.SourceFrames
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.JitterOutcomeSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.RetrySource
import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

/-- Corrected selected-unit prefix/suffix and worker-kind facts. The historical logical-due conclusion does not hold for arbitrary wheel metadata. -/
theorem source_timer_dispatch_due (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (initial final : World) (d : Device)
    (device : initial.wg.dev = some d)
    (run : (timerDispatchUnit_variant worker pid timer we step).run initial = .ok ((), final)) :
    ∃ selected,
      (timerDispatchPrefix_variant worker pid timer we step).run initial = .ok ((), selected) ∧
      (fireWheelSelected worker pid timer we).run selected = .ok ((), final) ∧
      worker.timer? = some timer ∧ selected.wg.dev = some d :=
  fireTimer_execution worker pid timer we step initial final d device run

/-- Normal selected-unit completion preserves the original retry postcondition, conditional on the actual prefix. Outer selection is a separate obligation. -/
theorem source_retransmit_dispatch (pid : PeerId) (we : WheelEntry) (step : Option UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Noise.Product.Ensures (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we step)
      (fun w => retryAt w.wg pid = some (identity, attempts, timer) ∧
        ∃ selected, (timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step).run w =
          .ok ((), selected))
      (fun _ w => retryAt w.wg pid = some (identity, nextAttempts attempts, none)) :=
  fireTimer_retransmit pid we step identity attempts timer

end Leanux.Proofs.WG.TimerDiscipline
