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

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise




/-- Every normally completed original timer dispatch selects a resident peer's
pending timer of the worker's kind whose expiry precedes the supplied horizon
under the mirror's time comparison. The actual selection and detached section
suffix execute in sequence. Selection may consume ambient records; it preserves
the kernel state. No firing-order or wall-clock theorem is claimed. -/
theorem source_timer_dispatch_due (worker : Worker) (jHi : UInt64) (initial final : World) (d : Device)
    (device : initial.k.wg = some d) (run : (Env.fireTimer worker jHi).run initial = .ok ((), final)) :
    ∃ pid timer selected,
      (timerSelection worker jHi).run initial = .ok ((pid, timer), selected) ∧
      (fireSelected worker pid timer).run selected = .ok ((), final) ∧
      worker.timer? = some timer ∧ selected.k.wg = some d ∧
      pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
        p.timer timer = some expiry ∧ timeBefore expiry jHi = true :=
  fireTimer_execution worker jHi initial final d device run

/-- When original selection chooses this peer's retransmit timer, a normally
completed original dispatch preserves its allocation identity, increments the
attempt counter at or below the limit, and retains it above the limit. The
retransmit timer is detached and remains detached through this callback; later
worker rearming is outside this call. Selection is an actual prefix run, not an
assumed callback outcome. This is not a universal retry-episode theorem. -/
theorem source_retransmit_dispatch (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Ensures (Env.fireTimer .timerRetransmit jHi)
      (fun w => retryAt w pid = some (identity, attempts, timer) ∧
        ∃ selected, (timerSelection .timerRetransmit jHi).run w =
          .ok ((pid, .retransmitHandshake), selected))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, none)) :=
  fireTimer_retransmit pid jHi identity attempts timer




end Leanux.Proofs.WG.TimerDiscipline
