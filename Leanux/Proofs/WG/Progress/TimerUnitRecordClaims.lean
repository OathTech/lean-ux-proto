import Leanux.Proofs.WG.Progress.TimerUnitRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result decrease for the exact timer-unit factor used by
the original wheel dispatcher. No timer readiness, guard success or return
existence is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
open Leanux.Proofs.WG.TimerDiscipline

theorem timerDispatchUnit_record_strict (records : List HiddenRecord) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) (step : Option UInt64) :
    Campaign2.Product.Ensures (timerDispatchUnit_variant worker pid timer entry step)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (timerDispatchUnit_strict records worker pid timer entry step)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
