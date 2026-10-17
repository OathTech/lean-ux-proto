import Leanux.Proofs.WG.TimerDiscipline.TimerInputFrames
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The original arbitrary Kernel predicate spans all its subsystem owners.
The actual Ambient lift preserves those owners and the recorded-arm mode. -/
theorem hidden_recorded_kernel_spec
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) (site : HiddenSite) :
    Product.Ensures (liftAmbient (AmbientM.hidden site))
      (fun w => P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = true)
      (fun _ w => P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = true) := by
  intro w result final pre run
  change ((AmbientM.hidden site).run w.ambient >>= fun (value, after) =>
    .ok (value, {w with ambient := after})) = .ok (result, final) at run
  cases read : (AmbientM.hidden site).run w.ambient with
  | error stop => rw [read] at run; cases run
  | ok pair =>
    obtain ⟨value, after⟩ := pair
    rw [read] at run
    cases run
    exact ⟨pre.1, InitiationReady.hidden_mode true site w.ambient result after pre.2 read⟩

theorem callerJiffies_recorded_spec (site : HiddenSite) (d : Device) :
    Campaign2.Ensures (callerJiffies site)
      (fun w => w.wg.device = some d ∧ w.ambient.armRecords = true)
      (fun result w => result.isSome = true ∧ w.wg.device = some d ∧
        w.ambient.armRecords = true) := by
  intro g ambient result final after pre run
  obtain ⟨state, mode, value⟩ := callerJiffies_input_effect site g final ambient after result run
  exact ⟨value.trans pre.2, by change final.dev = some d; rw [state]; exact pre.1, mode.trans pre.2⟩

end Leanux.Proofs.WG.TimerDiscipline
