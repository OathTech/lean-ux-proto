import Leanux.Kernel.Defs
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false



namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
/-- Peeking preserves all original subsystem owners jointly with unit associations. -/
theorem peekUnit_dispatch_frame
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → List (Nat × Nat × Nat) → Prop) :
    Product.Ensures (peekUnit .sendWorker : Leanux.M (Option Nat))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.unitPeers)
      (fun _ w => P w.wg w.fs w.tasks w.seccomp w.ambient.unitPeers) := by
  intro w result final pre run
  change ((AmbientM.peekUnit .sendWorker).run w.ambient >>= fun (value, after) =>
    Except.ok (value, {w with ambient := after})) = Except.ok (result, final) at run
  cases peek : (AmbientM.peekUnit .sendWorker).run w.ambient with
  | error stop => rw [peek] at run; cases run
  | ok pair =>
    obtain ⟨value, after⟩ := pair
    rw [peek] at run
    cases run
    have same : after.unitPeers = w.ambient.unitPeers := by
      cases records : w.ambient.hidden with
      | none =>
        simp [AmbientM.peekUnit, AmbientM.skipAmbient, records] at peek
        cases peek
        rfl
      | some records =>
        simp [AmbientM.peekUnit, AmbientM.skipAmbient, records] at peek
        split at peek
        all_goals try split at peek
        all_goals simp_all [StateT.run_pure]
        all_goals cases peek <;> rfl
    rw [same]
    exact pre
end Leanux.Proofs.WG.TimerDiscipline
