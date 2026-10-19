import Leanux.Proofs.WG.Progress.ReleaseSuffixSource

/-! Physical record-field frames used by the concrete clear dispatch. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem resolveUnit_hidden (records : Option (List HiddenRecord)) (worker : Worker) (unit : Nat) (queue : List Nat) :
    Hoare (AmbientM.resolveUnit worker unit queue)
      (fun a => a.hidden = records) (fun _ a => a.hidden = records) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  simp only [AmbientM.resolveUnit,StateT.run_bind,StateT.run_get,pure_bind] at run
  split at run
  · split at run
    · cases run
    · cases run; exact pre
  · cases run

/-- This physical frame is valid for precisely the supplied record field. -/
theorem modifyAmbient_hidden (records : List HiddenRecord) (f : Ambient → Ambient)
    (same : ∀ a, (f a).hidden = a.hidden) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (modifyAmbient f : Leanux.M Unit) :=
  liftAmbient_contract (modify f) (fun a=>Tail records a.hidden)
    (fun _ a=>Tail records a.hidden)
    (hoare_modify f (fun a h=>by simpa only [same] using h))

end Leanux.Proofs.WG.Progress.RecordSuffix
