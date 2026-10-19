import Leanux.Proofs.WG.Progress.NativeSuffixSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise
theorem recordQueued_retains (records : List HiddenRecord) (worker : Worker) (pid : Nat) :
    Preserves (fun a=>Tail records a.hidden) (AmbientM.recordQueued worker pid) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  unfold AmbientM.recordQueued at run
  simp only [StateT.run_bind,StateT.run_get,pure_bind] at run
  split at run
  · cases run
    exact pre
  · rw [StateT.run_bind] at run
    cases read : (AmbientM.hidden (.queued worker)).run before with
    | error e => rw [read] at run; cases run
    | ok pair =>
      rcases pair with ⟨bytes,middle⟩
      have kept := strict_tail ((hoare_iff_run _ _ _).mp
        (hidden_after_tail (.queued worker) records) before bytes middle pre read)
      rw [read] at run
      simp only [bind,Except.bind] at run
      change ((get : AmbientM Ambient).run middle >>= _) = .ok (value,after) at run
      rw [show (get : AmbientM Ambient).run middle = .ok (middle,middle) from rfl] at run
      simp only [bind,Except.bind] at run
      split at run
      · cases run; exact kept
      · cases found : middle.unitPeers.find?
          (fun e : Nat × Nat × Nat=>e.2.1 == worker.index && e.2.2 == pid) with
        | none => simp only [found] at run; cases run; exact kept
        | some row =>
          rcases row with ⟨address,kind,owner⟩
          simp only [found] at run
          split at run
          · cases run
          · cases run; exact kept

theorem peekQueued_retains (records : List HiddenRecord) (worker : Worker) (pid : Nat) :
    Preserves (fun a=>Tail records a.hidden) (AmbientM.peekQueuedUnit worker pid) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  unfold AmbientM.peekQueuedUnit at run
  simp only [StateT.run_bind,StateT.run_get,pure_bind] at run
  split at run
  · cases run; exact pre
  · rw [StateT.run_bind] at run
    cases skipped : AmbientM.skipAmbient.run before with
    | error e => rw [skipped] at run; cases run
    | ok pair =>
      rcases pair with ⟨token,middle⟩
      have kept := (hoare_iff_run _ _ _).mp
        (retain_tail Ambient.hidden _ skipAmbient_suffix records) before token middle pre skipped
      rw [skipped] at run
      simp only [bind,Except.bind] at run
      change ((get : AmbientM Ambient).run middle >>= _) = .ok (value,after) at run
      rw [show (get : AmbientM Ambient).run middle = .ok (middle,middle) from rfl] at run
      simp only [bind,Except.bind] at run
      cases present : middle.hidden with
      | none => simp only [present] at run; cases run; exact kept
      | some remaining =>
        cases remaining with
        | nil => simp only [present] at run; cases run; exact kept
        | cons record rest =>
          simp only [present] at run
          split at run
          · cases run; exact kept
          · cases found : middle.unitPeers.find?
              (fun e : Nat × Nat × Nat=>e.2.1 == worker.index && e.2.2 == pid) with
            | none => simp only [found] at run; cases run; exact kept
            | some row =>
              rcases row with ⟨address,kind,owner⟩
              simp only [found] at run
              cases run; exact kept

theorem native_recordQueued (records : List HiddenRecord) (worker : Worker) (pid : Nat) :
    NativeKeeps records (recordQueued worker pid : WG.M Unit) :=
  native_ambient records _ (recordQueued_retains records worker pid)

theorem native_peekQueued (records : List HiddenRecord) (worker : Worker) (pid : Nat) :
    NativeKeeps records (peekQueuedUnit worker pid : WG.M Bool) :=
  native_ambient records _ (peekQueued_retains records worker pid)

theorem queueDeviceWork_retains (records : List HiddenRecord) (worker : Worker) :
    Preserves (fun a=>Tail records a.hidden) (AmbientM.queueDeviceWork worker) := by
  unfold AmbientM.queueDeviceWork
  apply preserves_bind (hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
  intro initial
  split
  · apply preserves_bind (peekQueued_retains records worker 0)
    intro queued
    cases queued with
    | false => exact preserves_pure _
    | true =>
      apply (hoare_iff_run _ _ _).mpr
      intro a value b pre run
      cases run
  · apply preserves_bind (recordQueued_retains records worker 0)
    intro _
    apply (hoare_iff_run _ _ _).mpr
    intro a value b pre run
    cases run
    exact pre

theorem native_queueDeviceWork (records : List HiddenRecord) (worker : Worker) :
    NativeKeeps records (queueDeviceWork worker : WG.M Unit) :=
  native_ambient records _ (queueDeviceWork_retains records worker)

end Leanux.Proofs.WG.Progress.RecordSuffix
