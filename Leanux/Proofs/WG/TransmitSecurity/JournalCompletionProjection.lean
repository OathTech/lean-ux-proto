import Leanux.Proofs.WG.TransmitSecurity.JournalSource

/-! The TX callback's socket and disposition receipts are retained in the
shared journal at their actual execution positions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem transmit_completion_projection (pid : PeerId) :
    ProjectsPrefix completion? id (transmit pid) (Completion.step pid) :=
  (Completion.step_appends pid).project_focus completionEvent completion? (fun e => by cases e <;> rfl)

theorem transmit_socket_receipts (pid : PeerId) (w : World) (h : List Event)
    (incoming : Completion.Good (h.filterMap completion?)) :
    Completion.Good ((runPrefix (transmit pid) w h).2.filterMap completion?) := by
  have exactRun := transmit_completion_projection pid w h
  obtain ⟨_,_,safe,_⟩ := Completion.step_safe pid w (h.filterMap completion?) incoming
  rw [exactRun] at safe
  exact safe

end Leanux.Proofs.WG.TransmitSecurity.Journal
