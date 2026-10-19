import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityRestore
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! The actual take and completed-selection observations are quiet for
allocation availability. Native selection facts extend over their real suffix;
no old history position is identified with a shifted one. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem selection_actual (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (CausalJournal.selection pid)
      (fun value h w _ => Carrier h w ∧ ∀ peer key, value = some (peer,key) → Saved h pid peer w) := by
  intro w a h before
  have quiet := CallbackQuiet.selection allocation? (fun _ => rfl) (fun _ _ => rfl) pid
  obtain ⟨suffix,grown⟩ := quiet.1 w a h
  have excluded := suffix_quiet quiet.2 grown
  have safe : Safe (runPrefix ((CausalJournal.selection pid).run w) a h).2 := by
    rw [grown]
    exact before.2.quiet excluded
  refine ⟨suffix,grown,safe,?_⟩
  cases outcome : (runPrefix ((CausalJournal.selection pid).run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have erase : ErasesStatePrefix (CausalJournal.selection pid)
        (HandshakeSecurity.Responder.selectionPrefix pid) :=
      receiptWGObserved_erases
        (HandshakeSecurity.StagedConservation.Take.observed_erases Event.stagingTaken pid) _
    have native := (erase w a h).symm.trans outcome
    obtain ⟨inv,saved⟩ := selection_origin pid ⟨value,w,v,a,b⟩ native before.1
    refine ⟨⟨?_,safe⟩,?_⟩
    · rw [grown]
      exact inv.append (fun _ event member => no_use (excluded event member))
    · intro peer key selected
      rw [grown]
      exact (saved peer key selected).append
        (fun event member => no_use (excluded event member))

theorem restore_actual (pid : PeerId) (peer : Peer) :
    StatePrefixEnsures (Held pid peer) Safe
      (CausalJournal.stagedRestore pid peer.staged) (fun _ h w _ => Carrier h w) := by
  unfold CausalJournal.stagedRestore HandshakeSecurity.StagedConservation.Restore.observed
    receiptWGObserved
  apply StatePrefixEnsures.bind ((held_restore pid peer).captureWGObserved.consequence
    (Q' := fun _ h w _ => Carrier h w)
    (fun _ _ _ before => before) (fun _ _ _ _ after => by
      obtain ⟨rfl,rfl,kept,_⟩ := after
      exact kept))
  intro receipt
  apply StatePrefixEnsures.bind (state_emit (.stagedRestored ⟨pid,peer.staged,receipt⟩) rfl)
  intro _
  exact state_pure receipt.value

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
