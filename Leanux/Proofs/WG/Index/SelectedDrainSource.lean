import Leanux.Proofs.WG.Index.SelectedDrainFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.SelectedDrain
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open Queues.RxCredits
open Noise.DriverTags.Flush

theorem placeholder_preserves (P : WGWorld → Prop) (send clear : PeerId → WG.M Unit)
    (hs : SendKeeps P send) (hc : ClearKeeps P clear) (d : Device) (upTo : Option PeerId) :
    Hoare (placeholderWith send clear d upTo) (fun w => P w ∧ w.dev = some d)
      (fun _ => P) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a step v b hi run
  unfold placeholderWith at run
  cases headSend : d.sendWorkQueue.head? with
  | some pid =>
    simp only [headSend,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨done,paid,after,worker,finish⟩ := run
    cases done
    have kept := hs w paid d pid a after hi.1 hi.2 (List.mem_of_head? headSend) worker
    cases finish
    exact kept
  | none =>
    cases headClear : d.clearWorkQueue.head? with
    | none =>
      simp only [headSend,headClear] at run
      cases run
      exact hi.1
    | some pid =>
      simp only [headSend,headClear,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨done,paid,after,worker,finish⟩ := run
      cases done
      have kept := hc w paid d pid a after hi.1 hi.2 (List.mem_of_head? headClear) worker
      split at finish <;> cases finish <;> exact kept

theorem turn_preserves (P : WGWorld → Prop) (send clear : PeerId → WG.M Unit)
    (hs : SendKeeps P send) (hc : ClearKeeps P clear) (upTo : Option PeerId) :
    Preserves P (turnWith (fun {_} a => a) send clear upTo) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a step v b hi run
  unfold turnWith at run
  dsimp only at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,ar,getter,rest⟩ := run
  obtain ⟨readEq,ambientEq,hd⟩ := DecryptCarrier.getDev_current a ar getter
  subst read
  subst ar
  split at rest
  · cases rest; exact hi
  · rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨unit,peeked,ap,peek,rest⟩ := rest
    obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .sendWorker) w peeked a ap unit peek
    subst peeked
    cases unit with
    | some u =>
      simp only [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨pid,picked,ac,resolve,done,paid,ad,worker,finish⟩ := rest
      obtain ⟨same,resolver⟩ := ambient_cut (AmbientM.resolveUnit .sendWorker u d.sendWorkQueue)
        w picked ap ac pid resolve
      subst picked
      cases done
      have kept := hs w paid d pid ac ad hi hd
        (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 worker
      cases finish
      exact kept
    | none =>
      simp only [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨unit,peeked,ac,peek,rest⟩ := rest
      obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .clearPeerWorker) w peeked ap ac unit peek
      subst peeked
      cases unit with
      | some u =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨pid,picked,ar,resolve,done,paid,ad,worker,finish⟩ := rest
        obtain ⟨same,resolver⟩ := ambient_cut
          (AmbientM.resolveUnit .clearPeerWorker u d.clearWorkQueue) w picked ac ar pid resolve
        subst picked
        cases done
        have kept := hc w paid d pid ar ad hi hd
          (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 worker
        split at finish <;> cases finish <;> exact kept
      | none =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨current,read,ar,getter,rest⟩ := rest
        obtain ⟨same,_⟩ := ambient_cut (get : AmbientM Ambient) w read ac ar current getter
        subst read
        split at rest
        · cases rest
        · exact (hoare_iff_run_ambient _ _ _).mp
            (placeholder_preserves P send clear hs hc d upTo) w ar step v b ⟨hi,hd⟩ rest

theorem drain_preserves (P : WGWorld → Prop) (send clear : PeerId → WG.M Unit)
    (hs : SendKeeps P send) (hc : ClearKeeps P clear) (upTo : Option PeerId) :
    Preserves P (drainWith (fun {_} a => a) send clear upTo) := by
  unfold drainWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec id P
    intro i acc
    exact turn_preserves P send clear hs hc upTo
  · rintro ⟨result,⟨⟩⟩
    cases result with
    | none => exact hoare_liftAmbient (AmbientM.invariant _) _
    | some result => exact preserves_pure result

theorem original_preserves (P : WGWorld → Prop)
    (hs : SendKeeps P runFlushedSendWork) (hc : ClearKeeps P runFlushedClearWork)
    (upTo : Option PeerId) : Preserves P (drainHandshakeSendWq upTo) := by
  rw [drain_factor]
  exact drain_preserves P runFlushedSendWork runFlushedClearWork hs hc upTo

end Leanux.Proofs.WG.Index.SelectedDrain
