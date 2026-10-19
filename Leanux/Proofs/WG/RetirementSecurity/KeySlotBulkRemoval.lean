import Leanux.Proofs.WG.RetirementSecurity.KeySlotRemoval

/-! Bulk removal tracks the actual saved list of selected peers. The first
loop adds explicit dead exceptions; the second discharges each only after its
native clear. Repeated numeric slots need no distinctness assumption. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem saved_make_dead (dead : List PeerId) (selected : ∀pid,pid∈dead → pid∈pending) :
    Preserves (InvExcept pending) (for pid in dead do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid : WG.M Unit) := by
  induction dead with
  | nil => exact preserves_pure ()
  | cons pid rest ih =>
    have factor : (for q in pid::rest do
        _ ← branch .peerRemoveAllIter1 true
        peerMakeDead q : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter1 true
        peerMakeDead pid
        for q in rest do
          _ ← branch .peerRemoveAllIter1 true
          peerMakeDead q) := by
      simp only [List.forIn_cons,bind_assoc,pure_bind]
    rw [factor]
    exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 true) _) (fun _=>
      preserves_bind (make_dead_pending pid (selected pid (by simp))) (fun _=>
        ih (fun q member=>selected q (by simp [member]))))

theorem saved_after_dead (dead : List PeerId) : Hoare
    (for pid in dead do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid : WG.M Unit)
    (InvExcept (dead++pending)) (fun _=>InvExcept pending) := by
  induction dead with
  | nil => exact preserves_pure ()
  | cons pid rest ih =>
    have factor : (for q in pid::rest do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead q : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid
        for q in rest do
          _ ← branch .peerRemoveAllIter2 true
          peerRemoveAfterDead q) := by
      simp only [List.forIn_cons,bind_assoc,pure_bind]
    rw [factor]
    exact hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 true) _) (fun _=>
      hoare_bind _ _ (after_dead pid) (fun _=>ih))

theorem entry : Preserves (InvExcept pending) BaseRemoval.entry := by
  unfold BaseRemoval.entry
  exact preserves_bind (combined_frame ConfiguredIdentity.allowedipsFree_view HolderRemoval.free_points)
    (fun _=>preserves_bind (store getDev_sameWGStore) (fun _=>preserves_pure _))

theorem all_peers : Preserves (InvExcept pending) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  rw [BaseRemoval.peerRemoveAll_entry,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨dead,entered,c,start,rest⟩ := run
  have ready := (hoare_iff_run_ambient _ _ _).mp entry w a dead entered c before start
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,marked,d,mark,rest⟩ := rest
  cases ignored
  have markedReady : InvExcept (dead++pending) marked :=
    (hoare_iff_run_ambient _ _ _).mp (saved_make_dead dead (pending:=dead++pending)
      (fun _ h=>List.mem_append_left _ h)) entered c () marked d
      (weaken ready (fun _ h=>List.mem_append_right _ h)) (by
        rw [MaterialOrigin.bind_ok_ambient]
        exact ⟨PUnit.unit,marked,d,mark,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,read,e,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 false) (fun g=>g=marked))
    marked d flag read e rfl decision
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,paid,f,payment,rest⟩ := rest
  cases ignored
  have done := (hoare_iff_run_ambient _ _ _).mp (saved_after_dead dead)
    marked e () paid f markedReady (by
      rw [MaterialOrigin.bind_ok_ambient]
      exact ⟨PUnit.unit,paid,f,payment,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨last,read,g,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 false) (fun state=>state=paid))
    paid f last read g rfl decision
  subst read
  cases rest
  exact done

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
