import Leanux.Proofs.WG.Queues.WorkReservations
import Leanux.Proofs.WG.Queues.WorkQueueFrames

/-! Clear-work dequeue transfers one existing ordered reservation to the
worker local. The unchanged worker pays it, including a possible final put. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ClearWork
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations

theorem erase_queue (hi : Inv cs loans w) (pid : PeerId) :
    Inv cs loans {w with dev := w.dev.map fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}} := by
  refine ⟨hi.1.view ?_,hi.2.view ?_⟩
  · unfold carrierView keyView peerView rxView RxCredits.keyWords RxCredits.currentCells
    cases w.dev <;> rfl
  · unfold stableView RxRing.nativeCell rxView
    cases w.dev <;> rfl

theorem flushed_selected (selected : WorkReservations.Selected owners pid o restOwners)
    (hi : Inv cs (owners ++ loans) w) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    Inv cs (restOwners ++ loans) v ∧
      queueView v = (queueView w).map (fun q => (q.1,q.2.erase pid)) := by
  have funded := selected_funded hi selected
  unfold runFlushedClearWork at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,taken,aTaken,hdequeue,start,started,aStarted,hs,u',cleared,ac,hclear,
    stop,stopped,aStopped,hstop,hpure⟩ := hr
  cases hdequeue
  let taken : WGWorld := {w with dev := w.dev.map fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}}
  have stage := erase_queue funded pid
  have before := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker))
      (fun g => g = taken)) taken a start started aStarted rfl hs
  subst started
  cases u'
  have paid := queued_normal o stage aStarted ac (by simpa only [selected.slot] using hclear)
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker))
      (fun g => g = cleared)) cleared ac stop stopped aStopped rfl hstop
  subst stopped
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (WorkQueueFrames.queuedClear_clear pid) taken aStarted () cleared ac hclear
  cases hpure
  refine ⟨paid,?_⟩
  rw [frame]
  simp [queueView,taken,Option.map_map,Function.comp_def]

/-- The list of stamped owners is aligned with the actual queue before
selection. Repeated peer ids retain every occurrence except the first one. -/
theorem flushed_normal (hi : Inv cs (owners ++ loans) w)
    (queue : queueView w = some (epoch,owners.map Owner.slot))
    (present : pid ∈ owners.map Owner.slot) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    ∃ o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      Inv cs (restOwners ++ loans) v ∧
      queueView v = some (epoch,restOwners.map Owner.slot) := by
  obtain ⟨o,restOwners,selected⟩ := select_exists owners pid present
  obtain ⟨kept,after⟩ := flushed_selected selected hi a b hr
  exact ⟨o,restOwners,selected,kept,by simpa [queue,selected.erase] using after⟩

/-- The timer appends its newly acquired source owner to the ordered work
ledger. A coalesced enqueue appends nothing, after its actual repayment. -/
theorem timer_accounts (hi : Inv cs (owners ++ loans) w)
    (queue : queueView w = some (epoch,owners.map Owner.slot)) (a b : Ambient)
    (hr : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      Inv cs ((owners ++ added) ++ loans) v ∧
      queueView v = some (epoch,(owners ++ added).map Owner.slot) := by
  obtain ⟨added,source,kept,after⟩ := timer_normal hi a b hr
  have order : (added ++ (owners ++ loans)).Perm ((owners ++ added) ++ loans) := by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := added) (l₂ := owners)).append_right loans
  refine ⟨added,source,⟨carrier_loans_perm kept.1 order,kept.2⟩,?_⟩
  simpa [queue,List.map_append] using after

end Leanux.Proofs.WG.Queues.RxCredits.ClearWork
