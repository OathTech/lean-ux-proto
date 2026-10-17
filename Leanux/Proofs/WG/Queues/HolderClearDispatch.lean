import Leanux.Proofs.WG.Queues.HolderWorkFrames
import Leanux.Proofs.WG.Queues.EnvClearDispatch

/-! One clear-queue occurrence moves to a transient owner before the actual
worker pays it. Every other lasting holder and RX carrier remains funded. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations

def clearTaken (w : WGWorld) (pid : PeerId) : WGWorld :=
  {w with dev := w.dev.map fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}}

def withoutClear (holders : DurableHolders) (rest : Reservations) : DurableHolders :=
  {holders with clear := rest}

theorem Aligned.take_clear {holders : DurableHolders} (hi : holders.Aligned w)
    (selected : Selected holders.clear pid o rest) :
    (holders.withoutClear rest).Aligned (clearTaken w pid) := by
  refine ⟨?_,?_,?_,?_,hi.cursor7,hi.cursor8⟩
  · simpa only [withoutClear,clearTaken,Option.map_map,Function.comp_def] using hi.base
  · intro d hd
    cases hw : w.dev with
    | none => simp [clearTaken,hw] at hd
    | some old =>
      simp only [clearTaken,hw,Option.map_some,Option.some.injEq] at hd
      cases hd
      exact hi.send old hw
  · change rest.map Owner.slot = _
    rw [←selected.erase,hi.clear]
    unfold clearTaken
    cases w.dev <;> rfl
  · intro q batches found
    apply hi.tx q batches
    simpa only [clearTaken,handoffTxView,Option.bind_map,Function.comp_def] using found

theorem Funded.take_clear {holders : DurableHolders} (hi : holders.Funded cs loans w)
    (selected : Selected holders.clear pid o rest) :
    (holders.withoutClear rest).Funded cs (o :: loans) (clearTaken w pid) := by
  refine ⟨hi.aligned.take_clear selected,?_⟩
  have kept : CarrierState cs (holders.owners ++ loans) (clearTaken w pid) :=
    hi.carriers.view (by
      unfold clearTaken carrierView keyView peerView rxView RxCredits.keyWords RxCredits.currentCells
      cases w.dev <;> rfl)
  exact WorkReservations.carrier_loans_perm kept (by
      apply List.perm_iff_count.mpr
      intro owner
      have count := List.Perm.count_eq selected.perm owner
      simp only [List.count_cons] at count
      simp only [withoutClear,owners,List.count_append,List.count_cons]
      omega)

theorem queued_clear_funded {holders : DurableHolders}
    (hi : holders.Funded cs (o :: loans) w) (stable : StableRx cs w)
    (a b : Ambient)
    (hr : ((queuedExpiredZeroKeyMaterial o.slot).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v := by
  have input : ClearWork.Inv cs (o :: (holders.owners ++ loans)) w :=
    ⟨carrier_loans_perm hi.carriers (List.perm_middle),stable⟩
  have paid := ClearWork.queued_normal o input a b hr
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (HolderWorkFrames.queuedClear_frame o.slot w) w a () v b (Frame.refl w) hr
  exact ⟨⟨hi.aligned.frame frame,paid.1⟩,paid.2⟩

theorem flushed_clear_funded {holders : DurableHolders}
    (selected : Selected holders.clear pid o rest)
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    (holders.withoutClear rest).Funded cs loans v ∧ StableRx cs v := by
  unfold runFlushedClearWork at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,taken,aTaken,hdequeue,start,started,aStarted,hs,u',cleared,ac,hclear,
    stop,stopped,aStopped,hstop,hpure⟩ := hr
  cases hdequeue
  have before := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker))
      (fun g => g = clearTaken w pid)) (clearTaken w pid) a start started aStarted rfl hs
  subst started
  cases u'
  have stage := hi.take_clear selected
  have stableTaken := (ClearWork.erase_queue ⟨hi.carriers,stable⟩ pid).2
  have paid := queued_clear_funded stage stableTaken aStarted ac
    (by simpa only [selected.slot] using hclear)
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker))
      (fun g => g = cleared)) cleared ac stop stopped aStopped rfl hstop
  subst stopped
  cases hpure
  exact paid

theorem runOneClearWorker_funded {holders : DurableHolders} (w v : World)
    (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.clear pid o rest ∧
      (holders.withoutClear rest).Funded cs loans v.wg ∧ StableRx cs v.wg := by
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,hd,_,_,_,member,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v hr
  have queue : holders.clear.map Owner.slot = d.clearWorkQueue := by
    simpa only [hd,Option.map_some,Option.getD_some] using hi.aligned.clear
  obtain ⟨o,rest,selected⟩ := select_exists holders.clear pid (queue ▸ member)
  obtain ⟨funded,stable⟩ := flushed_clear_funded selected hi stable beforeWorker v.ambient worker
  exact ⟨pid,o,rest,selected,funded,stable⟩

theorem runOneClearWorkerAudit_funded {holders : DurableHolders} (w v : World)
    (history : List AuditEvent) (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : (runPrefix runOneClearWorkerAudit w history).1 = .ok ((),v)) :
    ∃ pid o rest, Selected holders.clear pid o rest ∧
      (holders.withoutClear rest).Funded cs loans v.wg ∧ StableRx cs v.wg := by
  exact runOneClearWorker_funded w v hi stable
    ((runOneClearWorkerAudit_erases w history).symm.trans hr)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
