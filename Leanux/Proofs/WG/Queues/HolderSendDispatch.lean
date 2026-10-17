import Leanux.Proofs.WG.Queues.HolderWorkFrames
import Leanux.Proofs.WG.Queues.SendEnvironment

/-! One send-queue occurrence moves to a transient owner before the actual
worker pays it. Every other lasting holder and RX carrier remains funded. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations

def sendTaken (w : WGWorld) (pid : PeerId) : WGWorld :=
  {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}}

def withoutSend (holders : DurableHolders) (rest : Reservations) : DurableHolders :=
  {holders with send := rest}

theorem Aligned.take_send {holders : DurableHolders} (hi : holders.Aligned w)
    (selected : Selected holders.send pid o rest) :
    (holders.withoutSend rest).Aligned (sendTaken w pid) := by
  refine ⟨?_,?_,?_,?_,hi.cursor7,hi.cursor8⟩
  · simpa only [withoutSend,sendTaken,Option.map_map,Function.comp_def] using hi.base
  · intro d hd
    cases hw : w.dev with
    | none => simp [sendTaken,hw] at hd
    | some old =>
      simp only [sendTaken,hw,Option.map_some,Option.some.injEq] at hd
      cases hd
      exact (congrArg (fun xs => xs.erase pid) (hi.send old hw)).trans selected.erase
  · simpa only [withoutSend,sendTaken,Option.map_map,Function.comp_def] using hi.clear
  · intro q batches found
    apply hi.tx q batches
    simpa only [sendTaken,handoffTxView,Option.bind_map,Function.comp_def] using found

theorem Funded.take_send {holders : DurableHolders} (hi : holders.Funded cs loans w)
    (selected : Selected holders.send pid o rest) :
    (holders.withoutSend rest).Funded cs (o :: loans) (sendTaken w pid) := by
  refine ⟨hi.aligned.take_send selected,?_⟩
  have kept : CarrierState cs (holders.owners ++ loans) (sendTaken w pid) :=
    hi.carriers.view (by
      unfold sendTaken carrierView keyView peerView rxView RxCredits.keyWords RxCredits.currentCells
      cases w.dev <;> rfl)
  exact WorkReservations.carrier_loans_perm kept (by
      apply List.perm_iff_count.mpr
      intro owner
      have count := List.Perm.count_eq selected.perm owner
      simp only [List.count_cons] at count
      simp only [withoutSend,owners,List.count_append,List.count_cons]
      omega)

theorem queued_send_funded {holders : DurableHolders}
    (hi : holders.Funded cs (o :: loans) w) (stable : StableRx cs w)
    (a b : Ambient)
    (hr : ((handshakeSendWorker o.slot).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v := by
  have input : CarrierState cs (o :: (holders.owners ++ loans)) w :=
    carrier_loans_perm hi.carriers List.perm_middle
  have paid := SendWork.worker_normal o input stable a b hr
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (HolderWorkFrames.handshakeSendWorker_frame o.slot w) w a () v b (Frame.refl w) hr
  exact ⟨⟨hi.aligned.frame frame,paid.1⟩,paid.2⟩

private theorem flushed_send_frame (pid : PeerId) (initial : WGWorld) :
    Hoare (runFlushedSendWork pid) (fun g => g = initial) (fun _ => Frame (sendTaken initial pid)) := by
  unfold runFlushedSendWork
  apply hoare_bind _ _ (show Hoare (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
    (fun g => g = initial) (fun _ => Frame (sendTaken initial pid)) from ?_)
  · intro _
    change Preserves (Frame (sendTaken initial pid)) _
    simp (config := {zeta := false}) only [invariant,hidden]
    repeat' first
      | (rx_retention_head handshakeSendWorker; exact HolderWorkFrames.handshakeSendWorker_frame _ _)
      | holder_work_step (sendTaken initial pid)
  · apply hoare_modify
    intro w hi
    subst w
    exact Frame.refl _

theorem flushed_send_funded {holders : DurableHolders}
    (selected : Selected holders.send pid o rest)
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    (holders.withoutSend rest).Funded cs loans v ∧ StableRx cs v := by
  let outside := (holders.withoutSend []).owners ++ loans
  have input : ClearWork.Inv cs (holders.send ++ outside) w :=
    ⟨carrier_loans_perm hi.carriers (by
      apply List.perm_iff_count.mpr
      intro owner
      simp only [outside,withoutSend,owners,List.count_append,List.count_nil]
      omega),stable⟩
  have paid := (SendDispatch.flushed_selected selected input a b hr).1
  have frame := (hoare_iff_run_ambient _ _ _).mp (flushed_send_frame pid w) w a () v b rfl hr
  refine ⟨⟨(hi.aligned.take_send selected).frame frame,carrier_loans_perm paid.1 ?_⟩,paid.2⟩
  apply List.perm_iff_count.mpr
  intro owner
  simp only [outside,withoutSend,owners,List.count_append,List.count_nil]
  omega

theorem runOneSendWorker_funded {holders : DurableHolders} (w v : World)
    (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.send pid o rest ∧
      (holders.withoutSend rest).Funded cs loans v.wg ∧ StableRx cs v.wg := by
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,hd,_,_,_,member,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v hr
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((hi.aligned.send d hd) ▸ member)
  obtain ⟨funded,stable⟩ := flushed_send_funded selected hi stable beforeWorker v.ambient worker
  exact ⟨pid,o,rest,selected,funded,stable⟩

theorem runOneSendWorkerAudit_funded {holders : DurableHolders} (w v : World)
    (history : List AuditEvent) (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : (runPrefix runOneSendWorkerAudit w history).1 = .ok ((),v)) :
    ∃ pid o rest, Selected holders.send pid o rest ∧
      (holders.withoutSend rest).Funded cs loans v.wg ∧ StableRx cs v.wg := by
  exact runOneSendWorker_funded w v hi stable
    ((runOneSendWorkerAudit_erases w history).symm.trans hr)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
