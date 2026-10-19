import Leanux.Proofs.WG.RetirementSecurity.TxActorRun

/-! The original dispatch prefix moves a dequeued TX peer into the selected
activation. Non-TX dispatch leaves the outstanding TX actors in Ambient.
The source iteration contract is consumed by the exact native run factor. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem At.dispatch (before : At P crypt [] w) (pid : PeerId)
    (other : Preserves P (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}))
    (run : (liftWG (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid})).run w=.ok ((),v)) :
    At P crypt [pid] v := by
  have native:=HolderPoll.native_receipt run
  have service:=before.1.dispatch pid w.ambient v.ambient native
  have kept:=(hoare_iff_run_ambient _ _ _).mp other w.wg w.ambient () v.wg v.ambient before.2 native
  cases run
  exact ⟨service,kept⟩

def Selection (P : WGWorld→Prop) (crypt : List (List SkbId))
    (selected : Option Activation) (w : World) : Prop :=
  At P crypt ((selected.bind actor).toList) w

theorem start_service (before : At P crypt (actor act).toList w)
    (run : (do _←Leanux.hidden (.sectionStart act.worker); pure (some act) : Leanux.M (Option Activation)).run w=
      .ok (selected,v)) : Selection P crypt selected v := by
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,started,returned⟩:=run
  cases returned
  exact before.frame ((ProjectedAction.iff_run _ _ _).mp
    (TxActorFrames.hidden_product (.sectionStart act.worker)) w _ v started)

theorem select_unit (worker : Worker) (queue : List PeerId) (fallback : PeerId) :
    SameView (fun w : World=>(w.wg,w.ambient.suspended))
      (do match ←peekUnit worker with
          | some unit=>resolveUnit worker unit queue
          | none=>pure fallback : Leanux.M PeerId) := by
  apply (TxActorFrames.lift_ambient (TxActorFrames.peek_unit worker)).bind
  intro selected
  cases selected with
  | none=>exact SameView.pure _ _
  | some unit=>exact TxActorFrames.lift_ambient (TxActorFrames.resolve worker unit queue)

theorem begin_service
    (work : ∀pid,Preserves P (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}))
    (before : At P crypt [] w) (worker : Worker)
    (run : (TxDisposition.DispatchCuts.begin worker).run w=.ok (selected,v)) :
    Selection P crypt selected v := by
  unfold TxDisposition.DispatchCuts.begin at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨d,u,read,tail⟩:=run
  have same:u=w := (ProjectedAction.iff_run _ _ _).mp TxActorFrames.device w d u read
  subst u
  cases worker with
  | txWorker=>
    dsimp only at tail
    split at tail
    · rename_i pid found
      rw [MaterialOrigin.bind_ok] at tail
      obtain ⟨unit,u,peek,tail⟩:=tail
      have pending:At P crypt [] u := before.frame
        ((ProjectedAction.iff_run _ _ _).mp
          (TxActorFrames.lift_ambient (TxActorFrames.peek_unit .txWorker)) w unit u peek)
      have finish (chosen : PeerId) (t : World) (service : At P crypt [] t)
          (tail : (do
            liftWG (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase chosen})
            _←Leanux.hidden (.sectionStart .txWorker)
            pure (some {worker:=Worker.txWorker,pid:=some chosen}) : Leanux.M (Option Activation)).run t=
              .ok (selected,v)) : Selection P crypt selected v := by
        rw [MaterialOrigin.bind_ok] at tail
        obtain ⟨_,last,dequeued,tail⟩:=tail
        exact start_service (act:={worker:=.txWorker,pid:=some chosen})
          (service.dispatch chosen (work chosen) dequeued) tail
      cases unit with
      | none=>
        rw [MaterialOrigin.bind_ok] at tail
        obtain ⟨chosen,t,pureRun,tail⟩:=tail
        cases pureRun
        exact finish pid u pending tail
      | some unit=>
        rw [MaterialOrigin.bind_ok] at tail
        obtain ⟨chosen,t,resolved,tail⟩:=tail
        exact finish chosen t (pending.frame
          ((ProjectedAction.iff_run _ _ _).mp
            (TxActorFrames.lift_ambient (TxActorFrames.resolve .txWorker unit d.txWorkQueue))
              u chosen t resolved)) tail
    · cases tail; exact before
  | encryptWorker=>
    dsimp only at tail
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨eligible,u,queried,tail⟩:=tail
    have same:u=w := (ProjectedAction.iff_run _ _ _).mp
      (TxActorFrames.pending_device .encryptWorker !d.encryptQueue.empty) w eligible u queried
    subst u
    split at tail
    · cases tail; exact before
    · exact start_service (act:={worker:=.encryptWorker}) before tail
  | decryptWorker=>
    dsimp only at tail
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨eligible,u,queried,tail⟩:=tail
    have same:u=w := (ProjectedAction.iff_run _ _ _).mp
      (TxActorFrames.pending_device .decryptWorker !d.decryptQueue.empty) w eligible u queried
    subst u
    split at tail
    · cases tail; exact before
    · exact start_service (act:={worker:=.decryptWorker}) before tail
  | receiveWorker=>
    dsimp only at tail
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨eligible,u,queried,tail⟩:=tail
    have same:u=w := (ProjectedAction.iff_run _ _ _).mp
      (TxActorFrames.pending_device .receiveWorker !d.handshakeQueue.empty) w eligible u queried
    subst u
    split at tail
    · cases tail; exact before
    · exact start_service (act:={worker:=.receiveWorker}) before tail
  | sendWorker | netRx | timerRetransmit | timerSendKeepalive | timerNewHandshake | timerZeroKey |
      clearPeerWorker | timerPersistentKeepalive | netnsCleanup | linkwatch=>
    cases tail; exact before

theorem dispatch_service
    (work : ∀pid,Preserves P (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}))
    (iteration : IterationContract P crypt) (before : At P crypt [] w) (worker : Worker)
    (run : (Env.dispatch worker).run w=.ok (result,v)) : At P crypt [] v := by
  rw [TxDisposition.DispatchCuts.dispatch_factor,MaterialOrigin.bind_ok] at run
  obtain ⟨selected,u,began,tail⟩:=run
  have chosen:=begin_service work before worker began
  cases selected with
  | none=>cases tail; exact chosen
  | some act=>
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,t,activated,returned⟩:=tail
    cases returned
    exact activation_service iteration chosen activated

end Leanux.Proofs.WG.RetirementSecurity.TxWork
