import Leanux.Proofs.WG.Queues.SendWork
import Leanux.Proofs.WG.Queues.WorkReservations
import Leanux.Proofs.WG.Queues.WorkQueueFrames
import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit

/-! Send-work selection consumes one supplied occurrence, preserving all other
stamped reservations and the exact work-queue order. These are conditional
normal-execution contracts, not claims that every queued callback returns. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SendDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations

abbrev Inv := ClearWork.Inv

def queueView (w : WGWorld) := w.dev.map fun d => (d.ifindex,d.sendWorkQueue)

private theorem erase_queue (hi : Inv cs loans w) (pid : PeerId) :
    Inv cs loans {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}} := by
  refine ⟨hi.1.view ?_,hi.2.view ?_⟩
  · unfold carrierView keyView peerView rxView RxCredits.keyWords RxCredits.currentCells
    cases w.dev <;> rfl
  · unfold stableView RxRing.nativeCell rxView
    cases w.dev <;> rfl

private theorem pending_update (hi : Inv cs loans w) (hd : w.dev=some d)
    (hp : d.peers[pid]?=some p) (flag : Bool) :
    Inv cs loans {w with dev := some {d with peers := d.peers.insert pid {p with handshakePending := flag}}} :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.peer_update)
    hi hd hp _ rfl rfl rfl rfl (fun _ h => h)

/-- The actual flush erases the first matching work occurrence, updates
PENDING from the remaining queue, then pays that occurrence's reservation. -/
theorem flushed_selected (selected : Selected owners pid o restOwners)
    (hi : Inv cs (owners ++ loans) w) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a=.ok (((),v),b)) :
    Inv cs (restOwners ++ loans) v ∧
      queueView v=(queueView w).map (fun q => (q.1,q.2.erase pid)) := by
  have funded := selected_funded hi selected
  unfold runFlushedSendWork at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,taken,aTaken,hdequeue,tail⟩ := hr
  cases hdequeue
  let taken : WGWorld := {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}}
  have stage := erase_queue funded pid
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨p,read,aRead,hread,tail⟩ := tail
  obtain ⟨rfl,rfl,d0,hd,hp⟩ := getPeer_normal pid taken read p a aRead hread
  cases flag : p.handshakePending with
  | false =>
    simp [flag,invariant,AmbientM.invariant,StateT.run_bind] at tail
    cases tail
  | true =>
    simp only [flag,Bool.not_true,Bool.false_eq_true,↓reduceIte] at tail
    simp only [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨d,readDev,aDev,hdev,set,written,aWritten,hset,start,started,aStarted,hstart,
      work,sent,aSent,hworker,stop,stopped,aStopped,hstop,hpure⟩ := tail
    have eqDev : ((d0,taken),aRead)=((d,readDev),aDev) := by
      simpa [getDev,hd] using hdev
    cases eqDev
    let updated : WGWorld := {taken with dev := some {d0 with peers := d0.peers.insert pid {p with handshakePending := d0.sendWorkQueue.contains pid}}}
    have writeEq : (((),updated),aRead)=((set,written),aWritten) := by
      simpa [setPeer,modifyDev,hd,updated] using hset
    have hw : written=updated := (congrArg (fun q => q.1.2) writeEq).symm
    have ha : aWritten=aRead := (congrArg Prod.snd writeEq).symm
    subst written
    subst aWritten
    cases set
    have pending := pending_update stage hd hp (d0.sendWorkQueue.contains pid)
    have sameStart := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (fun g => g=updated))
      updated aRead start started aStarted rfl hstart
    subst started
    cases work
    have paid := SendWork.worker_normal o pending.1 pending.2 aStarted aSent
      (by simpa only [selected.slot] using hworker)
    have sameStop := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (fun g => g=sent))
      sent aSent stop stopped aStopped rfl hstop
    subst stopped
    have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
      (SendWork.worker_workQueues pid) updated aStarted () sent aSent hworker
    cases hpure
    refine ⟨paid,?_⟩
    have factor (g : WGWorld) : queueView g = (WorkQueueFrames.view g).map (fun q => (q.1,q.2.1)) := by
      simp only [queueView,WorkQueueFrames.view,Option.map_map,Function.comp_def]
    have qpaid : queueView v=queueView updated := by rw [factor,factor,queues]
    have qpending : queueView updated=queueView taken := by simp [queueView,updated,hd]
    exact qpaid.trans (qpending.trans (by
      simp [queueView,taken,Option.map_map,Function.comp_def]))

/-- An aligned ordered queue supplies the owner being paid. Duplicate peer
ids remain represented by all unselected reservation occurrences. -/
theorem flushed_normal (hi : Inv cs (owners ++ loans) w)
    (queue : queueView w=some (epoch,owners.map Owner.slot))
    (present : pid∈owners.map Owner.slot) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a=.ok (((),v),b)) :
    ∃ o restOwners, Selected owners pid o restOwners ∧
      Inv cs (restOwners ++ loans) v ∧ queueView v=some (epoch,restOwners.map Owner.slot) := by
  obtain ⟨o,restOwners,selected⟩ := select_exists owners pid present
  obtain ⟨kept,after⟩ := flushed_selected selected hi a b hr
  exact ⟨o,restOwners,selected,kept,by simpa [queue,selected.erase] using after⟩

end Leanux.Proofs.WG.Queues.RxCredits.SendDispatch
