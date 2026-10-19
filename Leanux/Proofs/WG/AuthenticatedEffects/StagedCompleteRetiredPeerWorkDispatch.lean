import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWork

/-! Actual queue dequeue and worker payment use the very same selected owner.
A normal return removes exactly that durable occurrence; other holders and
RX carriers retain their original indices. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Std.Do
open DurableHolders WorkReservations

private theorem pending_account (hi : Account holders cs loans w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p) (flag : Bool) :
    Account holders cs loans {w with dev := some {d with peers := d.peers.insert pid {p with handshakePending := flag}}} := by
  have kept := (pinned_const _private.Leanux.Proofs.WG.Queues.SendDispatch.«0».Leanux.Proofs.WG.Queues.RxCredits.SendDispatch.pending_update)
    ⟨hi.funded.carriers,hi.stable⟩ hd hp flag
  have frame : Frame w {w with dev := some {d with peers := d.peers.insert pid {p with handshakePending := flag}}} := by
    refine ⟨?_,?_,?_⟩
    · simp [passiveView,hd]
    · simp [sendView,hd]
    · intro q batches found
      by_cases same : pid = q <;> simp_all [handoffTxView,Std.TreeMap.getElem?_insert]
  have peers : peerView {w with dev := some {d with peers := d.peers.insert pid {p with handshakePending := flag}}} = peerView w := by
    simp only [peerView,hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl ?_
    funext q
    by_cases same : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]
  exact ⟨⟨hi.funded.aligned.frame frame,kept.1⟩,hi.upper.peer_view peers,kept.2⟩

theorem Account.flushed_clear {holders : DurableHolders}
    (selected : Selected holders.clear pid o rest)
    (hi : Account holders cs loans w) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    Account (holders.withoutClear rest) cs loans v := by
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
  have paid := Account.queued_clear stage
    (by simpa only [selected.slot] using hclear)
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker))
      (fun g => g = cleared)) cleared ac stop stopped aStopped rfl hstop
  subst stopped
  cases hpure
  exact paid

theorem Account.run_one_clear {holders : DurableHolders} (w v : World)
    (hi : Account holders cs loans w.wg)
    (hr : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.clear pid o rest ∧
      Account (holders.withoutClear rest) cs loans v.wg := by
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,hd,_,_,_,member,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v hr
  have queue : holders.clear.map Owner.slot = d.clearWorkQueue := by
    simpa only [hd,Option.map_some,Option.getD_some] using hi.funded.aligned.clear
  obtain ⟨o,rest,selected⟩ := select_exists holders.clear pid (queue ▸ member)
  have paid := Account.flushed_clear selected hi beforeWorker v.ambient worker
  exact ⟨pid,o,rest,selected,paid⟩

theorem Account.flushed_send {holders : DurableHolders}
    (selected : Selected holders.send pid o rest)
    (hi : Account holders cs loans w) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    Account (holders.withoutSend rest) cs loans v := by
  unfold runFlushedSendWork at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,taken,aTaken,hdequeue,tail⟩ := hr
  cases hdequeue
  let taken : WGWorld := {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}}
  have stage := hi.take_send selected
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
    have pending : Account (holders.withoutSend rest) cs (o :: loans) updated :=
      pending_account stage hd hp (d0.sendWorkQueue.contains pid)
    have sameStart := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (fun g => g=updated))
      updated aRead start started aStarted rfl hstart
    subst started
    cases work
    have paid := Account.queued_send pending
      (by simpa only [selected.slot] using hworker)
    have sameStop := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (fun g => g=sent))
      sent aSent stop stopped aStopped rfl hstop
    subst stopped
    cases hpure
    exact paid

theorem Account.run_one_send {holders : DurableHolders} (w v : World)
    (hi : Account holders cs loans w.wg)
    (hr : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.send pid o rest ∧
      Account (holders.withoutSend rest) cs loans v.wg := by
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,hd,_,_,_,member,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v hr
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((hi.funded.aligned.send d hd) ▸ member)
  have paid := Account.flushed_send selected hi beforeWorker v.ambient worker
  exact ⟨pid,o,rest,selected,paid⟩


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
