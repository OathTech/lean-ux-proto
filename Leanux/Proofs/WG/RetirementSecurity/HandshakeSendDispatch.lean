import Leanux.Proofs.WG.RetirementSecurity.HandshakeSendHolders

/-! Original queued send dispatch transfers the selected actual durable peer
occurrence into a source local, updates PENDING, sends, and pays that local.
The concrete key-reference account survives the complete native path. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open Queues.RxCredits.WorkReservations

theorem HolderAccount.flushed_send (account : HolderAccount temporary w)
    (selected : Selected holders.send pid o rest)
    (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (a b : Ambient)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  unfold runFlushedSendWork at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,taken,aTaken,dequeue,tail⟩ := run
  cases dequeue
  let taken := DurableHolders.sendTaken w pid
  have points : ownershipPointView taken = ownershipPointView w := by
    unfold taken DurableHolders.sendTaken ownershipPointView keyReferenceView keyAt ownershipAt peerAt packetKeyWords
    cases w.dev <;> rfl
  have peers : peerView taken = peerView w := by
    unfold taken DurableHolders.sendTaken peerView
    cases w.dev <;> rfl
  have keyAccount := account.points points
  have peerAccount := funded.take_send selected
  have active : ClearWork.Inv carriers ((holders.withoutSend rest).owners ++ o :: loans) taken :=
    ⟨peerAccount.carriers,stable.view (by
      unfold taken DurableHolders.sendTaken stableView RxRing.nativeCell rxView
      cases w.dev <;> rfl)⟩
  have protectedSlots : SlotPeerReferences (holders.withoutSend rest) loans taken :=
    anchors.transport peers points (List.Perm.refl _)
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨p,read,aRead,readRun,tail⟩ := tail
  obtain ⟨rfl,rfl,d,device,stored⟩ := getPeer_normal pid taken read p a aRead readRun
  cases flag : p.handshakePending with
  | false =>
    simp [flag,invariant,AmbientM.invariant,StateT.run_bind] at tail
    cases tail
  | true =>
    simp only [flag,Bool.not_true,Bool.false_eq_true,↓reduceIte] at tail
    simp only [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨saved,readDev,aDev,readDevRun,set,written,aWritten,setRun,start,started,aStarted,startRun,
      work,sent,aSent,workerRun,stop,stopped,aStopped,stopRun,finish⟩ := tail
    have eqDev : ((d,taken),aRead)=((saved,readDev),aDev) := by
      simpa [getDev,device] using readDevRun
    cases eqDev
    let updated := replacePeer taken d pid {p with handshakePending := d.sendWorkQueue.contains pid}
    have writeEq : (((),updated),aRead)=((set,written),aWritten) := by
      simpa [setPeer,modifyDev,device,updated,replacePeer] using setRun
    have writtenEq : written = updated := (congrArg (fun q => q.1.2) writeEq).symm
    have ambientEq : aWritten = aRead := (congrArg Prod.snd writeEq).symm
    subst written
    subst aWritten
    cases set
    have pending := (pinned_const _private.Leanux.Proofs.WG.Queues.SendDispatch.«0».Leanux.Proofs.WG.Queues.RxCredits.SendDispatch.pending_update)
      active device stored (d.sendWorkQueue.contains pid)
    have updatedPoints : ownershipPointView updated = ownershipPointView taken :=
      ownershipPoint_replace device stored rfl
    have updatedPeers : peerView updated = peerView taken := by
      unfold updated replacePeer peerView
      simp only [device,Option.map_some,Option.bind_some,Prod.mk.injEq,true_and]
      funext other
      by_cases same : pid = other
      · subst other; simp [stored]
      · simp [Std.TreeMap.getElem?_insert,same]
    have updatedSlots := protectedSlots.transport updatedPeers updatedPoints (List.Perm.refl _)
    have sameStart := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (fun g => g=updated))
      updated aRead start started aStarted rfl startRun
    subst started
    cases work
    have paid := (keyAccount.points updatedPoints).handshake_send_worker pending.1 pending.2 updatedSlots
      aStarted aSent (by simpa only [selected.slot] using workerRun)
    have sameStop := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (fun g => g=sent))
      sent aSent stop stopped aStopped rfl stopRun
    subst stopped
    cases finish
    exact paid

/-- Native recorded or legacy queue selection chooses the very durable
occurrence whose peer reference is paid. No key credit is inferred from its
peer count; the incoming exact key account is transported independently. -/
theorem HolderAccount.dispatched_send (account : HolderAccount temporary w.wg)
    (funded : holders.Funded carriers loans w.wg) (stable : StableRx carriers w.wg)
    (anchors : SlotPeerReferences holders loans w.wg)
    (run : Env.runOneSendWorker.run w = .ok ((),v)) : HolderAccount temporary v.wg := by
  obtain ⟨d,_,_,_,pid,beforeWorker,device,_,_,_,member,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((funded.aligned.send d device) ▸ member)
  exact account.flushed_send selected funded stable anchors beforeWorker v.ambient worker

end Leanux.Proofs.WG.RetirementSecurity
