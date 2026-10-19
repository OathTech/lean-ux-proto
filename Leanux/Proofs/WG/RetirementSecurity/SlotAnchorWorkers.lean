import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderHandshakePeerFrames

/-! Native send and zero-material callbacks retain independent slot anchors.
Queue selection pays a work reference; it does not consume a base/caller
anchor merely because the same peer number appears in both places. -/
namespace Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem index (action : IndexM α) :
    Preserves (SlotPeerReferences holders loans) (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table before device
  intro after pid p final stored slots
  cases final
  exact before d pid p device stored slots

theorem handshake_clear (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (handshakeClear pid) := by
  unfold handshakeClear
  apply preserves_bind (indexOwner_peerDeref_preserves _ _)
  intro _
  apply preserves_bind (index _)
  intro _
  change Preserves _ (updatePeer pid zeroedPeer)
  exact update pid zeroedPeer (fun _ => rfl) (fun _ h => h)

theorem initiation (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (sendHandshakeInitiation pid) :=
  frame (HolderHandshake.initiation_peers pid) (HolderHandshake.initiation_points pid)

theorem send_worker (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (initiation pid) (fun _ => peer_put (some pid))

theorem zero_worker (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshake_clear pid) (fun _ =>
    preserves_bind (clear pid) (fun _ => peer_put (some pid)))

theorem flushed_clear (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  apply preserves_bind (SlotAnchors.modify (holders := holders) (loans := loans)
    (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl) (fun _ => rfl))
  intro _
  apply preserves_bind (hoare_liftAmbient _ (SlotPeerReferences holders loans))
  intro _
  apply preserves_bind (zero_worker pid)
  intro _
  apply preserves_bind (hoare_liftAmbient _ (SlotPeerReferences holders loans))
  intro _
  exact preserves_pure ()

theorem flushed_send (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  apply preserves_bind (SlotAnchors.modify (holders := holders) (loans := loans)
    (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl) (fun _ => rfl))
  intro _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,tail⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  cases flag : p.handshakePending with
  | false =>
    simp [flag,invariant,AmbientM.invariant,StateT.run_bind] at tail
    cases tail
  | true =>
    simp only [flag,Bool.not_true,Bool.false_eq_true,↓reduceIte,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨saved,readDev,aDev,readDevRun,set,written,aWritten,setRun,start,started,aStarted,startRun,
      work,sent,aSent,workerRun,stop,stopped,aStopped,stopRun,finish⟩ := tail
    have eqDev : ((d,w),a)=((saved,readDev),aDev) := by
      simpa [getDev,device] using readDevRun
    cases eqDev
    let updated := replacePeer w d pid {p with handshakePending := d.sendWorkQueue.contains pid}
    have writeEq : (((),updated),a)=((set,written),aWritten) := by
      simpa [setPeer,modifyDev,device,updated,replacePeer] using setRun
    have writtenEq : written = updated := (congrArg (fun q => q.1.2) writeEq).symm
    have ambientEq : aWritten = a := (congrArg Prod.snd writeEq).symm
    subst written
    subst aWritten
    cases set
    have updatedSlots : SlotPeerReferences holders loans updated :=
      before.replace device stored rfl (fun h => h)
    have sameStart := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (fun g => g=updated))
      updated a start started aStarted rfl startRun
    subst started
    have paid := (hoare_iff_run_ambient _ _ _).mp (send_worker pid)
      updated aStarted work sent aSent updatedSlots workerRun
    have sameStop := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (fun g => g=sent))
      sent aSent stop stopped aStopped rfl stopRun
    subst stopped
    cases finish
    exact paid

theorem del_timer (pid : PeerId) (timer : PeerTimer) :
    Preserves (SlotPeerReferences holders loans) (delTimer pid timer) :=
  frame (HolderConsume.control_peers (delTimer_control pid timer)) (delTimer_ownership pid timer)

end Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
