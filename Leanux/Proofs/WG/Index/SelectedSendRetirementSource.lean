import Leanux.Proofs.WG.Index.SelectedSendRetirementEffects
import Leanux.Proofs.WG.Index.SelectedSendRetirementFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The original initiation retains its whole funded account by the landed
carrier and holder contracts. No account traversal is reimplemented here. -/
theorem sendInitiation_funded_cut
    (holders : DurableHolders) (cs : Ledger) (loans : Reservations) (pid : PeerId)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w) (stable : StableRx cs w)
    (run : ((sendHandshakeInitiation pid).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v ∧
      ConfiguredIdentity.Inv v ∧ BaseCoherence.Inv v := by
  have credit := (hoare_iff_run_ambient _ _ _).mp (SendWork.initiation_preserves pid)
    w a () v b ⟨funded.carriers,stable⟩ run
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (HolderWorkFrames.sendHandshakeInitiation_frame pid w)
    w a () v b (Frame.refl w) run
  refine ⟨⟨funded.aligned.frame frame,credit.1⟩,credit.2,?_,?_⟩
  · exact (hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame (ConfiguredHandshake.sendHandshakeInitiation_view pid))
      w a () v b configured run
  · exact BaseCoherence.transport base
      ((ProjectedAction.iff_run_ambient _ _ _).mp
        (BaseCoherence.sendHandshakeInitiation_view pid) w a () v b run)

/-- The worker's actual final-put entry is still funded by its selected
stamped loan. Residency, stamp agreement and positive refcount are derived. -/
theorem queued_send_beforePayment
    (holders : DurableHolders) (cs : Ledger) (paid : Owner) (loans : Reservations)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (paid :: loans) w) (stable : StableRx cs w)
    (run : ((handshakeSendWorker paid.slot).run w).run a = .ok (((),v),b)) :
    ∃ sent c d p,
      ((sendHandshakeInitiation paid.slot).run w).run a = .ok (((),sent),c) ∧
      ((peerPut (some paid.slot)).run sent).run c = .ok (((),v),b) ∧
      holders.Funded cs (paid :: loans) sent ∧ StableRx cs sent ∧
      ConfiguredIdentity.Inv sent ∧ BaseCoherence.Inv sent ∧
      sent.dev = some d ∧ d.peers[paid.slot]? = some p ∧
      paid = ⟨d.ifindex,paid.slot,p.internalId⟩ ∧ 0 < p.refcount := by
  unfold handshakeSendWorker at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,sent,c,send,payment⟩ := run
  cases u
  obtain ⟨credit,stillStable,cfg,coh⟩ := sendInitiation_funded_cut
    holders cs (paid :: loans) paid.slot w sent a c configured base funded stable send
  have charged : 0 < demand cs (holders.owners ++ (paid :: loans)) paid := by
    simp only [demand,List.count_append,List.count_cons_self]
    omega
  obtain ⟨p,found,bound⟩ := protected_resident credit.carriers.funded charged
  obtain ⟨d,device,epoch,resident,stamp⟩ := resident_fields found
  have paidAt : paid = ⟨d.ifindex,paid.slot,p.internalId⟩ := by
    cases paid
    simp only [Owner.mk.injEq]
    exact ⟨epoch.symm,True.intro,stamp.symm⟩
  exact ⟨sent,c,d,p,send,payment,credit,stillStable,cfg,coh,device,resident,paidAt,by omega⟩

/-- Complete actual worker, conditional only on the named initiation-index
leaf. Its final release is discharged from selected funding and retirement;
the endpoint account is the landed original worker account theorem. -/
theorem queued_send_retirement
    (holders : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations)
    (initiation : InitiationIndexContract holders cs paid retired loans)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (paid :: (retired ++ loans)) w) (stable : StableRx cs w)
    (safe : SendIndexSafe retired w)
    (run : ((handshakeSendWorker paid.slot).run w).run a = .ok (((),v),b)) :
    holders.Funded cs (retired ++ loans) v ∧ StableRx cs v ∧
      ConfiguredIdentity.Inv v ∧ BaseCoherence.Inv v ∧ SendIndexSafe retired v := by
  obtain ⟨sent,c,d,p,send,payment,credit,stillStable,cfg,coh,device,resident,paidAt,positive⟩ :=
    queued_send_beforePayment holders cs paid (retired ++ loans)
      w v a b configured base funded stable run
  have index := initiation w a () sent c ⟨configured,base,funded,stable,safe⟩ send
  have actualCredit : holders.Funded cs
      (⟨d.ifindex,paid.slot,p.internalId⟩ :: (retired ++ loans)) sent := by
    rw [← paidAt]
    exact credit
  have roots : DeadHashedReserved (retired ++ loans) d := by
    intro entry member kid key pid peer owner keyFound keyPeer peerFound dead
    exact List.mem_append.mpr (Or.inl
      (index.2.2 d device entry member kid key pid peer owner keyFound keyPeer peerFound dead))
  obtain ⟨present,covered,coherent⟩ := peerPut_funded_hashSlots
    sent v c b () cfg coh actualCredit device resident (index.2.1 d device)
      (index.1 d device) roots payment
  obtain ⟨paidCredit,paidStable⟩ := queued_send_funded funded stable a b run
  refine ⟨paidCredit,paidStable,?_,?_,?_,?_,?_⟩
  · exact (hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerPut_preserves (some paid.slot))
      sent c () v b cfg payment
  · exact BaseCoherence.transport coh
      ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view (some paid.slot))
        sent c () v b payment)
  · intro actual found
    rw [present] at found
    cases found
    exact covered
  · intro actual found
    rw [present] at found
    cases found
    exact coherent
  · exact peerPut_retirement retired paid.slot d p resident positive
      sent c () v b ⟨device,index.2.2⟩ payment

/-- A normal preparation supplies its real resident pending peer. All
missing-device, missing-peer and false-pending refusals remain in the source. -/
theorem flushedSendPrepare_normal (pid : PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Unit)
    (run : ((flushedSendPrepare pid).run w).run a = .ok ((result,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ p.handshakePending = true ∧
      v = {w with dev := some (sendPreparedDevice d pid p)} ∧ b = a := by
  cases device : w.dev with
  | none =>
    simp [flushedSendPrepare,modifyDev,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases pendingFlag : p.handshakePending with
      | false =>
        simp [flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,pendingFlag,
          invariant,AmbientM.invariant] at run
        cases run
      | true =>
        simp [flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,pendingFlag,setPeer] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        exact ⟨d,p,rfl,resident,pendingFlag,rfl,rfl⟩

/-- Complete original flushed send, including dequeue, pending guard and
both recorded section boundaries. A selected occurrence funds the actual
worker; only the named original-initiation index leaf remains explicit. -/
theorem flushed_send_retirement
    (holders : DurableHolders) (cs : Ledger) (pid : PeerId) (paid : Owner)
    (rest retired loans : Reservations)
    (selected : WorkReservations.Selected holders.send pid paid rest)
    (initiation : InitiationIndexContract (holders.withoutSend rest) cs paid retired loans)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (safe : SendIndexSafe retired w)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    (holders.withoutSend rest).Funded cs (retired ++ loans) v ∧ StableRx cs v ∧
      ConfiguredIdentity.Inv v ∧ BaseCoherence.Inv v ∧ SendIndexSafe retired v := by
  rw [runFlushedSendWork_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,prepared,c,prepare,start,started,e,startRun,
    worker,sent,f,workerRun,stop,stopped,h,stopRun,finish⟩ := run
  obtain ⟨d,p,device,resident,_,preparedEq,_⟩ :=
    flushedSendPrepare_normal pid w prepared a c u prepare
  have prepCredit : (holders.withoutSend rest).Funded cs
      (paid :: (retired ++ loans)) prepared ∧ StableRx cs prepared := by
    rw [preparedEq]
    exact sendPrepared_funded holders cs (retired ++ loans) pid paid rest
      selected w d p device resident funded stable
  have prepIndex : ConfiguredIdentity.Inv prepared ∧ BaseCoherence.Inv prepared ∧
      SendIndexSafe retired prepared := by
    rw [preparedEq]
    exact sendPrepared_index retired pid w d p device resident configured base safe
  have sameStart := (SelectedDrain.ambient_cut
    (AmbientM.hidden (.sectionStart .sendWorker)) prepared started c e start startRun).1
  subst started
  have sameStop := (SelectedDrain.ambient_cut
    (AmbientM.hidden (.sectionStop .sendWorker)) sent stopped f h stop stopRun).1
  subst stopped
  have final : sent = v ∧ h = b := by simpa using finish
  rw [← final.1]
  cases worker
  apply queued_send_retirement (holders.withoutSend rest) cs paid retired loans
    initiation prepared sent e f prepIndex.1 prepIndex.2.1 prepCredit.1 prepCredit.2 prepIndex.2.2
  simpa only [selected.slot] using workerRun

end Leanux.Proofs.WG.Index
