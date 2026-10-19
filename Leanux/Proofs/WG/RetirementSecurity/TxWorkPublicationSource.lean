import Leanux.Proofs.WG.RetirementSecurity.TxWorkAdmissionCoverage

/-! Publication's actual queue-membership guard identifies the scheduled
peer, and its work update retains every previously pending actor. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem cpu_work (pid : PeerId) : SameView queued (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold cpumaskChooseOnline
  simp only [branch,Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range',
    show (Std.Legacy.Range.mk 0 0 1 (by decide)).size=0 from rfl,
    List.range'_zero,List.forIn_nil]
  repeat' tx_work_step initial

theorem schedule_keeps (pid : PeerId) (a b : Ambient)
    (run : ((schedule pid).run w).run a=.ok (((),v),b)) : queued w ⊆ queued v := by
  intro q member
  have preserve : Preserves (fun w=>q∈queued w) (schedule pid) := by
    unfold schedule
    simp only [peekQueuedUnit,recordQueued]
    repeat' first
      | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (fun work=>q∈work))
      | (rx_retention_head modifyDev
         apply hoare_modify
         intro w before
         cases device:w.dev with
         | none=>simp [queued,device] at before
         | some d=>
           have prior:q∈d.txWorkQueue := by simpa [queued,device] using before
           simpa [queued,device] using List.mem_append_left [pid] prior)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  exact (hoare_iff_run_ambient _ _ _).mp preserve w a () v b member run

theorem middle_keeps (pid : PeerId) (first : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((TxDisposition.publicationMiddle pid first state).run w).run a=.ok (((),v),b)) :
    queued w ⊆ queued v := by
  rw [middle_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,rest⟩:=run
  obtain ⟨same,clock,_,_,_⟩:=Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  split at rest
  · simp only [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨_,_,_,stopped,_⟩:=rest
    cases stopped
  · simp only [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨_,t,e,marked,_,s,f,cpu,tail⟩:=rest
    have markedWork:queued t=queued w := (ProjectedAction.iff_run_ambient _ _ _).mp
      (set_packet_work first (fun p=>{p with state})) w a () t e marked
    have cpuWork:queued s=queued t := (ProjectedAction.iff_run_ambient _ _ _).mp
      (cpu_work pid) t e _ s f cpu
    simpa only [cpuWork,markedWork] using schedule_keeps pid f b tail

theorem publication_keeps (items : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b)) : queued w ⊆ queued v := by
  rw [TxDisposition.publication_factor] at run
  cases head:items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨packet,u,c,readRun,pid,t,e,ownerRun,_,s,f,getRun,_,x,g,middle,put⟩:=run
    have readWorld:u=w := (Packets.getTxSkb_current first w u packet a c readRun).1
    have ownerWorld:t=u := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerDeref_preserves _ (fun t=>t=u)) u c pid t e rfl ownerRun
    have getWork:queued s=queued t := (ProjectedAction.iff_run_ambient _ _ _).mp
      (peer_get pid) t e () s f getRun
    have putWork:queued v=queued x := (ProjectedAction.iff_run_ambient _ _ _).mp
      (peer_put (some pid)) x g () v b put
    simpa only [putWork,getWork,ownerWorld,readWorld] using middle_keeps pid first state f g middle

theorem publication_selected (items : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b)) :
    ∃first pid p batch,items.head?=some first ∧ peerAt w pid=some p ∧
      batch∈p.txQueue.all ∧ batch.head?=some first ∧ pid∈queued v := by
  rw [TxDisposition.publication_factor] at run
  cases head:items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨packet,u,c,readRun,pid,t,e,ownerRun,_,s,f,getRun,_,x,g,middle,put⟩:=run
    obtain ⟨same,clock,_,_,_⟩:=Packets.getTxSkb_current first w u packet a c readRun
    subst u
    subst c
    have ownerWorld:t=w := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerDeref_preserves _ (fun t=>t=w)) w a pid t e rfl ownerRun
    subst t
    have queues:TxDisposition.txQueues s=TxDisposition.txQueues w :=
      ((hoare_iff_run_ambient _ _ _).mp (TxDisposition.strict_acquire_queues pid
        (TxDisposition.txQueues w)) w e () s f rfl getRun).1
    have pending:=middle_member pid first state f g middle
    have work:queued v=queued x := (ProjectedAction.iff_run_ambient _ _ _).mp
      (peer_put (some pid)) x g () v b put
    rw [middle_factor,MaterialOrigin.bind_ok_ambient] at middle
    obtain ⟨p,u,c,read,tail⟩:=middle
    obtain ⟨_,_,d,device,stored⟩:=Origins.getPeer_return pid s u p f c read
    have atStart:peerAt s pid=some p := by simp [peerAt,device,stored]
    have original:TxDisposition.txQueues w pid=some p.txQueue := by
      rw [←queues]
      simpa only [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,peerAt,atStart,
        Option.map_some] using congrArg (Option.map (·.txQueue)) atStart
    obtain ⟨old,oldFound,oldQueue⟩:=Option.map_eq_some_iff.mp original
    split at tail
    · simp only [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,_,_,stopped,_⟩:=tail
      cases stopped
    · rename_i guard
      have any:p.txQueue.all.any (·.head? == some first)=true := by
        cases test:p.txQueue.all.any (·.head? == some first) <;> simp_all
      obtain ⟨batch,member,selected⟩:=List.any_eq_true.mp any
      refine ⟨first,pid,old,batch,rfl,oldFound,?_,?_,work.symm ▸ pending⟩
      · simpa only [oldQueue] using member
      · exact beq_iff_eq.mp selected

end Leanux.Proofs.WG.RetirementSecurity.TxWork
