import Leanux.Proofs.WG.RetirementSecurity.FinalDisposal

/-! The original TX worker removes a last-reference key after consuming its
actual first logical batch. The proof follows peek, readiness, queue removal,
optional completed-send effects and the literal final disposal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.FinalDisposal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem one_credit (account : Credits.Exact credits w)
    (one : credits.count allocation=1) :
    Credits.Exact (allocation::credits.erase allocation) w ∧ allocation∉credits.erase allocation :=
  ⟨account.perm (List.perm_cons_erase (List.count_pos_iff.mp (by omega))),
    List.count_eq_zero.mp (by rw [List.count_erase_self,one])⟩

theorem completion_references (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    SameView keyReferenceView (txCompletionSource pid items head) := by
  intro initial
  unfold txCompletionSource
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .txCrypted (head.state == .crypted)) _)
  intro yes
  split
  · exact ((createDataDone_ownership pid items).of_factor Prod.fst _ (fun _=>rfl)).wp (fun s=>s=initial)
  · exact preserves_pure ()

theorem tx_step (allocation : Credits.Allocation) (account : HolderAccount [] w)
    (projected : durableLoans w=some loans) (one : (loans.map (·.allocation)).count allocation=1)
    (pid : PeerId) (p : Peer) (items : List SkbId) (headId : SkbId) (head : DataPacket)
    (peer : peerAt w pid=some p) (queued : p.txQueue.all.head?=some items)
    (first : items.head?=some headId) (packet : Queues.TxDisposition.txPackets w headId=some head)
    (key : head.keypair=allocation.slot) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((true,v),b)) : keyAt v allocation.slot=none := by
  obtain ⟨all,named,credits⟩ := account
  have sameLoans : all=loans := Option.some.inj (named.symm.trans projected)
  subst all
  simp only [List.append_nil] at credits
  have total : HolderAccount [] w := ⟨loans,projected,by simpa only [List.append_nil] using credits⟩
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨chosen,u,c,peekRun,bodyRun⟩ := run
  obtain ⟨_,old,after,oldFound,_,selected,_,_⟩ := total.peek_tx pid a c peekRun
  have oldSame : old=p := Option.some.inj (oldFound.symm.trans peer)
  subst old
  rw [queued] at selected
  rw [selected] at bodyRun
  obtain ⟨d,q,queue,device,stored,_,_,changed⟩ := txPeek_effect pid a c peekRun
  have referencesU : keyReferenceView u=keyReferenceView w := by
    rw [changed]
    funext slot
    simp [keyReferenceView,keyAt,replacePeer,device]
  have packetU : Queues.TxDisposition.txPackets u headId=some head := by
    simpa [changed,Queues.TxDisposition.txPackets,replacePeer,device] using packet
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at bodyRun
  obtain ⟨ready,t,e,testRun,tail⟩ := bodyRun
  have sameT := (hoare_iff_run_ambient _ _ _).mp
    (ready_world_frame (some items) (fun z=>z=u)) u c ready t e rfl testRun
  subst t
  cases ready with
  | false=>simp only [Bool.not_false,ite_true] at tail; cases tail
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [txReadyTail_factor pid items headId first,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨read,t,f,readRun,tail⟩ := tail
    obtain ⟨sameT,sameF,ud,udFound,headFound⟩ := Packets.getTxSkb_current headId u t read e f readRun
    subst t
    subst f
    have readSame : read=head := by
      have actual : Queues.TxDisposition.txPackets u headId=some read := by
        simp [Queues.TxDisposition.txPackets,udFound,headFound]
      exact Option.some.inj (actual.symm.trans packetU)
    subst read
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨dropped,s,f,dropRun,tail⟩ := tail
    cases dropped
    obtain ⟨sd,sp,sDevice,_,_,changedS⟩ := txDrop_effect pid e f dropRun
    have referencesS : keyReferenceView s=keyReferenceView u := by
      rw [changedS]
      funext slot
      simp [keyReferenceView,keyAt,replacePeer,sDevice]
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨completed,t,g,completeRun,disposeRun⟩ := tail
    cases completed
    have referencesT := (ProjectedAction.iff_run_ambient _ _ _).mp
      (completion_references pid items head) s f () t g completeRun
    have paid := (credits.reference_view (referencesT.trans (referencesS.trans referencesU)))
    obtain ⟨lastAccount,last⟩ := one_credit paid one
    rw [key] at disposeRun
    exact (tx allocation _ lastAccount last pid items g b disposeRun).2

end Leanux.Proofs.WG.RetirementSecurity.FinalDisposal
