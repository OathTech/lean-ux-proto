import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceAllocation

/-! Native peer-queue enqueue consumes the unpublished occurrence on both
normal ring admission and EPIPE. ENOSPC keeps it in the caller's local list.
The device ring changes no ownership multiplicity. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem enqueue_tail_ownership (items : List SkbId) :
    SameView ownershipPointView (Queues.RxCredits.enqueueTailItem items) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold Queues.RxCredits.enqueueTailItem
  simp only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom
       exact (ownershipPoints_kernel _ (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | ownership_source_step initial

theorem enqueue_tail_result (items : List SkbId) (a b : Ambient)
    (run : ((Queues.RxCredits.enqueueTailItem items).run w).run a = .ok ((ret,v),b)) :
    ret = 0 ∨ ret = -Leanux.EPIPE := by
  simp only [Queues.RxCredits.enqueueTailItem,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,full,_,_,_,tail⟩ := run
  cases full with
  | true => simp only [ite_true] at tail; cases tail; exact Or.inr rfl
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,_,_,_,_,_,_,_,done⟩ := tail
    cases done
    exact Or.inl rfl

theorem TxInventory.enqueue_native
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    (ret = -Leanux.ENOSPC ∧ TxInventory (⟨.unpublished,pid,items⟩ :: locals) v) ∨
      ((ret = 0 ∨ ret = -Leanux.EPIPE) ∧ TxInventory locals v) := by
  rw [Queues.RxCredits.enqueue_factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,markRun,p,t,e,peerRun,full,s,f,branchRun,tail⟩ := run
    have marked := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _
        (setTx_holderStore first (fun p => {p with state := .uncrypted}) (fun _ => rfl)))
      w a () u c markRun
    have hu := inventory.points marked
    obtain ⟨same,_,d,device,found⟩ := Origins.getPeer_return pid u t p c e peerRun
    subst t
    have same : s = u := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull
        (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS))) (fun s => s = u))
      u e full s f rfl branchRun
    subst s
    cases full with
    | true =>
      simp only [ite_true] at tail
      cases tail
      exact Or.inl ⟨rfl,hu⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,s,g,installRun,tailRun⟩ := tail
      have installed : replacePeer u d pid {p with txQueue := p.txQueue.enqueue items} = s ∧ f = g := by
        simpa [setPeer,modifyDev,replacePeer,device] using installRun
      have hs : TxInventory locals s := installed.1 ▸ hu.enqueue device found
      exact Or.inr ⟨enqueue_tail_result items g b tailRun,
        hs.points ((ProjectedAction.iff_run_ambient _ _ _).mp (enqueue_tail_ownership items)
          s g ret v b tailRun)⟩

end Leanux.Proofs.WG.RetirementSecurity
