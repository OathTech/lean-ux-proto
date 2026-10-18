import Leanux.Proofs.WG.RetirementSecurity.HolderStoreFrames
import Leanux.Proofs.WG.Queues.TxRxProtection

/-! Full original TX enqueue: the peer-queue admission consumes one saved
key reference even when the device ring subsequently refuses the batch. A
peer-queue refusal leaves that same reference for createData's cleanup. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

theorem enqueue_tail_holders (item : List SkbId) (temporary : Credits.Ledger) :
    Hoare (enqueueTailItem item) (HolderAccount temporary)
      (fun ret w => (ret = 0 ∨ ret = -EPIPE) ∧ HolderAccount temporary w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a ret v b account run
  simp only [enqueueTailItem,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,aa,readRun,cpu,t,ab,cpuRun,result,s,ac,setRun,full,e,ae,branchRun,tail⟩ := run
  have hu := account.store ((ProjectedAction.iff_run_ambient _ _ _).mp
    (holderStore_kernel _ getDev_sameWGStore) w a d u aa readRun)
  have ht := hu.store ((ProjectedAction.iff_run_ambient _ _ _).mp
    (holderStore_kernel _ (cpumaskNextOnlineFrom_sameStore d.encryptLastCpu)) u aa cpu t ab cpuRun)
  have hs := ht.store ((ProjectedAction.iff_run_ambient _ _ _).mp
    (modifyDev_holderStore (fun d => {d with encryptLastCpu := cpu})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    t ab result s ac setRun)
  have he := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (HolderAccount temporary) .enqueueRingFull d.encryptQueue.full)
    s ac full e ae hs branchRun).2
  cases full with
  | true =>
    simp only [ite_true] at tail
    cases tail
    exact ⟨Or.inr rfl,he⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,f,af,queueRun,result,g,ag,produceRun,tail⟩ := tail
    have hf := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) (HolderAccount temporary))
      e ae result f af he queueRun
    have hg := hf.store ((ProjectedAction.iff_run_ambient _ _ _).mp
      (modifyDev_holderStore (fun d => {d with encryptQueue := d.encryptQueue.produce item})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
      f af result g ag produceRun)
    cases tail
    exact ⟨Or.inl rfl,hg⟩

theorem HolderAccount.enqueue_detail (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid item).run w).run a = .ok ((ret,v),b)) :
    (ret = -ENOSPC ∧ HolderAccount (allocation :: temporary) v ∧ holderStore v = holderStore w) ∨
      ((ret = 0 ∨ ret = -EPIPE) ∧ HolderAccount temporary v) := by
  rw [enqueue_factor] at run
  cases head : item.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨result,u,aa,setRun,p,t,ab,readRun,full,e,ae,branchRun,tail⟩ := run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (setTx_holderStore first (fun p => {p with state := .uncrypted}) (fun _ => rfl))
      w a result u aa setRun
    have hu := account.store same
    have batchU : transmitLoan u pid item = some ⟨.transmit pid item,allocation⟩ :=
      (loan_store same).2.1 pid item |>.trans batch
    obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid u t p aa ab readRun
    subst t
    subst ab
    have found : peerAt u pid = some p := by simp [peerAt,device,stored]
    have he := ((hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun s => HolderAccount (allocation :: temporary) s ∧
        peerAt s pid = some p ∧ transmitLoan s pid item = some ⟨.transmit pid item,allocation⟩ ∧
        holderStore s = holderStore w)
        .enqueuePeerQueueFull (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS)))
      u aa full e ae ⟨hu,found,batchU,same⟩ branchRun).2
    cases full with
    | true =>
      simp only [ite_true] at tail
      cases tail
      exact Or.inl ⟨rfl,he.1,he.2.2.2⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨result,f,af,installRun,tailRun⟩ := tail
      cases result
      have hf := he.1.enqueue_tx he.2.1 he.2.2.1 ae af installRun
      exact Or.inr ((hoare_iff_run_ambient _ _ _).mp
        (enqueue_tail_holders item temporary) f af ret v b hf tailRun)

theorem HolderAccount.enqueue (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid item).run w).run a = .ok ((ret,v),b)) :
    (ret = -ENOSPC ∧ HolderAccount (allocation :: temporary) v) ∨
      ((ret = 0 ∨ ret = -EPIPE) ∧ HolderAccount temporary v) := by
  rcases account.enqueue_detail batch a b run with refused | published
  · exact Or.inl ⟨refused.1,refused.2.1⟩
  · exact Or.inr published

end Leanux.Proofs.WG.RetirementSecurity
