import Leanux.Proofs.WG.RetirementSecurity.TxPublishHolders
import Leanux.Proofs.WG.RetirementSecurity.TxCleanupHolders

/-! Original createData either hands its saved key reference to the peer TX
queue or pays it in rejection cleanup. The intermediate predicate describes
the actual return code's source-local ownership, not a replacement schedule. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

def CreateHeld (allocation : Credits.Allocation) (temporary : Credits.Ledger)
    (pid : PeerId) (items : List SkbId) (ret : Int) (w : WGWorld) : Prop :=
  if ret = 0 ∨ ret = -EPIPE then HolderAccount temporary w
  else HolderAccount (allocation :: temporary) w ∧
    transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩ ∧
    TxDetached items w ∧ PeerReleaseReady pid w

theorem publish_return_holders (items : List SkbId) (ret : Int) (temporary : Credits.Ledger) :
    Hoare (createPublishReturn items ret) (HolderAccount temporary)
      (fun result w => result = ret ∧ HolderAccount temporary w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨epipe,u,c,guard,tail⟩ := run
  have hu := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (HolderAccount temporary) .createDataEpipe (ret == -EPIPE))
    w a epipe u c account guard).2
  cases epipe with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact ⟨rfl,hu⟩
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,d,publish,finish⟩ := tail
    have ht := hu.publish_tx items .dead c d publish
    cases finish
    exact ⟨rfl,ht⟩

theorem create_return_holders (allocation : Credits.Allocation) (temporary : Credits.Ledger)
    (pid : PeerId) (items : List SkbId) :
    Hoare (createReturnSource pid items)
      (fun w => HolderAccount (allocation :: temporary) w ∧
        transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩ ∧
        TxDetached items w ∧ PeerReleaseReady pid w)
      (CreateHeld allocation temporary pid items) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b state run
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,dead,t,d,guard,tail⟩ := run
  let P : WGWorld → Prop := fun s => HolderAccount (allocation :: temporary) s ∧
    transmitLoan s pid items = some ⟨.transmit pid items,allocation⟩ ∧
    TxDetached items s ∧ PeerReleaseReady pid s
  have hu := (hoare_iff_run_ambient _ _ _).mp (getPeer_preserves pid P) w a p u c state readRun
  have ht := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native P .createDataDead p.isDead) u c dead t d hu guard).2
  cases dead with
  | true =>
    simp only [ite_true] at tail
    cases tail
    simpa [CreateHeld,EINVAL,EPIPE] using ht
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ret,s,e,enqueueRun,publishRun⟩ := tail
    rcases ht.1.enqueue_detail ht.2.1 d e enqueueRun with refused | published
    · obtain ⟨rfl,account,same⟩ := refused
      have after : s = v := by
        simp [createPublishReturn,branch,AmbientM.branch,ENOSPC,WG.EPIPE] at publishRun
        exact publishRun.1.2
      have ret : result = -ENOSPC := by
        simp [createPublishReturn,branch,AmbientM.branch,ENOSPC,WG.EPIPE] at publishRun
        exact publishRun.1.1.symm
      subst v
      rw [ret]
      have peers : peersAt s = peersAt t := congrArg (fun shape => shape.2.1) same
      have batch : transmitLoan s pid items = some ⟨.transmit pid items,allocation⟩ :=
        ((loan_store same).2.1 pid items).trans ht.2.1
      simpa [CreateHeld,ENOSPC,EPIPE] using
        And.intro account (And.intro batch (And.intro (ht.2.2.1.peers peers) (ht.2.2.2.peers peers)))
    · obtain ⟨returned,account⟩ := published
      obtain ⟨same,after⟩ := (hoare_iff_run_ambient _ _ _).mp
        (publish_return_holders items ret temporary) s e result v b account publishRun
      rw [same]
      simpa only [CreateHeld,ite_eq_left returned] using after

theorem create_tail_holders (allocation : Credits.Allocation) (temporary : Credits.Ledger)
    (pid : PeerId) (items : List SkbId) (first : SkbId) (head : items.head? = some first)
    (ret : Int) :
    Hoare (Queues.TxDisposition.createTailSource pid items first ret)
      (CreateHeld allocation temporary pid items ret) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b state run
  simp only [Queues.TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ok,u,c,guard,tail⟩ := run
  have hu := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateHeld allocation temporary pid items ret)
      .createDataOk (ret == 0)) w a ok u c state guard
  cases ok with
  | true =>
    have zero : ret = 0 := by simpa using hu.1.symm
    simp only [ite_true] at tail
    cases tail
    simpa [CreateHeld,zero] using hu.2
  | false =>
    have nonzero : ret ≠ 0 := by simpa using hu.1.symm
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨epipe,t,d,guard,tail⟩ := tail
    have ht := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (CreateHeld allocation temporary pid items ret)
        .createDataOkEpipe (ret == -EPIPE)) u c epipe t d hu.2 guard
    cases epipe with
    | true =>
      have pipe : ret = -EPIPE := by simpa using ht.1.symm
      simp only [ite_true] at tail
      cases tail
      simpa [CreateHeld,pipe] using ht.2
    | false =>
      have nonpipe : ret ≠ -EPIPE := by simpa using ht.1.symm
      have saved : HolderAccount (allocation :: temporary) t ∧
          transmitLoan t pid items = some ⟨.transmit pid items,allocation⟩ ∧
          TxDetached items t ∧ PeerReleaseReady pid t := by
        simpa [CreateHeld,nonzero,nonpipe] using ht.2
      simp only [Bool.false_eq_true,ite_false] at tail
      cases result
      exact saved.1.cleanup_tx saved.2.1 head saved.2.2.1 saved.2.2.2 d b tail

theorem HolderAccount.create_tx (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩)
    (detached : TxDetached items w) (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  have factor : createData pid items = (do
      let some first := items.head? | invariant "an empty ring item"
      let ret ← createReturnSource pid items
      Queues.TxDisposition.createTailSource pid items first ret) := by
    simp only [Queues.TxDisposition.createSource_factor,createReturnSource,createPublishReturn,
      bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,c,front,tail⟩ := run
    have state := (hoare_iff_run_ambient _ _ _).mp
      (create_return_holders allocation temporary pid items) w a ret u c
      ⟨account,batch,detached,ready⟩ front
    exact (hoare_iff_run_ambient _ _ _).mp
      (create_tail_holders allocation temporary pid items first head ret) u c () v b state tail

end Leanux.Proofs.WG.RetirementSecurity
