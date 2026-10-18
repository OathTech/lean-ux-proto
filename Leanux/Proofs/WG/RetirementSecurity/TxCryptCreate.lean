import Leanux.Proofs.WG.RetirementSecurity.TxCryptFrames

/-! Complete native createData preserves encryption-phase ownership across
peer refusal, ring refusal/publication and successful ring admission. Every
cleanup frees only its unpublished batch, apart from live/active aliases. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

def CreateCryptState (active : List (List SkbId)) (items : List SkbId) (ret : Int)
    (w : WGWorld) : Prop := TxCryptInventory active w ∧ (ret ≠ 0 → CryptOutside items active w)

theorem create_publish_crypt (state : CreateCryptState active items ret w) (a b : Ambient)
    (run : ((createPublishReturn items ret).run w).run a = .ok ((result,v),b)) :
    result = ret ∧ CreateCryptState active items ret v := by
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pipe,u,c,branchRun,tail⟩ := run
  have guarded := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateCryptState active items ret) .createDataEpipe (ret == -WG.EPIPE))
    w a pipe u c state branchRun
  cases pipe with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    cases tail
    exact ⟨rfl,guarded.2⟩
  | true =>
    have returned : ret = -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using guarded.1.symm
    have nonzero : ret ≠ 0 := by rw [returned]; decide
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,e,publishRun,done⟩ := tail
    cases done
    have outside := guarded.2.2 nonzero
    exact ⟨rfl,guarded.2.1.publish_outside outside .dead c b publishRun,
      fun _ => outside.ring ((ProjectedAction.iff_run_ambient _ _ _).mp
        (TxRing.enqueuePeer_frame items .dead) u c () v b publishRun)⟩

theorem create_return_crypt (crypt : TxCryptInventory active w)
    (owned : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w) (a b : Ambient)
    (run : ((createReturnSource pid items).run w).run a = .ok ((ret,v),b)) :
    CreateCryptState active items ret v := by
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,dead,t,e,branchRun,tail⟩ := run
  obtain ⟨same,clock,d,device,_⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same : t = w := by cases branchRun; rfl
  subst t
  cases dead with
  | true =>
    simp only [ite_true] at tail
    cases tail
    exact ⟨crypt,fun _ => crypt.local_outside owned⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,u,c,enqueueRun,publishRun⟩ := tail
    have next := crypt.enqueue owned device e c enqueueRun
    have separate : result ≠ 0 → CryptOutside items active u := by
      intro nonzero
      have ring := TxRing.enqueue_result pid items w u e c result enqueueRun
      rcases ring with ⟨zero,_⟩ | ⟨_,same⟩ | ⟨_,same,_⟩
      · exact (nonzero zero).elim
      · exact (crypt.local_outside owned).ring same
      · exact (crypt.local_outside owned).ring same
    obtain ⟨returned,last⟩ := create_publish_crypt ⟨next,separate⟩ c b publishRun
    exact returned ▸ last

theorem create_tail_crypt (state : CreateCryptState active items ret w) (pid : PeerId)
    (first : SkbId) (a b : Ambient)
    (run : ((TxDisposition.createTailSource pid items first ret).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  simp only [TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ok,u,c,branchRun,tail⟩ := run
  have guard := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateCryptState active items ret) .createDataOk (ret == 0))
    w a ok u c state branchRun
  cases ok with
  | true => simp only [ite_true] at tail; cases tail; exact guard.2.1
  | false =>
    have nonzero : ret ≠ 0 := by simpa using guard.1.symm
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨pipe,t,e,branchRun,tail⟩ := tail
    have same : t = u := by cases branchRun; rfl
    subst t
    cases pipe with
    | true => simp only [ite_true] at tail; cases tail; exact guard.2.1
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      exact guard.2.1.cleanup (guard.2.2 nonzero) pid first e b tail

/-- Full original creation preserves pending/active encryption exclusivity;
its refusal cleanup cannot remove a packet still available for encryption. -/
theorem TxCryptInventory.create (crypt : TxCryptInventory active w)
    (owned : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w) (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  have factor : createData pid items = (do
      let some first := items.head? | invariant "an empty ring item"
      let ret ← createReturnSource pid items
      TxDisposition.createTailSource pid items first ret) := by
    simp only [TxDisposition.createSource_factor,createReturnSource,createPublishReturn,
      bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,c,front,tail⟩ := run
    exact create_tail_crypt (create_return_crypt crypt owned a c front) pid first c b tail

end Leanux.Proofs.WG.RetirementSecurity
