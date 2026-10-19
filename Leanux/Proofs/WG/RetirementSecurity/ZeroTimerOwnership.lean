import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledDeferred

/-! The actual zero-material timer borrows only a peer reference. Refused
work repays that very acquisition, so neither arm changes any key holder.
The later clear worker, not this timer callback, pays published key slots. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem zero_timer_ownership (pid : PeerId) : SameView ownershipPointView (expiredZeroKeyMaterial pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  unfold expiredZeroKeyMaterial at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,alive,test,aTest,guard,tail⟩ := run
  obtain ⟨sameRead,sameAmbient,d,device,stored⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  have same := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g=>g=w) .zeroKeyAlive (!p.isDead))
    w a alive test aTest rfl guard
  have sameTest := same.2
  subst test
  cases alive with
  | false=>simp only [Bool.false_eq_true,ite_false] at tail; cases tail; rfl
  | true=>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,got,ag,acquire,dev,readDev,ad,getter,peek,peeked,ap,peeking,
      pending,checked,ac,guard,tail⟩ := tail
    cases u
    have borrowed := (hoare_iff_run_ambient _ _ _).mp
      (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w aTest () got ag rfl acquire
    have points := (ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_ownership pid) w aTest () got ag acquire
    have same := (DecryptCarrier.getDev_current ag ad getter).1
    subst readDev
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun g=>g=got))
      got ad peek peeked ap rfl peeking
    subst peeked
    have same := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g=>g=got) .zeroKeyAlreadyQueued
        (dev.clearWorkQueue.contains pid && !peek)) got ap pending checked ac rfl guard
    have sameWorld := same.2
    subst checked
    cases pending with
    | true=>
      simp only [ite_true] at tail
      have restored := (hoare_iff_run_ambient _ _ _).mp
        (PeerBorrow.repay_spec (some pid) (wgStoreView w)) got ac () v b borrowed tail
      exact ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames.«0».Leanux.Proofs.WG.RetirementSecurity.ownership_borrow_factor) v).symm.trans
        ((congrArg (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames.«0».Leanux.Proofs.WG.RetirementSecurity.ownershipFromBorrow) restored).trans
          ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames.«0».Leanux.Proofs.WG.RetirementSecurity.ownership_borrow_factor) w))
    | false=>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨u,recorded,ar,record,install⟩ := tail
      have same := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun g=>g=got))
        got ac u recorded ar rfl record
      subst recorded
      have final := (ProjectedAction.iff_run_ambient _ _ _).mp
        (ownership_modifyDev (fun e=>{e with clearWorkQueue:=e.clearWorkQueue++[pid]})
          (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) got ar () v b install
      exact final.trans points

end Leanux.Proofs.WG.RetirementSecurity
