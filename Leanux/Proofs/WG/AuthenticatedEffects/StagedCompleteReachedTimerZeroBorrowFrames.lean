import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointZero
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingQueueRepaymentFrames

/-! A zero-key timer can enter raw repayment only after its own successful
borrow and duplicate-work test. That source fact excludes final peer erasure;
it is derived from the prefix, not assumed of every raw peerPut call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity CausalJournal
set_option maxHeartbeats 600000

theorem before_repay_funded
    (performed : ((beforeRepay pid).run w).run a=.ok ((true,v),b)) : Queued.Funded pid v := by
  unfold beforeRepay at performed
  simp only [MaterialOrigin.bind_ok_ambient] at performed
  obtain ⟨peer,u,c,_,alive,t,d,_,tail⟩:=performed
  cases alive with
  | false=>cases tail
  | true=>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,got,ag,borrow,device,readDev,ad,deviceRead,peek,peeked,ap,peekRead,
      pending,checked,ac,test,tail⟩:=tail
    cases ignored
    have funded:=Queued.acquired pid d ag borrow
    have sameRead : readDev=got := by
      cases found : got.dev with
      | none=>simp [getDev,found,invariant,AmbientM.invariant] at deviceRead;cases deviceRead
      | some device=>
        simp [getDev,found] at deviceRead
        exact deviceRead.1.2.symm
    subst readDev
    have samePeek : peeked=got := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun world=>world=got))
      got ad peek peeked ap rfl peekRead
    subst peeked
    have sameTest : checked=got := by cases test; rfl
    subst checked
    cases pending with
    | true=>cases tail;exact funded
    | false=>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,_,_,_,_,_,_,_,bad⟩:=tail
      cases bad

theorem repayment_funded
    (leading : runPrefix (wg (beforeRepay pid)) w h=(.ok (true,u),middle)) :
    Queued.Funded pid u.wg := by
  rw [liftWGObserver_run,runWGPrefix_lift] at leading
  cases native : ((beforeRepay pid).run w.wg).run w.ambient with
  | error stop=>rw [native] at leading;cases leading
  | ok result=>
    obtain ⟨⟨value,v⟩,b⟩:=result
    rw [native] at leading
    cases leading
    exact before_repay_funded native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
