import Leanux.Proofs.WG.KeyTimes.ZeroTimer
import Leanux.Proofs.WG.RetirementSecurity.InitializedRetirement

/-! The actual zero-key timer callback guarantees queued clear work for a
live peer. Coalescing already-pending work repays only the extra peer borrow;
it does not remove the existing queued occurrence. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ZeroTimerQueued
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem callback (pid : PeerId) (p : Peer) (alive : p.isDead=false)
    (found : peerAt w pid=some p) (a b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w).run a=.ok (((),v),b)) :
    ∃d,v.dev=some d ∧ pid∈d.clearWorkQueue := by
  unfold expiredZeroKeyMaterial at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨read,u,c,readRun,yes,t,e,aliveRun,tail⟩ := run
  obtain ⟨sameU,sameC,d,device,stored⟩ := Origins.getPeer_return pid w u read a c readRun
  subst u
  subst c
  have samePeer : read=p := Option.some.inj ((show peerAt w pid=some read from by
    simp [peerAt,device,stored]).symm.trans found)
  subst read
  have positive : yes=true ∧ t=w := by
    rw [alive] at aliveRun
    cases aliveRun
    exact ⟨rfl,rfl⟩
  obtain ⟨rfl,sameT⟩ := positive
  subst t
  simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨got,u,c,getRun,readDev,t,f,deviceRun,peek,s,g,peekRun,pending,z,i,pendingRun,tail⟩ := tail
  cases got
  obtain ⟨dg,pg,dgFound,pgFound,pos,effect⟩ := peerGet_loan pid w u e c getRun
  have sameD : dg=d := Option.some.inj (dgFound.symm.trans device)
  subst dg
  have sameP : pg=p := Option.some.inj (pgFound.symm.trans stored)
  subst pg
  have dev : u.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} :=
    congrArg WGStoreView.dev effect
  have getter : ((getDev).run u).run c=
      .ok (({d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}},u),c) := by
    simp [getDev,dev]
  rw [deviceRun] at getter
  cases getter
  have sameS := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun z=>z=u))
    u c peek s g rfl peekRun
  subst s
  have branch := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun z=>z=u) .zeroKeyAlreadyQueued
      (d.clearWorkQueue.contains pid && !peek)) u g pending z i rfl pendingRun
  have sameZ := branch.2
  subst z
  cases pending with
  | true=>
    simp only [ite_true] at tail
    have member : pid∈d.clearWorkQueue := by
      have selected := branch.1
      simp only [Bool.true_eq, Bool.and_eq_true] at selected
      exact List.contains_iff_mem.mp selected.1
    have paid := (hoare_iff_run_ambient _ _ _).mp
      (peerPut_nonfinal_spec pid (wgStoreView u) _ {p with refcount:=p.refcount+1}
        dev (by simp) (by simp; omega)) u i () v b rfl tail
    have finalDev := congrArg WGStoreView.dev paid
    change v.dev=_ at finalDev
    exact ⟨_,finalDev,member⟩
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨recorded,t,j,recordRun,install⟩ := tail
    have sameT := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun z=>z=u))
      u i recorded t j rfl recordRun
    subst t
    cases install
    refine ⟨{d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}, clearWorkQueue:=d.clearWorkQueue++[pid]},?_,by simp⟩
    simp [dev]


/-- The initialized key account continues through the actual timer callback.
The callback leaves key material intact and establishes a real queued unit. -/
theorem initialized_callback (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (pid : PeerId) (p : Peer) (alive : p.isDead=false)
    (found : peerAt w.wg pid=some p) (b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w.wg).run w.ambient=.ok (((),v),b)) :
    HolderAccount [] v ∧ KeyTimes.keypairStore v=KeyTimes.keypairStore w.wg ∧
      ∃d,v.dev=some d ∧ pid∈d.clearWorkQueue := by
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp (zero_timer_ownership pid)
    w.wg w.ambient () v b run
  exact ⟨(HolderInitialized.account trace placeholders initialized).points points,
    (ProjectedAction.iff_run_ambient _ _ _).mp (KeyTimes.expiredZeroKeyMaterial_store pid)
      w.wg w.ambient () v b run,
    callback pid p alive found w.ambient b run⟩

/-- Clock/record progress is represented by execution of the actual callback;
worker progress by execution of that peer's original flushed clear work.
Neither condition is inferred from elapsed wall-clock time or queue membership. -/
theorem initialized_callback_then_worker (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (pid : PeerId) (p : Peer) (alive : p.isDead=false)
    (found : peerAt w.wg pid=some p) (b c : Ambient)
    (fired : ((expiredZeroKeyMaterial pid).run w.wg).run w.ambient=.ok (((),u),b))
    (dispatched : ((runFlushedClearWork pid).run u).run b=.ok (((),v),c)) :
    (∃d,u.dev=some d ∧ pid∈d.clearWorkQueue) ∧ HolderAccount [] v ∧
      SlotsCleared pid v ∧ Retains u v := by
  obtain ⟨keys,_,queued⟩ := initialized_callback trace placeholders initialized pid p alive found b fired
  exact ⟨queued,(hoare_iff_run_ambient _ _ _).mp (flushed_holders pid []) u b () v c keys dispatched,
    flushed_retirement pid u v b c dispatched⟩

end Leanux.Proofs.WG.RetirementSecurity.ZeroTimerQueued
