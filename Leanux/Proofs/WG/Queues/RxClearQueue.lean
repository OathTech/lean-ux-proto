import Leanux.Proofs.WG.Queues.RxClearWork

/-! A clear-work reservation is obtained from the actual timer callback's
peerGet. A coalesced queue attempt returns that same reservation immediately;
an accepted attempt retains it with the appended work item. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ClearWork
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def queueView (w : WGWorld) := w.dev.map fun d => (d.ifindex,d.clearWorkQueue)

theorem acquire (hi : Inv cs loans w) (a b : Ambient)
    (hr : ((peerGet pid).run w).run a = .ok (((),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Inv cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,hd,hp,pos,handoff⟩ := peerGet_handoff a b hr
  have funded := (handoff.funded hi.1.inventory hi.1.queues
    (by simpa using hi.1.funded)).2.2
  have key := keyEffect_of_view (allowed := NoPromotion)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_keyView pid) w a () v b hr)
  refine ⟨d,p,hd,hp,pos,⟨inventory_view hi.1.inventory handoff.rx,
    queueOwners_base hi.1.queues handoff.base,?_,key.rxCompatible handoff.rx hi.1.keys.1,
    key.currentsCompatible hi.1.keys.2 (fun _ _ h => h.elim)⟩,?_⟩
  · intro o
    simpa [demand,HandoffDelta.owners,List.count_append,List.count_cons,Nat.add_comm] using funded o
  · exact hi.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (stable_peerGet pid) w a () v b hr)

theorem install (hi : Inv cs loans w) (pid : PeerId) :
    Inv cs loans {w with dev := w.dev.map fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}} := by
  refine ⟨hi.1.view ?_,hi.2.view ?_⟩
  · unfold carrierView keyView peerView rxView RxCredits.keyWords RxCredits.currentCells
    cases w.dev <;> rfl
  · unfold stableView RxRing.nativeCell rxView
    cases w.dev <;> rfl

/-- The accepted timer enqueue retains exactly its acquired reservation and
appends the corresponding work item. Coalescing repays it before returning. -/
theorem timer_normal (hi : Inv cs loans w) (a b : Ambient)
    (hr : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      Inv cs (added ++ loans) v ∧
      queueView v = (queueView w).map (fun q => (q.1,q.2 ++ added.map Owner.slot)) := by
  unfold expiredZeroKeyMaterial at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,ar,hread,alive,test,testedAmbient,hbranch,tail⟩ := hr
  obtain ⟨sameRead,sameAmbient,d,hd,hp⟩ := getPeer_normal pid w read p a ar hread
  subst read
  subst ar
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g = w) .zeroKeyAlive (!p.isDead))
    w a alive test testedAmbient rfl hbranch
  have sameTest := hb.2
  subst test
  cases alive with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    cases tail
    exact ⟨[],Or.inl rfl,hi,by simp⟩
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,got,ag,hget,device,readDev,ad,hdev,peek,peeked,ap,hpeek,
      pending,checked,ac,hpending,tail⟩ := tail
    cases u
    obtain ⟨dg,pg,hdg,hpg,pos,acquired⟩ := acquire hi testedAmbient ag hget
    have deq : dg = d := Option.some.inj (hdg.symm.trans hd)
    subst dg
    have peq : pg = p := Option.some.inj (hpg.symm.trans hp)
    subst pg
    obtain ⟨dd,pp,hdd,hpp,positive,effect⟩ := peerGet_loan pid w got testedAmbient ag hget
    have deq : dd = d := Option.some.inj (hdd.symm.trans hd)
    subst dd
    have peq : pp = p := Option.some.inj (hpp.symm.trans hp)
    subst pp
    have dev : got.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev effect
    have getter : ((getDev).run got).run ag =
      .ok (({d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}},got),ag) := by
      simp [getDev,dev]
    rw [hdev] at getter
    cases getter
    have hpw := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun g => g = got))
      got ag peek peeked ap rfl hpeek
    subst peeked
    have hcw := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g => g = got) .zeroKeyAlreadyQueued
        (d.clearWorkQueue.contains pid && !peek)) got ap pending checked ac rfl hpending
    have sameChecked := hcw.2
    subst checked
    cases pending with
    | true =>
      simp only [ite_true] at tail
      have kept := reservation_payment_stable acquired.1 acquired.2 ac b tail
      have paid := (hoare_iff_run_ambient _ _ _).mp
        (peerPut_nonfinal_spec pid (wgStoreView got) _ {p with refcount := p.refcount + 1}
          dev (by simp) (by simp; omega)) got ac () v b rfl tail
      have out := congrArg WGStoreView.dev paid
      change v.dev = _ at out
      dsimp only at out
      exact ⟨[],Or.inl rfl,kept,by simp [queueView,out,hd]⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨u,recorded,arecord,hrecord,hinstall⟩ := tail
      have same := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun g => g = got))
        got ac u recorded arecord rfl hrecord
      subst recorded
      cases hinstall
      refine ⟨[⟨d.ifindex,pid,p.internalId⟩],Or.inr ⟨d,p,hd,hp,rfl⟩,install acquired pid,?_⟩
      simp [queueView,dev,hd]

end Leanux.Proofs.WG.Queues.RxCredits.ClearWork
