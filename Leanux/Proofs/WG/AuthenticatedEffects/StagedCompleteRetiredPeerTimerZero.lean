import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWork
import Leanux.Proofs.WG.Queues.HolderTimers

/-! The zero-material timer retains the exact added clear-work occurrence
in both bounds of one account. Coalescing pays the acquired loan in source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders HolderTimers

namespace TimerFrames

theorem zero_source (hi : ClearWork.Inv cs loans w) (upper : Upper {} cs loans w) (a b : Ambient)
    (hr : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      ClearWork.Inv cs (added ++ loans) v ∧ Upper {} cs (added ++ loans) v ∧
      ClearWork.queueView v = (ClearWork.queueView w).map (fun q => (q.1,q.2 ++ added.map Owner.slot)) := by
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
    exact ⟨[],Or.inl rfl,hi,upper,by simp⟩
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,got,ag,hget,device,readDev,ad,hdev,peek,peeked,ap,hpeek,
      pending,checked,ac,hpending,tail⟩ := tail
    cases u
    obtain ⟨dg,pg,hdg,hpg,pos,acquired⟩ := ClearWork.acquire hi testedAmbient ag hget
    have deq : dg = d := Option.some.inj (hdg.symm.trans hd)
    subst dg
    have peq : pg = p := Option.some.inj (hpg.symm.trans hp)
    subst pg
    obtain ⟨dd,pp,hdd,hpp,positive,effect⟩ := peerGet_loan pid w got testedAmbient ag hget
    have deq : dd = d := Option.some.inj (hdd.symm.trans hd)
    subst dd
    have peq : pp = p := Option.some.inj (hpp.symm.trans hp)
    subst pp
    have upperGot : Upper {} cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) got := by
      obtain ⟨dg,pg,hdg,hpg,_,transfer⟩ := peerGet_handoff testedAmbient ag hget
      have deq : dg = d := Option.some.inj (hdg.symm.trans hd)
      subst dg
      have peq : pg = p := Option.some.inj (hpg.symm.trans hp)
      subst pg
      intro owner
      have equation := transfer.count owner
      have before := upper owner
      simp [demand,DurableHolders.owners,HandoffDelta.owners] at equation before ⊢
      simp only [List.count_cons,List.count_nil] at equation ⊢
      omega
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
      have found : resident got ⟨d.ifindex,pid,p.internalId⟩ =
          some {p with refcount := p.refcount + 1} := by simp [resident,dev]
      exact ⟨[],Or.inl rfl,kept,upperGot.payment found tail,
        by simp [ClearWork.queueView,out,hd]⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨u,recorded,arecord,hrecord,hinstall⟩ := tail
      have same := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun g => g = got))
        got ac u recorded arecord rfl hrecord
      subst recorded
      cases hinstall
      have afterUpper := upperGot.peer_view (show peerView
        {got with dev := got.dev.map fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}} = peerView got from by
          unfold peerView
          cases got.dev <;> rfl)
      refine ⟨[⟨d.ifindex,pid,p.internalId⟩],Or.inr ⟨d,p,hd,hp,rfl⟩,
        ClearWork.install acquired pid,afterUpper,?_⟩
      simp [ClearWork.queueView,dev,hd]

end TimerFrames

theorem Account.expired_zero (pid : PeerId) {h : DurableHolders}
    (account : Account h cs loans w) (a b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      Account (addClear h added) cs loans v := by
  have upper : Upper {} cs (h.owners ++ loans) w := by
    exact account.upper
  obtain ⟨added,source,kept,afterUpper,queue⟩ :=
    TimerFrames.zero_source ⟨account.funded.carriers,account.stable⟩ upper a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (expiredZero_frame pid w)
    w a () v b (ClearFrame.refl w) run
  have aligned : (addClear h added).Aligned v := by
    have base := congrArg Prod.fst frame.passive
    have cursor7 := congrArg (fun p => p.2.1) frame.passive
    have cursor8 := congrArg (fun p => p.2.2) frame.passive
    refine ⟨account.funded.aligned.base.trans base.symm,?_,?_,?_,
      account.funded.aligned.cursor7.trans cursor7.symm,account.funded.aligned.cursor8.trans cursor8.symm⟩
    · intro d hd
      have same := frame.send
      cases hw : w.dev with
      | none => simp [sendView,hd,hw] at same
      | some old =>
        have eq : d.sendWorkQueue = old.sendWorkQueue := by
          simpa only [sendView,hd,hw,Option.map_some,Option.some.injEq] using same
        exact eq.trans (account.funded.aligned.send old hw)
    · change (h.clear ++ added).map Owner.slot = _
      rw [List.map_append,account.funded.aligned.clear]
      cases hw : w.dev with
      | none =>
        have empty : added = [] := by
          rcases source with empty | ⟨d,p,hd,_,_⟩
          · exact empty
          · simp [hw] at hd
        have out : v.dev = none := by
          cases hv : v.dev with
          | none => rfl
          | some d => simp [ClearWork.queueView,hw,hv] at queue
        simp [out,empty]
      | some old =>
        cases hv : v.dev with
        | none => simp [ClearWork.queueView,hw,hv] at queue
        | some d =>
          have eq : d.clearWorkQueue = old.clearWorkQueue ++ added.map Owner.slot := by
            simpa [ClearWork.queueView,hw,hv] using congrArg (Option.map Prod.snd) queue
          simp [eq]
    · intro q batches found
      exact account.funded.aligned.tx q batches (frame.tx q batches found)
  refine ⟨added,source,⟨⟨aligned,WorkReservations.carrier_loans_perm kept.1
    (addClear_owners h added loans).symm⟩,?_,kept.2⟩⟩
  intro owner
  have bound := afterUpper owner
  have counts := (addClear_owners h added loans).count_eq owner
  change balance v owner ≤ demand cs (added ++ (h.owners ++ loans)) owner at bound
  unfold demand at bound ⊢
  rw [counts]
  exact bound

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
