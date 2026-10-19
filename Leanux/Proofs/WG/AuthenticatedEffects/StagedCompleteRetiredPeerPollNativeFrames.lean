import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollContextFrames

/-! Native poll bookkeeping keeps exact peer counts. Peek may rearrange a
queue cache, while counter validation and NAPI completion preserve its peer
projection. No deletion-retaining frame is used as count equality. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Phased.store (account : Phased holders carriers loans w)
    (same : wgStoreView v = wgStoreView w) : Phased holders carriers loans v := by
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  exact ⟨⟨account.funded.aligned.frame (Frame.of_store same),account.funded.carriers.kernel same⟩,
    account.upper.peer_view (by simp only [peerView,device])⟩

theorem Upper.rx_peek (upper : Upper holders carriers loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peekRxQueue pid).run w).run a = .ok ((first,v),b)) : Upper holders carriers loans v := by
  unfold peekRxQueue at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,au,get,tail⟩ := run
  obtain ⟨same,ambient,d,device,peer⟩ := getPeer_normal pid w u p a au get
  subst u
  subst au
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨⟨head,q⟩,u,au,peek,tail⟩ := tail
  obtain ⟨_,_,_,same⟩ := prev_peek_normal p.rxQueue w u a au head q peek
  subst u
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨p2,u,a2,get2,tail⟩ := tail
  obtain ⟨same,ambient,d2,device2,peer2⟩ := getPeer_normal pid w u p2 au a2 get2
  subst u
  subst a2
  have eq := Option.some.inj (device2.symm.trans device)
  subst d2
  have eq := Option.some.inj (peer2.symm.trans peer)
  subst p2
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨u,out,ao,set,finish⟩ := tail
  cases u
  cases finish
  have after : v = {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := q}}} := by
    cases set
    simp [device]
  intro owner
  rw [after,peer_update_balance (q := {p with rxQueue := q}) device peer rfl rfl]
  exact upper owner

theorem Account.rx_peek (account : Account holders carriers loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peekRxQueue pid).run w).run a = .ok ((first,v),b)) :
    Account holders carriers loans v ∧ Peeked pid first v := by
  obtain ⟨funded,peek⟩ := peek_state pid account.funded.carriers a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (peek_frame pid w)
    w a first v b (Frame.refl w) run
  exact ⟨⟨⟨account.funded.aligned.frame frame,funded⟩,account.upper.rx_peek pid a b run,
    stable_peek pid account.stable a b run⟩,peek⟩

theorem Phased.counter (account : Phased holders carriers loans w) (stable : StableRx rest w)
    (kid : KeypairId) (nonce : Nat) (a b : Ambient)
    (run : ((counterValidate kid nonce).run w).run a = .ok ((result,v),b)) :
    Phased holders carriers loans v ∧ StableRx rest v := by
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (counter_carrierView kid nonce) w a result v b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (counter_frame kid nonce w)
    w a result v b (Frame.refl w) run
  exact ⟨⟨⟨account.funded.aligned.frame frame,account.funded.carriers.view same⟩,
    account.upper.peer_view (congrArg Prod.fst same)⟩,stable_counterValidate kid nonce stable a b run⟩

theorem Account.rx_complete (account : Account holders carriers loans w) (cold : ColdHead pid w)
    (a b : Ambient) (run : ((completeRxQueue pid).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v := by
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (complete_carrierView pid) w a () v b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (complete_frame pid w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame frame,account.funded.carriers.view same⟩,
    account.upper.peer_view (congrArg Prod.fst same),account.stable.complete cold a b run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
