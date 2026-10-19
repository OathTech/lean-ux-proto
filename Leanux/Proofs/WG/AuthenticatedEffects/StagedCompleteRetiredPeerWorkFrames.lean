import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHolderFrames

/-! Native clear/send prefixes retain the same stamped holder account before
its explicit worker loan is paid. No history or completed-worker premise is
used to infer a live loan. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Std.Do
open DurableHolders

namespace WorkFrames

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (count : ∀ p, (f p).refcount = p.refcount)
    (queue : ∀ p, (f p).rxQueue = p.rxQueue) :
    SameView peerView (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,middle,hread,hwrite⟩ := run
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w read p a middle hread
  cases hwrite
  simp only [hd,Option.map_some,peerView,Option.bind_some]
  refine Prod.ext rfl ?_
  funext q
  by_cases same : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]

private theorem read_peer (pid : PeerId) : SameView peerView (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg peerView (getPeer_normal pid w v p a b run).1

private theorem key_put (kid : Option KeypairId) (now : Bool) :
    SameView peerView (keypairPut kid now) :=
  (keypairPut_credit_frame kid now).of_factor Prod.fst peerView (fun _ => rfl)

theorem handshake (pid : PeerId) : SameView peerView (handshakeClear pid) := by
  intro initial
  unfold handshakeClear
  apply preserves_bind (indexOwner_peerDeref_preserves (.handshake pid) _)
  intro _
  apply preserves_bind (show Preserves (fun w => peerView w = initial)
      (liftIndex (indexRemove (.handshake pid))) from ?_)
  · intro _
    unfold handshakeZero
    exact (update_peer pid (fun p => { p with
        ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0,
        chainingKey := List.replicate 32 0, hash := List.replicate 32 0,
        remoteIndex := 0, handshakeState := 0 }) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp
      (fun s => s = initial)
  · apply hoare_liftIndex
    intro w d table hi hd
    simpa [peerView,hd] using hi

theorem keys (pid : PeerId) : SameView peerView (keypairsClear pid) := by
  unfold keypairsClear
  apply (read_peer pid).bind
  intro p
  apply (update_peer pid (fun p => {p with keypairNext := none}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind
  intro _
  apply (key_put p.keypairNext true).bind
  intro _
  apply (read_peer pid).bind
  intro p
  apply (update_peer pid (fun p => {p with keypairPrevious := none}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind
  intro _
  apply (key_put p.keypairPrevious true).bind
  intro _
  apply (read_peer pid).bind
  intro p
  exact (update_peer pid (fun p => {p with keypairCurrent := none}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind
    (fun _ => key_put p.keypairCurrent true)

theorem initiation (pid : PeerId) : SameView peerView (sendHandshakeInitiation pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendHandshakeInitiation_view) pid)
    w a x v b run
  have carrier := ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
    ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) frame).trans
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
  exact congrArg Prod.fst carrier

theorem fixed {action : WG.M α} (peers : SameView peerView action)
    (frame : ∀ initial, Preserves (Frame initial) action)
    (keeps : ∀ cs loans, Preserves (ClearWork.Inv cs loans) action)
    (account : Account holders carriers loans w)
    (run : (action.run w).run a = .ok ((x,v),b)) :
    Account holders carriers loans v := by
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (keeps carriers (holders.owners ++ loans)) w a x v b
    ⟨account.funded.carriers,account.stable⟩ run
  have fields := (hoare_iff_run_ambient _ _ _).mp (frame w)
    w a x v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame fields,kept.1⟩,
    account.upper.peer_view ((ProjectedAction.iff_run_ambient _ _ _).mp peers w a x v b run),kept.2⟩

end WorkFrames

theorem Account.handshake_clear (account : Account holders carriers loans w)
    (run : ((handshakeClear pid).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v :=
  WorkFrames.fixed (WorkFrames.handshake pid) (HolderWorkFrames.handshakeClear_frame pid)
    (fun _ _ => ClearWork.handshakeClear_preserves pid) account run

theorem Account.keys_clear (account : Account holders carriers loans w)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v :=
  WorkFrames.fixed (WorkFrames.keys pid) (HolderWorkFrames.keypairsClear_frame pid)
    (fun _ _ => ClearWork.keypairsClear_preserves pid) account run

theorem Account.send_initiation (account : Account holders carriers loans w)
    (run : ((sendHandshakeInitiation pid).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v :=
  WorkFrames.fixed (WorkFrames.initiation pid) (HolderWorkFrames.sendHandshakeInitiation_frame pid)
    (fun _ _ => SendWork.initiation_preserves pid) account run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
