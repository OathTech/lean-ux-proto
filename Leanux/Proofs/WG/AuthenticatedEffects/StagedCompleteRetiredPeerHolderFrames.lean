import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTransfers

/-! Concrete native holder transfers retain both reference bounds together.
These are normal source-cut rules, not a whole initialized execution claim. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans before after rest : Reservations} {w v : WGWorld} {a b : Ambient}
  {owner : Owner} {pid : PeerId} {delta : HandoffDelta}

theorem Account.handoff (account : Account holders carriers (loans ++ before) w)
    (step : Handoff w v before after delta) (keys : KeysCompatible v)
    (passive : passiveView v = passiveView w) (stable : StableRx carriers v) :
    Account (holders.absorb delta) carriers (loans ++ after) v :=
  ⟨account.funded.handoff step keys passive,account.upper.handoff step,stable⟩

theorem Account.payment (account : Account holders carriers (owner :: loans) w)
    (run : ((peerPut (some owner.slot)).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v := by
  have positive : 0 < demand carriers (holders.owners ++ owner :: loans) owner := by
    simp [demand]
    omega
  obtain ⟨p,found,_⟩ := protected_resident account.funded.carriers.funded positive
  have paid := reservation_payment_stable
    (WorkReservations.carrier_loans_perm account.funded.carriers List.perm_middle)
    account.stable a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.peerPut_frame (some owner.slot) w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame frame,paid.1⟩,account.upper.payment found run,paid.2⟩

theorem Account.make_dead (account : Account holders carriers loans w) (pid : PeerId)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    Account (holders.withoutBase (BaseRemoval.live holders.base pid)) carriers
      (BaseRemoval.detached holders.base pid ++ loans) v := by
  have kept := peerMakeDead_funded pid account.funded account.stable a b run
  have fields := BaseRemoval.peerMakeDead_normal pid w v a b run
  have peers : peerView v = peerView w := congrArg (fun s => s.1.1) fields.1
  exact ⟨kept.1,(account.upper.peer_view peers).detach pid,kept.2⟩

theorem Account.take_clear (account : Account holders carriers loans w)
    (selected : WorkReservations.Selected holders.clear pid owner rest) :
    Account (holders.withoutClear rest) carriers (owner :: loans) (clearTaken w pid) := by
  have peers : peerView (clearTaken w pid) = peerView w := by
    unfold clearTaken peerView
    cases w.dev <;> rfl
  exact ⟨account.funded.take_clear selected,(account.upper.peer_view peers).take_clear selected,
    (ClearWork.erase_queue ⟨account.funded.carriers,account.stable⟩ pid).2⟩

theorem Account.take_send (account : Account holders carriers loans w)
    (selected : WorkReservations.Selected holders.send pid owner rest) :
    Account (holders.withoutSend rest) carriers (owner :: loans) (sendTaken w pid) := by
  have peers : peerView (sendTaken w pid) = peerView w := by
    unfold sendTaken peerView
    cases w.dev <;> rfl
  have unchanged : stableView (sendTaken w pid) = stableView w := by
    unfold sendTaken stableView rxView RxRing.nativeCell
    cases w.dev <;> rfl
  exact ⟨account.funded.take_send selected,(account.upper.peer_view peers).take_send selected,
    account.stable.view unchanged⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
