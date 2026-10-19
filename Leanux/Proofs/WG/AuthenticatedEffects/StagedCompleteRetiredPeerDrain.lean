import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWorkDispatch
import Leanux.Proofs.WG.Queues.HolderDrains

/-! Native finite drains consume only selected work holders and retain both
reference bounds for the same remaining account. Caller loans are unchanged.
These are normal source contracts, including the exact access-observer run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders WorkReservations

def DuringWork (original : DurableHolders) (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ holders, WorkRemainder original holders ∧ Account holders cs loans w

theorem duringWork_initial {holders : DurableHolders} (hi : Account holders cs loans w) : DuringWork holders cs loans w :=
  ⟨holders,WorkRemainder.refl holders,hi⟩

private theorem send_selected (hi : DuringWork original cs loans w) (hd : w.dev=some d)
    (member : pid∈d.sendWorkQueue) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a=.ok (((),v),b)) :
    DuringWork original cs loans v := by
  obtain ⟨holders,remainder,account⟩ := hi
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((account.funded.aligned.send d hd) ▸ member)
  have kept := Account.flushed_send selected account a b hr
  exact ⟨holders.withoutSend rest,remainder.trans ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.WorkRemainder.send_step) selected),kept⟩

private theorem clear_selected (hi : DuringWork original cs loans w) (hd : w.dev=some d)
    (member : pid∈d.clearWorkQueue) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a=.ok (((),v),b)) :
    DuringWork original cs loans v := by
  obtain ⟨holders,remainder,account⟩ := hi
  have queue : holders.clear.map Owner.slot=d.clearWorkQueue := by
    simpa only [hd,Option.map_some,Option.getD_some] using account.funded.aligned.clear
  obtain ⟨o,rest,selected⟩ := select_exists holders.clear pid (queue ▸ member)
  have kept := Account.flushed_clear selected account a b hr
  exact ⟨holders.withoutClear rest,remainder.trans ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.WorkRemainder.clear_step) selected),kept⟩

private theorem ambient_cut (action : AmbientM α) (w v : WGWorld) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) :
    v=w ∧ action.run a=.ok (x,b) := by
  change (((StateT.lift action : WG.M α).run w).run a)=.ok ((x,v),b) at run
  rw [stateLiftAmbient_run] at run
  cases h : action.run a with
  | error e => simp [h,Except.map] at run
  | ok out =>
    rcases out with ⟨y,c⟩
    simp only [h,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨rfl,rfl⟩

/-- Every normal iteration pays only an occurrence selected from its actual
saved queue. Exhaustion and missing/malformed section records still stop. -/
theorem drain_preserves (upTo : Option PeerId) (original : DurableHolders)
    (cs : Ledger) (loans : Reservations) :
    Preserves (DuringWork original cs loans) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec id (DuringWork original cs loans)
    intro i acc
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a step v b hi hr
    dsimp only at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨d,read,ar,getter,rest⟩ := hr
    obtain ⟨readEq,ambientEq,hd⟩ := DecryptCarrier.getDev_current a ar getter
    subst read
    subst ar
    split at rest
    · cases rest; exact hi
    · rw [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨unit,peeked,ap,peek,rest⟩ := rest
      obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .sendWorker) w peeked a ap peek
      subst peeked
      cases unit with
      | some u =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨pid,picked,ac,resolve,done,paid,ad,worker,finish⟩ := rest
        obtain ⟨same,resolver⟩ := ambient_cut (AmbientM.resolveUnit .sendWorker u d.sendWorkQueue) w picked ap ac resolve
        subst picked
        cases done
        have kept := send_selected hi hd (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 ac ad worker
        cases finish
        exact kept
      | none =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨unit,peeked,ac,peek,rest⟩ := rest
        obtain ⟨same,_⟩ := ambient_cut (AmbientM.peekUnit .clearPeerWorker) w peeked ap ac peek
        subst peeked
        cases unit with
        | some u =>
          simp only [MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨pid,picked,ar,resolve,done,paid,ad,worker,finish⟩ := rest
          obtain ⟨same,resolver⟩ := ambient_cut (AmbientM.resolveUnit .clearPeerWorker u d.clearWorkQueue) w picked ac ar resolve
          subst picked
          cases done
          have kept := clear_selected hi hd (ClearWork.resolveUnit_member _ _ _ _ _ _ resolver).1 ar ad worker
          split at finish <;> cases finish <;> exact kept
        | none =>
          simp only [MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨current,read,ar,getter,rest⟩ := rest
          obtain ⟨same,_⟩ := ambient_cut (get : AmbientM Ambient) w read ac ar getter
          subst read
          split at rest
          · cases rest
          · cases hs : d.sendWorkQueue.head? with
            | some pid =>
              simp only [hs,MaterialOrigin.bind_ok_ambient] at rest
              obtain ⟨done,paid,ad,worker,finish⟩ := rest
              cases done
              have kept := send_selected hi hd (List.mem_of_head? hs) ar ad worker
              cases finish
              exact kept
            | none =>
              cases hc : d.clearWorkQueue.head? with
              | none => simp only [hs,hc] at rest; cases rest; exact hi
              | some pid =>
                simp only [hs,hc,MaterialOrigin.bind_ok_ambient] at rest
                obtain ⟨done,paid,ad,worker,finish⟩ := rest
                cases done
                have kept := clear_selected hi hd (List.mem_of_head? hc) ar ad worker
                split at finish <;> cases finish <;> exact kept
  · intro result
    rcases result with ⟨result,⟨⟩⟩
    cases result with
    | none => exact hoare_liftAmbient (AmbientM.invariant _) _
    | some result => exact preserves_pure result

/-- The initial holder account is retained except for ordered send/clear
occurrences actually paid by the original finite drain. -/
theorem drain_normal (upTo : Option PeerId) {holders : DurableHolders}
    (hi : Account holders cs loans w) (a b : Ambient)
    (hr : ((drainHandshakeSendWq upTo).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (drain_preserves upTo holders cs loans)
    w a () v b (duringWork_initial hi) hr

/-- The existing access observer supplies the same execution, at arbitrary
incoming lifetime history. This conclusion is restricted to normal return. -/
theorem drain_observed_normal (upTo : Option PeerId) {holders : DurableHolders}
    (hi : Account holders cs loans w)
    (h : List LifetimeEvent) (a b : Ambient)
    (hr : (runStatePrefix (drainHandshakeSendWqPrefix upTo) w a h).1 = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  drain_normal upTo hi a b ((drainHandshakeSendWqPrefix_erases upTo w a h).symm.trans hr)

private theorem during_frame (action : WG.M α) (peers : SameView peerView action)
    (frame : ∀ initial, Preserves (Frame initial) action)
    (keeps : ∀ cs loans, Preserves (ClearWork.Inv cs loans) action) :
    Preserves (DuringWork original cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  obtain ⟨holders,remainder,account⟩ := hi
  exact ⟨holders,remainder,WorkFrames.fixed peers frame keeps account hr⟩

private theorem del_view (pid : PeerId) (timer : PeerTimer) :
    SameView peerView (delTimer pid timer) := by
  unfold delTimer
  apply WorkFrames.update_peer
  all_goals intro p; cases timer <;> rfl

private theorem del_stable (pid : PeerId) (timer : PeerTimer) :
    Preserves (ClearWork.Inv cs loans) (delTimer pid timer) := by
  unfold delTimer
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.modify_peer)
  all_goals first | (intro p; cases timer <;> rfl) | (intro p kid h; cases timer <;> exact h)

theorem delTimer_preserves (pid : PeerId) (timer : PeerTimer) :
    Preserves (DuringWork original cs loans) (delTimer pid timer) :=
  during_frame _ (del_view pid timer)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)
    (fun _ _ => del_stable pid timer)

theorem keypairsClear_preserves (pid : PeerId) :
    Preserves (DuringWork original cs loans) (keypairsClear pid) :=
  during_frame _ (WorkFrames.keys pid) (HolderWorkFrames.keypairsClear_frame pid)
    (fun _ _ => ClearWork.keypairsClear_preserves pid)

/-- The real five timer deletions and conditional selected clear-work flush
retain the same caller loans, including detached or saved base reservations. -/
theorem timersStop_preserves (pid : PeerId) :
    Preserves (DuringWork original cs loans) (timersStop pid) := by
  unfold timersStop
  apply preserves_bind
  · apply list_view_spec id (DuringWork original cs loans)
    intro timer u
    exact preserves_bind (delTimer_preserves pid timer) (fun _ => preserves_pure _)
  · intro _
    apply preserves_bind (show Preserves (DuringWork original cs loans) getDev from by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a d v b hi hr
      exact (DecryptCarrier.getDev_current a b hr).1 ▸ hi)
    intro d
    split
    · exact drain_preserves _ _ _ _
    · exact preserves_pure ()

theorem timersStop_normal (pid : PeerId) {holders : DurableHolders}
    (hi : Account holders cs loans w) (a b : Ambient)
    (hr : ((timersStop pid).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (timersStop_preserves pid)
    w a () v b (duringWork_initial hi) hr

theorem timersStop_observed_normal (pid : PeerId) {holders : DurableHolders}
    (hi : Account holders cs loans w)
    (h : List LifetimeEvent) (a b : Ambient)
    (hr : (runStatePrefix (timersStopPrefix pid) w a h).1 = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  timersStop_normal pid hi a b ((timersStopPrefix_erases pid w a h).symm.trans hr)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
