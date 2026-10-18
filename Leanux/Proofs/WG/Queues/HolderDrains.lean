import Leanux.Proofs.WG.Queues.HolderClearDispatch
import Leanux.Proofs.WG.Queues.HolderSendDispatch
import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Queues.DecryptCarrier

/-! The actual finite handshake-work drain retains one complete funded account.
Only selected work occurrences disappear; transient caller loans stay supplied. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations

structure WorkRemainder (before after : DurableHolders) : Prop where
  base : after.base = before.base
  tx : after.tx = before.tx
  cursor7 : after.cursor7 = before.cursor7
  cursor8 : after.cursor8 = before.cursor8
  send : after.send.Sublist before.send
  clear : after.clear.Sublist before.clear

theorem WorkRemainder.refl (holders : DurableHolders) : WorkRemainder holders holders :=
  ⟨rfl,rfl,rfl,rfl,.refl _,.refl _⟩

theorem WorkRemainder.trans (first : WorkRemainder h k) (next : WorkRemainder k j) :
    WorkRemainder h j :=
  ⟨next.base.trans first.base,next.tx.trans first.tx,next.cursor7.trans first.cursor7,
    next.cursor8.trans first.cursor8,next.send.trans first.send,next.clear.trans first.clear⟩

private theorem selected_sublist {owners : Reservations} (selected : Selected owners pid o rest) : rest.Sublist owners := by
  obtain ⟨before,after,rfl,_,_,rfl⟩ := selected
  exact (List.Sublist.refl before).append (.cons o (.refl after))

private theorem WorkRemainder.send_step (selected : Selected holders.send pid o rest) :
    WorkRemainder holders (holders.withoutSend rest) :=
  ⟨rfl,rfl,rfl,rfl,selected_sublist selected,.refl _⟩

private theorem WorkRemainder.clear_step (selected : Selected holders.clear pid o rest) :
    WorkRemainder holders (holders.withoutClear rest) :=
  ⟨rfl,rfl,rfl,rfl,.refl _,selected_sublist selected⟩

def DuringWork (original : DurableHolders) (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ holders, WorkRemainder original holders ∧ holders.Funded cs loans w ∧ StableRx cs w

theorem duringWork_initial {holders : DurableHolders} (hi : holders.Funded cs loans w)
    (stable : StableRx cs w) : DuringWork holders cs loans w :=
  ⟨holders,WorkRemainder.refl holders,hi,stable⟩

private theorem send_selected (hi : DuringWork original cs loans w) (hd : w.dev=some d)
    (member : pid∈d.sendWorkQueue) (a b : Ambient)
    (hr : ((runFlushedSendWork pid).run w).run a=.ok (((),v),b)) :
    DuringWork original cs loans v := by
  obtain ⟨holders,remainder,funded,stable⟩ := hi
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((funded.aligned.send d hd) ▸ member)
  obtain ⟨kept,stable⟩ := flushed_send_funded selected funded stable a b hr
  exact ⟨holders.withoutSend rest,remainder.trans (WorkRemainder.send_step selected),kept,stable⟩

private theorem clear_selected (hi : DuringWork original cs loans w) (hd : w.dev=some d)
    (member : pid∈d.clearWorkQueue) (a b : Ambient)
    (hr : ((runFlushedClearWork pid).run w).run a=.ok (((),v),b)) :
    DuringWork original cs loans v := by
  obtain ⟨holders,remainder,funded,stable⟩ := hi
  have queue : holders.clear.map Owner.slot=d.clearWorkQueue := by
    simpa only [hd,Option.map_some,Option.getD_some] using funded.aligned.clear
  obtain ⟨o,rest,selected⟩ := select_exists holders.clear pid (queue ▸ member)
  obtain ⟨kept,stable⟩ := flushed_clear_funded selected funded stable a b hr
  exact ⟨holders.withoutClear rest,remainder.trans (WorkRemainder.clear_step selected),kept,stable⟩

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
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((drainHandshakeSendWq upTo).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (drain_preserves upTo holders cs loans)
    w a () v b (duringWork_initial hi stable) hr

/-- The existing access observer supplies the same execution, at arbitrary
incoming lifetime history. This conclusion is restricted to normal return. -/
theorem drain_observed_normal (upTo : Option PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (h : List LifetimeEvent) (a b : Ambient)
    (hr : (runStatePrefix (drainHandshakeSendWqPrefix upTo) w a h).1 = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  drain_normal upTo hi stable a b ((drainHandshakeSendWqPrefix_erases upTo w a h).symm.trans hr)

private theorem during_frame (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action)
    (keeps : ∀ cs loans, Preserves (ClearWork.Inv cs loans) action) :
    Preserves (DuringWork original cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  obtain ⟨holders,remainder,funded,stable⟩ := hi
  have fields := (hoare_iff_run_ambient _ _ _).mp (frame w) w a x v b (Frame.refl w) hr
  have post := (hoare_iff_run_ambient _ _ _).mp (keeps cs (holders.owners ++ loans))
    w a x v b ⟨funded.carriers,stable⟩ hr
  exact ⟨holders,remainder,⟨funded.aligned.frame fields,post.1⟩,post.2⟩

private theorem del_stable (pid : PeerId) (timer : PeerTimer) :
    Preserves (ClearWork.Inv cs loans) (delTimer pid timer) := by
  unfold delTimer
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.modify_peer)
  all_goals first | (intro p; cases timer <;> rfl) | (intro p kid h; cases timer <;> exact h)

theorem delTimer_preserves (pid : PeerId) (timer : PeerTimer) :
    Preserves (DuringWork original cs loans) (delTimer pid timer) :=
  during_frame _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)
    (fun _ _ => del_stable pid timer)

theorem keypairsClear_preserves (pid : PeerId) :
    Preserves (DuringWork original cs loans) (keypairsClear pid) :=
  during_frame _ (HolderWorkFrames.keypairsClear_frame pid)
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
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((timersStop pid).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (timersStop_preserves pid)
    w a () v b (duringWork_initial hi stable) hr

theorem timersStop_observed_normal (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (h : List LifetimeEvent) (a b : Ambient)
    (hr : (runStatePrefix (timersStopPrefix pid) w a h).1 = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  timersStop_normal pid hi stable a b ((timersStopPrefix_erases pid w a h).symm.trans hr)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
