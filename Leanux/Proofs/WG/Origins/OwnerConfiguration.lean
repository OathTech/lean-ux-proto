import Leanux.Proofs.WG.Origins.OwnerFocus
import Leanux.Proofs.WG.Origins.OwnerHistory

/-! Configuration may create a peer at the current frontier. Current support
and receiving-owner bounds therefore travel together through the actual
lifetime observer; neither is assumed independently preserved by creation. -/
namespace Leanux.Proofs.WG.OwnerConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues
open Origins.HistorySupport (sessions sensitive lifeEncode sessionEvent)

private theorem mixed_frame (projection : RxHistory.Event → Option E)
    (quiet : ∀ e, projection (lifeEncode e) = none) (g : PrefixM LifetimeEvent α) :
    HistoryFrame projection (RxHistory.mixed g) := by
  intro w h
  unfold RxHistory.mixed RxHistory.audit auditFocus
  rw [Origins.HistorySupport.focus_compose]
  exact focusPrefix_other _ _ projection quiet g w h

private theorem native_joint_endpoint (g : RxHistory.Obs α) (a : WG.M α)
    (erases : ErasesPrefix g (liftWG a))
    (state : ∀ allocation history, Hoare a
      (fun w => AllocationInv allocation w ∧ CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w))
    (w : World) (h : List RxHistory.Event) (hi : OwnerChecks.Inv h w)
    (x : α) (v : World) (hr : (runPrefix g w h).1 = .ok (x,v)) :
    CurrentLifecycle.Inv (sessions h) v.wg ∧ OwnerBounds.Carrier v.wg := by
  have native := (erases w h).symm.trans hr
  rw [liftWG_run] at native
  cases hs : (a.run w.wg).run w.ambient with
  | error e => simp [hs,Except.map] at native
  | ok endpoint =>
    rcases endpoint with ⟨⟨result,u⟩,ambient⟩
    simp only [hs,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact (hoare_iff_run_ambient _ _ _).mp (state (RxHistory.prior h) (sessions h))
      w.wg w.ambient result u ambient ⟨hi.allocation,hi.current.2.1,hi.carrier⟩ hs

/-- A joint native contract, with allocation at this same input history,
is sufficient for the original two-stage lifetime focus. -/
theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a)
    (allocation : StatePrefixPreserves
      (fun h w _ => AllocationInv h w) LifetimeEvent.Safe g)
    (material : Origins.Retaining.RetainsCall a)
    (state : ∀ allocation history, Hoare a
      (fun w => AllocationInv allocation w ∧ CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver g)) := by
  intro w h hi
  obtain ⟨s,hs,safe,post⟩ :=
    Origins.HistorySupport.mixed (liftWGObserver g) (liftWG a)
      (liftWGObserver_erases erases) material.product w h hi.current.1
  obtain ⟨_,_,bsafe,bpost⟩ :=
    RxHistory.mixed_preserves allocation.liftWGObserver w h hi.boundary
  have quiet := mixed_frame sensitive (fun _ => rfl) (liftWGObserver g)
  have currentChecks := CurrentChecks.Checks.of_unchanged (w := w) (h := h)
    (Appends.focus _ _ _) quiet hi.current.2.2
  have ownerChecks := OwnerChecks.Checks.of_unchanged (w := w) (h := h)
    (Appends.focus _ _ _) quiet hi.checked
  refine ⟨s,hs,⟨⟨safe,currentChecks⟩,bsafe,ownerChecks⟩,?_⟩
  cases hr : (runPrefix (RxHistory.mixed (liftWGObserver g)) w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at post bpost
    have kept := native_joint_endpoint _ a
      (RxHistory.mixed_erases (liftWGObserver_erases erases)) state w h hi out.1 out.2 hr
    have frame := mixed_frame sessionEvent (fun _ => rfl) (liftWGObserver g) w h
    have current : CurrentSessionPrefix.StateInv
        (runPrefix (RxHistory.mixed (liftWGObserver g)) w h).2 out.2 := by
      change CurrentLifecycle.Inv (sessions _) out.2.wg
      change sessions (runPrefix (RxHistory.mixed (liftWGObserver g)) w h).2 = sessions h at frame
      rw [frame]
      exact kept.1
    exact ⟨⟨post,current,currentChecks⟩,bpost,kept.2,ownerChecks⟩

/-- Actual peer creation preserves both invariants together. Owner bounds
supply the missing fresh-slot condition; allocation safety remains the
original observer's independent guarantee on the identical execution. -/
theorem peerCreate (key : Key) (psk : Option Key) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (peerCreateMixed key psk))) := by
  apply native_mixed _ _ (peerCreateMixed_erases key psk) (peerCreateMixed_preserves key psk)
    (Origins.Retaining.of_view (Origins.Retaining.peerCreate_material key psk))
  intro allocation history
  exact hoare_consequence (OwnerCreation.peerCreate_current key psk history)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

end Leanux.Proofs.WG.OwnerConfiguration
