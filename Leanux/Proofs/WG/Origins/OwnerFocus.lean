import Leanux.Proofs.WG.Origins.OwnerChecks
import Leanux.Proofs.WG.Origins.OwnerConsume
import Leanux.Proofs.WG.Origins.CurrentWorkers

/-! Joint current, lifetime and receiving-owner contracts for quiet calls.
The allocation premise is taken at the actual input journal, never inferred
for a saved earlier World from a later lifetime prefix. -/
namespace Leanux.Proofs.WG.OwnerChecks
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues
open Origins.HistorySupport (sensitive)

theorem congr (hg : Preserves g)
    (eq : ∀ w h, runPrefix g w h = runPrefix f w h) : Preserves f := by
  intro w h hi
  simpa only [← eq w h] using hg w h hi

theorem quiet (g : RxHistory.Obs α) (appends : Appends g)
    (noSensitive : HistoryFrame sensitive g)
    (current : CurrentChecks.Preserves g)
    (boundary : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe g)
    (carrier : ∀ w h, Inv h w → ∀ x v,
      (runPrefix g w h).1 = .ok (x,v) → OwnerBounds.Carrier v.wg) : Preserves g :=
  combine g current boundary carrier
    (fun _ _ hi => Checks.of_unchanged appends noSensitive hi.checked)

/-- Exact native erasure supplies the normal endpoint; the source Hoare rule
uses the allocation invariant of this very entry history. -/
theorem native_endpoint (g : RxHistory.Obs α) (a : WG.M α)
    (erases : ErasesPrefix g (liftWG a))
    (state : ∀ history, Hoare a
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w))
    (w : World) (h : List RxHistory.Event) (hi : Inv h w)
    (x : α) (v : World) (hr : (runPrefix g w h).1 = .ok (x,v)) :
    OwnerBounds.Carrier v.wg := by
  have native := (erases w h).symm.trans hr
  rw [liftWG_run] at native
  cases hs : (a.run w.wg).run w.ambient with
  | error e => simp [hs,Except.map] at native
  | ok endpoint =>
    rcases endpoint with ⟨⟨result,u⟩,ambient⟩
    simp only [hs,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact (hoare_iff_run_ambient _ _ _).mp (state (RxHistory.prior h))
      w.wg w.ambient result u ambient ⟨hi.allocation,hi.carrier⟩ hs

theorem native_quiet (g : RxHistory.Obs α) (a : WG.M α)
    (appends : Appends g) (erases : ErasesPrefix g (liftWG a))
    (noSensitive : HistoryFrame sensitive g)
    (current : CurrentChecks.Preserves g)
    (boundary : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe g)
    (state : ∀ history, Hoare a
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w)) : Preserves g :=
  quiet g appends noSensitive current boundary (native_endpoint g a erases state)

/-- Lifetime-only calls retain arbitrary incoming receipts and probes. Their
actual two-stage focus appends no new owner-check event. -/
theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a)
    (allocation : StatePrefixPreserves
      (fun h w _ => AllocationInv h w) LifetimeEvent.Safe g)
    (material : Origins.Retaining.RetainsCall a)
    (current : ∀ history, Framing.Preserves (CurrentLifecycle.Inv history) a)
    (carrier : ∀ history, Hoare a
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w)) :
    Preserves (RxHistory.mixed (liftWGObserver g)) := by
  apply native_quiet _ a (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases erases)) _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_mixed)
      g a erases material current)
    (RxHistory.mixed_preserves allocation.liftWGObserver) carrier
  intro w h
  unfold auditFocus
  rw [Origins.HistorySupport.focus_compose]
  exact focusPrefix_other _ _ sensitive (fun _ => rfl) _ w h

/-- The concrete input path uses its existing lifetime observer. All normal
None/ENOSPC/EPIPE paths and stopped prefixes remain in that execution. -/
theorem consumeData (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) :=
  native_mixed _ _ (consumeDataPrefix_erases msg src ds)
    (consumeDataPrefix_allocation msg src ds)
    (Origins.Retaining.consumeData_material msg src ds)
    (CurrentRx.consumeData_preserves msg src ds)
    (OwnerConsume.consumeData_spec msg src ds)

end Leanux.Proofs.WG.OwnerChecks
