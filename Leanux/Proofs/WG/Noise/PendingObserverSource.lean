import Leanux.Proofs.WG.Noise.PendingInvariantFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Observer transport separates exact outcome erasure, append-only journaling,
all-outcome confirmation-label silence, and normal original-call effects. -/
theorem observer {α : Type} (g : RxHistory.Obs α) (action : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g action)
    (labels : ∀ w h, CounterConsume.confirmationLabels (runPrefix g w h).2 =
      CounterConsume.confirmationLabels h)
    (normal : ∀ seen, Preserves (fun w : World => NativeInv w.wg seen) action) :
    PrefixPreserves StateInv HistorySafe g := by
  intro w h hi
  obtain ⟨suffix,appended⟩ := appends w h
  refine ⟨suffix,appended,?_,?_⟩
  · change (CounterConsume.confirmationLabels (runPrefix g w h).2).reverse.Nodup
    rw [labels]
    exact hi.2.2.distinct
  · cases outcome : (runPrefix g w h).1 with
    | error stop => trivial
    | ok out =>
      change NativeInv out.2.wg (CounterConsume.confirmationLabels (runPrefix g w h).2).reverse
      rw [labels]
      exact (hoare_iff_run _ _ _).mp (normal _) w out.1 out.2 hi
        ((erases w h).symm.trans outcome)

theorem native_product {α : Type} (action : WG.M α)
    (normal : ∀ seen, Preserves (fun w => NativeInv w seen) action)
    (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value final hi original
  rw [liftWG_run] at original
  cases run : (action.run w.wg).run w.ambient with
  | error stop => simp [run,Except.map] at original
  | ok result =>
    rcases result with ⟨⟨value,g⟩,after⟩
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at original
    obtain ⟨rfl,rfl⟩ := original
    exact (hoare_iff_run_ambient _ _ _).mp (normal seen)
      w.wg w.ambient value g after hi run

end Leanux.Proofs.WG.Noise.PendingSession

