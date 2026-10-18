import Leanux.Proofs.WG.Noise.PendingSessionSource
import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Normal state transport separates the pre-existing identity/slot obligations
from retention of pending allocation identities. -/
theorem native_retained {α : Type} (action : WG.M α)
    (core : Ensures action (fun w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w)
      (fun _ w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w))
    (pending : PendingTickets.RetainsCall action) (seen : List Nat) :
    Ensures action (fun w => NativeInv w seen) (fun _ w => NativeInv w seen) := by
  intro w ambient result final after hi run
  have invariant := core w ambient result final after ⟨hi.1,hi.2.1⟩ run
  have retained := (ProjectedAction.iff_run_ambient _ _ _).mp
    pending w ambient result final after run
  exact ⟨invariant.1,invariant.2,hi.2.2.retained retained⟩

theorem core_of_frames {α : Type} (action : WG.M α)
    (configured : SameView ConfiguredIdentity.view action)
    (slots : Ensures action (fun w => CurrentSlots.Inv w ∧ ConfiguredIdentity.Inv w)
      (fun _ w => CurrentSlots.Inv w)) :
    Ensures action (fun w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w)
      (fun _ w => ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w) := by
  intro w ambient result final after hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    configured w ambient result final after run
  exact ⟨fun s hs => hi.1 s (same.symm.trans hs),
    slots w ambient result final after ⟨hi.2,hi.1⟩ run⟩

theorem native_store (w v : WGWorld) (seen : List Nat)
    (same : wgStoreView v = wgStoreView w) (hi : NativeInv w seen) : NativeInv v seen := by
  have device := congrArg WGStoreView.dev same
  have counter := congrArg WGStoreView.keypairCounter same
  change v.dev = w.dev at device
  change v.keypairCounter = w.keypairCounter at counter
  simpa only [NativeInv,ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,CurrentSlots.Inv,
    Affiliation.view,PendingTickets.view,device,counter] using hi

/-- The actual initialized WG fixture establishes the supplied history invariant
with an empty confirmation journal. No accepted-trace premise is needed. -/
theorem native_initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    NativeInv w [] := by
  refine ⟨ConfiguredMaintenance.configured_initial net bare w same,
    CurrentSlots.initial net bare w same,?_⟩
  have pending := congrArg PendingTickets.storeView same
  change PendingTickets.view w = PendingTickets.view (Runner.initialWG net bare) at pending
  rw [pending,PendingTickets.view_initial]
  exact PendingTickets.empty_initial 0

theorem quiet_native {α : Type} (action : WG.M α)
    (normal : ∀ seen, Ensures action (fun w => NativeInv w seen) (fun _ w => NativeInv w seen)) :
    StatePrefixPreserves
      (fun h w _ => NativeInv w (CounterConsume.confirmationLabels h).reverse)
      HistorySafe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h w ambient hi
    exact hi.2.2.distinct
  · intro h w ambient result final after hi run
    exact normal _ w ambient result final after hi run

theorem quiet {α : Type} (action : WG.M α)
    (normal : ∀ seen, Ensures action (fun w => NativeInv w seen) (fun _ w => NativeInv w seen)) :
    PrefixPreserves StateInv HistorySafe (liftWGObserver (liftWGPrefix action)) :=
  (quiet_native action normal).liftWGObserver

theorem state_store (h : List RxHistory.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : StateInv h w) : StateInv h v :=
  native_store w.wg v.wg _ same hi

end Leanux.Proofs.WG.Noise.PendingSession
