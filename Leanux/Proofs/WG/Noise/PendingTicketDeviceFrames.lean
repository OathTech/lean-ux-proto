import Leanux.Proofs.WG.Noise.PendingInvariantFrames
import Leanux.Proofs.WG.Queues.DeviceAuxEntry
import Leanux.Proofs.WG.Index.LinkSource
import Leanux.Proofs.WG.Keypairs.Frames.WGDevice

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do

theorem link_view (w : WGWorld) : storeView (linkView w) = view w := by
  simp [storeView,linkView,linkStore,wgStoreView,view,pending,linkDevice,
    Option.bind_map,Function.comp_def]

/-- Newlink changes registration fields, not the pending allocation tickets. -/
theorem wgNewlink_frame : SameView view wgNewlink := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient ret v after run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgNewlink_endpoint (linkView w))
    w ambient ret v after rfl run
  rcases endpoint with ⟨_,same⟩ | ⟨_,fresh⟩
  · simpa only [link_view] using congrArg storeView same
  · have observed := congrArg storeView fresh
    rw [link_view] at observed
    simpa [storeView,registeredLink,linkView,linkStore,linkDevice,wgStoreView,
      view,pending,Option.bind_map,Function.comp_def] using observed

/-- Guarded creation either keeps its device or starts with empty pending
slots. The allocation counter belongs to the persistent WireGuard world. -/
theorem wgCreate_retained : RetainsCall wgCreate := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient ret v after run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient ret v after rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have observed := congrArg storeView same
    simp only [link_view] at observed
    rw [observed]
    exact Retained.refl _
  · have observed := congrArg storeView fresh
    rw [link_view] at observed
    refine ⟨congrArg WGStoreView.keypairCounter fresh,?_⟩
    intro pid stamp present
    rw [observed] at present
    simp [storeView,registeredLink,setupLink,linkDevice,pending] at present

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do

theorem create (seen : List Nat) :
    Ensures wgCreate (fun w => NativeInv w seen) (fun _ w => NativeInv w seen) := by
  apply native_retained wgCreate _ PendingTickets.wgCreate_retained seen
  intro w ambient result final after hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp Queues.RxCredits.DeviceAuxEntry.create_configured
      w ambient result final after hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp Queues.RxCredits.DeviceAuxEntry.create_slots
      w ambient result final after hi.2 run⟩

/-- An absent final device carries no pending slot. A monotone allocation
frontier suffices to retain the previously confirmed identities. -/
theorem absent (w v : WGWorld) (seen : List Nat) (hi : NativeInv w seen)
    (empty : v.dev = none) (counter : w.keypairCounter ≤ v.keypairCounter) : NativeInv v seen := by
  refine ⟨?_,?_,?_,?_,hi.2.2.distinct,?_,?_⟩
  · simp [ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,empty]
  · simp [CurrentSlots.Inv,Affiliation.view,empty]
  · intro pid stamp resident
    simp [PendingTickets.view,empty] at resident
  · intro pid other stamp resident
    simp [PendingTickets.view,empty] at resident
  · intro stamp member
    exact Nat.le_trans (hi.2.2.past stamp member) counter
  · intro stamp member pid resident
    simp [PendingTickets.view,empty] at resident

theorem destruct (seen : List Nat) :
    Ensures wgDestruct (fun w => NativeInv w seen) (fun _ w => NativeInv w seen) := by
  intro w ambient result final after hi run
  apply absent w final seen hi (Index.wgDestruct_absent w ambient result final after trivial run)
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp Keypairs.WGDevice.wgDestruct_ordinary
    w ambient result final after run).frontier_mono

theorem delete (seen : List Nat) :
    Ensures (wgDelete : WG.M Int) (fun w => NativeInv w seen) (fun _ w => NativeInv w seen) := by
  intro w ambient result final after hi run
  apply absent w final seen hi (Index.wgDelete_absent w ambient result final after trivial run)
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp Keypairs.WGDevice.wgDelete_ordinary
    w ambient result final after run).frontier_mono

end Leanux.Proofs.WG.Noise.PendingSession
