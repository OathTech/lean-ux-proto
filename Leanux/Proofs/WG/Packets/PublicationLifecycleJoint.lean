import Leanux.Proofs.WG.Packets.PublicationRemovalObserved
import Leanux.Proofs.WG.Packets.PublicationTimers
import Leanux.Proofs.WG.Packets.PublicationJoint

/-! Removal and timer callbacks preserve the existing positional packet
certificates as well as their native state. The unchanged consumed-event
projection is taken from the actual lifetime-only journal focus. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues

/-- Add the incoming positional certificates to a concrete owner/frontier
observer contract when that same execution emits no consumed event. -/
theorem checked_quiet (g : RxHistory.Obs α)
    (checked : PrefixPreserves
      (fun h w => OwnerChecks.Inv h w ∧ PublicationFrontier.Inv h w.wg) OwnerChecks.Safe g)
    (appends : Appends g) (frame : HistoryFrame PublicationChecks.sensitive g) :
    Preserves g := by
  intro w h hi
  obtain ⟨suffix,hs,ownerSafe,normal⟩ := checked w h ⟨hi.1,hi.2.1⟩
  have certificates := PublicationChecks.Safe.of_unchanged (w := w) g appends frame hi.2.2
  refine ⟨suffix,hs,⟨ownerSafe,certificates⟩,?_⟩
  cases outcome : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    rw [outcome] at normal
    exact ⟨normal.1,normal.2,certificates⟩

theorem removalCall (call : PeerRemovalCall) :
    Preserves (RxHistory.mixed (liftWGObserver call.observed)) :=
  checked_quiet _ (PublicationFrontier.removalCall_checked call) (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      PublicationChecks.sensitive (fun _ => rfl) _)

theorem timerCallback (pid : PeerId) (timer : PeerTimer) :
    Preserves (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) :=
  checked_quiet _ (PublicationFrontier.timerCallback_checked pid timer) (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      PublicationChecks.sensitive (fun _ => rfl) _)

end Leanux.Proofs.WG.PublicationJoint
