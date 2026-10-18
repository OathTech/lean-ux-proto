import Leanux.Proofs.WG.Index.InitializedBoundsEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedBounds
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-! Frames: concrete observations are projected once, without replaying a call
or manufacturing a state for an error result. -/
theorem currentSlots_session_fresh (w : WGWorld) (d : Device) (pid : PeerId)
    (p : Peer) (slots : CurrentSlots.Inv w) (device : w.dev = some d)
    (resident : d.peers[pid]? = some p) :
    SessionRotationFresh p d.nextKeypairId :=
  slots_session_fresh d pid p
    (slots (Affiliation.state d) (by simp [Affiliation.view,device])) resident

theorem allocation_hashed_bound (w : WGWorld) (history : List LifetimeEvent)
    (d : Device) (allocation : AllocationInv history w) (device : w.dev = some d)
    (coherent : HashedOwnersCoherent d) : KeypairOwnersBounded d :=
  store_hashed_bound d (allocation.keySlots d device) coherent

theorem holder_entry_bounds (cs : Ledger) (loans : Reservations)
    (history : List RxHistory.Event) (w : World) (d : Device)
    (entry : HolderEntry.Inv cs loans history w) (device : w.wg.dev = some d) :
    EndpointBounds d := by
  have auxiliary := HolderEntry.to_aux entry (by simp [device])
  have allocation := auxiliary.2.1.allocation
  exact ⟨auxiliary.2.2 (Affiliation.state d) (by simp [Affiliation.view,device]),
    allocation.peerSlots d device,allocation.keySlots d device⟩

theorem holder_entry_projection (cs : Ledger) (loans : Reservations)
    (history : List RxHistory.Event) (w : World)
    (entry : HolderEntry.Inv cs loans history w) :
    EndpointSafe (Campaign2.snapshot w.wg w.ambient) := by
  intro d device
  exact holder_entry_bounds cs loans history w d entry device


end Leanux.Proofs.WG.Index.InitializedBounds
