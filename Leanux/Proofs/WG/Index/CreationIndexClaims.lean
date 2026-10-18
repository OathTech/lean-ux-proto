import Leanux.Proofs.WG.Index.CreationIndexModel
import Leanux.Proofs.WG.Index.CreationIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

/-- Original peer creation preserves hashed-slot and retirement relations on
every normal result. Cursor vacancy is derived from configured entry bounds;
no store-absence, successful-creation, or record-readiness premise is supplied. -/
theorem peerCreate_hashSlots_retirement
    (publicKey : Key) (psk : Option Key) (retired : Reservations) :
    Campaign2.Ensures (peerCreate publicKey psk)
      (fun s => View.ConfiguredSafe s ∧ View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) :=
  peerCreate_hashSlots_retirement_source publicKey psk retired
end Leanux.Proofs.WG.Index
