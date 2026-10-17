import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Each slot clear writes the current resident peer before its actual keypair
put. Coherence is retained through the evolving states, including aliased slots. -/
theorem clearRun_owner_coherent {pid : PeerId} {d final : Device}
    {slots : List ClearSlot} (steps : ClearRun pid d slots final)
    (coherent : HashedOwnersCoherent d) : HashedOwnersCoherent final := by
  have putPreserves {key : Option KeypairId} {start stop : Device}
      (put : ClearPut key start stop) (safe : HashedOwnersCoherent start) :
      HashedOwnersCoherent stop := by
    cases put with
    | null => exact safe
    | present d id k resident live word =>
      exact releasedDevice_owner_coherent _ id k true resident live safe
  induction steps with
  | nil => exact coherent
  | cons d slot p middle final rest resident put tail ih =>
    have written : HashedOwnersCoherent (clearWrite d pid slot p) := by
      apply peerWrite_owner_coherent d pid p (slot.clear p) resident
      · cases slot <;> rfl
      · cases slot <;> rfl
      · exact coherent
    exact ih (putPreserves put written)

end Leanux.Proofs.WG.Index
