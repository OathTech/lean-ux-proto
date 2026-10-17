import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.AllocationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Allocation cannot overwrite a hashed keypair owner when that owner lies
below the allocation cursor. Unhashed allocations need no peer-word premise. -/
theorem created_owner_coherent (d : Device) (counter : Nat) (peer : Option PeerId)
    (bounded : KeypairOwnersBounded d) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (createdDevice d counter peer) := by
  intro e member
  have old := coherent e member
  cases owner : e.owner with
  | handshake pid =>
    simpa [OwnerCoherent, owner, ownerWord, createdDevice] using old
  | keypair id =>
    have below := bounded e member id owner
    have different : d.nextKeypairId ≠ id := (Nat.ne_of_lt below).symm
    simpa [OwnerCoherent, owner, ownerWord, createdDevice,
      Std.TreeMap.getElem?_insert, different] using old

end Leanux.Proofs.WG.Index
