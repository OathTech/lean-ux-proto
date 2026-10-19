import Leanux.WG.Peer

/-! Exact source equations for the local index-unhash action and its recorded
decision. The missing-device guard belongs to the liftIndex adapter. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG

def indexUnhash (d : Decision) (hashed : IndexEntry → Bool) : IndexM Unit := do
  _ ← branch d ((← get).any hashed)
  modify fun entries => entries.filter fun e => !hashed e

theorem indexRemove_eq (owner : IndexOwner) :
    indexRemove owner = indexUnhash .idxRemoveHashed
      (fun e => e.owner == owner) := rfl

end Leanux.Proofs.Framing
