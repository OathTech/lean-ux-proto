import Leanux.Proofs.WG.Noise.ResponseTagSource
import Leanux.Proofs.WG.Noise.ResponseEdgeClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Whole response consumption changes only its returned peer's tag. All
normal refusals preserve every optional tag, and actual successful lookup
provides the retained cleanup reference without an entry budget. -/
theorem consumeResponse_tagMap_projected (msg : List UInt8) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeResponse msg) (fun s => s = entry)
      (fun result after =>
        (∀pid, after.tagAt pid = if result = some pid then
          some HANDSHAKE_CONSUMED_RESPONSE else entry.tagAt pid) ∧
        (∀pid, result = some pid → entry.tagAt pid = some HANDSHAKE_CREATED_INITIATION)) := by
  intro g ambient result final after pre run
  have tags := consumeResponse_tagMap msg g.dev g ambient result final after rfl run
  have edge := consumeResponse_entry_edge msg entry g ambient result final after pre run
  constructor
  · intro pid
    rw [← pre]
    exact tags pid
  · intro pid returned
    exact (edge pid returned).1


end Leanux.Proofs.WG.Noise
