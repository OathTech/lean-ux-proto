import Leanux.Proofs.WG.Noise.CreationTagSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- The actual creator changes only its own tag on success. All normal
refusals retain the complete optional tag map, without entry assumptions. -/
theorem createInitiation_tagMap_projected (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (createInitiation pid) (fun s => s = entry)
      (fun result after => (∀target, after.tagAt target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_INITIATION else entry.tagAt target
        else entry.tagAt target)) := by
  intro g ambient result final after pre run
  rw [← pre]
  exact createInitiation_tagMap pid g.dev g ambient result final after rfl run

/-- The actual creator changes only its own tag on success. All normal
refusals retain the complete optional tag map, without entry assumptions. -/
theorem createResponse_tagMap_projected (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (createResponse pid) (fun s => s = entry)
      (fun result after => (∀target, after.tagAt target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_RESPONSE else entry.tagAt target
        else entry.tagAt target) ∧
        (result.isSome → entry.tagAt pid = some HANDSHAKE_CONSUMED_INITIATION)) := by
  intro g ambient result final after pre run
  rw [← pre]
  exact createResponse_tagMap pid g.dev g ambient result final after rfl run

end Leanux.Proofs.WG.Noise
