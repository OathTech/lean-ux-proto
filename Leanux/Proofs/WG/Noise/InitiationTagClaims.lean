import Leanux.Proofs.WG.Noise.InitiationTagSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Actual initiation consumption changes only the returned peer's tag. A
normal refusal preserves all tags; successful restarts accept every old tag. -/
theorem consumeInitiation_tagMap_projected (msg : List UInt8) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeInitiation msg) (fun s => s = entry)
      (fun result after => ∀pid, after.tagAt pid = if result = some pid then
        some HANDSHAKE_CONSUMED_INITIATION else entry.tagAt pid) := by
  intro g ambient result final after pre run pid
  rw [← pre]
  exact consumeInitiation_tagMap msg g.dev g ambient result final after rfl run pid

end Leanux.Proofs.WG.Noise
