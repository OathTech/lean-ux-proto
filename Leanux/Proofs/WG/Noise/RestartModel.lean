import Leanux.Proofs.WG.Campaign2.View

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- The tracked next slot satisfies a predicate whenever the peer survives.
Deletion is permitted; this says nothing about residency of the named key. -/
def RestartDevice (tracked : PeerId) (cursor : Nat) (allowed : Option KeypairId → Prop)
    (d : Device) : Prop :=
  d.nextKeypairId = cursor ∧ ∀ p, d.peers[tracked]? = some p → allowed p.keypairNext

end Leanux.Proofs.WG.Noise
