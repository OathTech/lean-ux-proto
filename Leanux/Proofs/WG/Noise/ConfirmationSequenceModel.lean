import Leanux.Proofs.WG.Noise.RotationModel

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- The first initial-next match is the only successful confirmation. Before
and after lists describe the input, not another execution model. The successful
case retains the existing ordered confirmation effect, including aliased puts. -/
def ConfirmationSequenceEffect (pid : PeerId) (ids : List KeypairId)
    (initial : Device) (p : Peer) (results : List Bool) (final : Device) : Prop :=
  (results = List.replicate ids.length false ∧ final = initial ∧
    ∀ id ∈ ids, p.keypairNext ≠ some id) ∨
  ∃ before matched after,
    ids = before ++ matched :: after ∧
    (∀ id ∈ before, p.keypairNext ≠ some id) ∧
    p.keypairNext = some matched ∧
    results = List.replicate before.length false ++ true :: List.replicate after.length false ∧
    ConfirmationEffect pid matched initial p true final ∧
    ∃ caller, final.peers[pid]? = some caller ∧ caller.keypairNext = none

end Leanux.Proofs.WG.Noise
