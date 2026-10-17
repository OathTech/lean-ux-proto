import Leanux.Proofs.WG.Config.MixedAttributeModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Pointwise effect of the actual captured clear list, including repeated
visits. Each visited peer retains its resulting reset timestamp. -/
def ClearedPeerStore (initial current : Device) (seen : List PeerId) : Prop :=
  ∀ q, if q ∈ seen then
    ∃ p reset, initial.peers[q]? = some p ∧ current.peers[q]? = some (clearedSource p reset)
  else current.peers[q]? = initial.peers[q]?

/-- Actual clear-prefix device followed by the existing ordered scalar writes.
The prefix is not assumed successful: this describes its normal-run effect. -/
def MultiMixedEffect (d : Device) (mark : Nat) (pid : PeerId) (psk : Key)
    (interval : Nat) (final : Device) : Prop :=
  ∃ cleared selected, withoutPeers cleared = withoutPeers (mixedFwmarkBase d mark) ∧
    ClearedPeerStore d cleared d.peerList ∧ cleared.peers[pid]? = some selected ∧
    final = scalarDevice cleared pid selected psk interval


end Leanux.Proofs.WG.Config
