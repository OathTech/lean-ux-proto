import Leanux.Proofs.WG.Config.MultiMixedModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The ordered scalar update changes no field outside the peer store. -/
theorem multiMixedEffect_outer (d final : Device) (mark : Nat) (pid : PeerId)
    (psk : Key) (interval : Nat) (effect : MultiMixedEffect d mark pid psk interval final) :
    withoutPeers final = withoutPeers (mixedFwmarkBase d mark) := by
  obtain ⟨cleared,selected,outer,_,_,rfl⟩ := effect
  simpa only [scalarDevice,withPeer,withoutPeers] using outer


end Leanux.Proofs.WG.Config
