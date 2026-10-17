import Leanux.Proofs.WG.Config.ScalarGetterFrames
import Leanux.Proofs.WG.Config.Model

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

def mixedFwmarkAttrs (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) : DeviceAttrs :=
  {scalarDeviceAttrs d key psk interval bad with fwmark := some mark}

def mixedFwmarkBase (d : Device) (mark : Nat) : Device :=
  {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1}

def mixedFwmarkPeer (p : Peer) (psk : Key) (interval : Nat) (reset : UInt64) : Peer :=
  {clearedSource p reset with presharedKey := psk, persistentKeepaliveInterval := interval}

def MixedFwmarkEffect (d : Device) (mark : Nat) (pid : PeerId) (p : Peer)
    (psk : Key) (interval : Nat) (reset : UInt64) (final : Device) : Prop :=
  withoutPeers final = withoutPeers (mixedFwmarkBase d mark) ∧
  final.peers[pid]? = some (mixedFwmarkPeer p psk interval reset) ∧
  ∀ q, q ≠ pid → final.peers[q]? = d.peers[q]?

end Leanux.Proofs.WG.Config
