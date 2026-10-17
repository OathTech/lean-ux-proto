import Leanux.Proofs.WG.Config.DeviceScalars

/-! Pure request and committed-prefix device for a mixed port refusal. -/

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

def portRefusalAttrs (d : Device) (mark port : Nat) (flags : Option UInt32)
    (key : Option Key) (peers : Option (List PeerEntry)) : DeviceAttrs :=
  {device := byIndex d, flags, fwmark := some mark, listenPort := some port,
    privateKey := key, peers}

def portRefusalBase (d : Device) (mark : Nat) : Device :=
  {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1}

end Leanux.Proofs.WG.Config
