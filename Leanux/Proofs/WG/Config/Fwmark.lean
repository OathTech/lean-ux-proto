import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.EndpointSources
import Leanux.Proofs.WG.Config.DeviceScalars

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def fwmarkAttrs (d : Device) (mark : Nat) : DeviceAttrs :=
  { device := byIndex d, fwmark := some mark }

theorem setDevice_fwmark_frame (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 })) := by
  let updated := withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hc := fun pid => clearEndpointSource_device_frame pid (some updated)
  rw [← wgSetDevice_source, ensures_iff]
  simp [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, devicePeersSource,
    fwmarkAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [Leanux.WG.orM, Leanux.WG.andM, branch, getDev, getK,
    modifyDev, modifyK, invariant, hl, hc]
  invariants
  | inv1 => ((⇓? _ w => ⌜w.k.wg.map withoutPeers = some updated⌝) :
      PostCond _ (.arg World (.except Stop .pure)))
  | inv2 => ((⇓? _ w => ⌜w.k.wg.map withoutPeers = some updated⌝) :
      PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, updated, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals grind only

end Leanux.Proofs.WG.Config
