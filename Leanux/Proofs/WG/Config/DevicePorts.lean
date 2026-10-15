import Leanux.Proofs.WG.Config.RunningPort

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def portAttrs (d : Device) (port : Nat) : DeviceAttrs :=
  { device := byIndex d, listenPort := some port }

theorem lookupInterface_index_bound (d : Device) (bound : Nat → Bool) :
    ⦃fun w => ⌜w.k.wg = some d ∧ selectsDevice w d ∧ w.portBound = bound⌝⦄ lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.k.wg = some d ∧ w.portBound = bound⌝⦄ := by
  mvcgen [lookupInterface, byIndex, netDevices, getK, branch, Leanux.WG.orM, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [selectsDevice, -List.find?_eq_none]
  all_goals grind only

theorem setDevice_port_nonzero (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (net : d.creatingNet = true) (bound : Nat → Bool) :
    Ensures (wgSetDevice (portAttrs d port))
      (fun w => w.k.wg = some d ∧ selectsDevice w d ∧ w.portBound = bound)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        if d.incomingPort = port then ret = 0 ∧ w.k.wg = some updated
        else ret = (portOutcome updated port bound).1 ∧
          w.k.wg.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
          clearedPeers d w.k d.peerList) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index_bound d bound
  have hp := (ensures_iff _ _ _).mp (setPort_nonzero_effects updated port nonzero bound)
  rw [← wgSetDevice_source, ensures_iff]
  simp [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, devicePeersSource,
    portAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, clearedPeers]
  all_goals grind only

end Leanux.Proofs.WG.Config
