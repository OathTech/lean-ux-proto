import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.KeyCollision

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setDevice_private_changed_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice (requestGeneration d) key) d.peerList final) := by
  have hl := lookupInterface_index d
  have hc := (returns_iff _ _ _).mp
    (keyCollision_absent (requestGeneration d) key (by simpa [noKeyCollision, requestGeneration] using absent))
  have hi := (ensures_iff _ _ _).mp (keyInstall_complete (requestGeneration d) key)
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, ← devicePrivate_source]
  simp [devicePrivateSource, devicePeersSource, privateKeyAttrs, branch, bind_assoc,
    WG.andM, WG.orM, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hc, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [changed, requestGeneration, requestsStagedSend]
  all_goals subst_vars
  all_goals simp_all
  all_goals grind only

end Leanux.Proofs.WG.Config
