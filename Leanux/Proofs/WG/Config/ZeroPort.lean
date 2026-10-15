import Leanux.Proofs.WG.Config.RandomPort
import Leanux.Proofs.WG.Config.DevicePorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem hiddenUdp_range (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hidden .udpPortDraw
    ⦃⇓? bs w => ⌜P w.k ∧
      LOCAL_PORT_LOW ≤ randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0) ∧
      randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0) ≤ LOCAL_PORT_HIGH⌝⦄ := by
  rw [← ensures_iff]
  intro w bs v hp hr
  obtain ⟨hp, hlen⟩ := (ensures_iff _ _ _).mpr (hiddenUdp_shape P) w bs v hp hr
  have hb := littleEndian_bound bs
  rw [hlen] at hb
  exact ⟨hp, randomPortFirst_range _ hb⟩

theorem socketInit_zero_projected (d initial : Device) (seen : List PeerId)
    (net : d.creatingNet = true) :
    ⦃fun w => ⌜w.k.wg.map withoutPeers = some (withoutPeers d) ∧ clearedPeers initial w.k seen⌝⦄ socketInit 0
    ⦃⇓? ret w => ⌜ret = 0 ∧ clearedPeers initial w.k seen ∧ ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      w.k.wg.map withoutPeers = some (withoutPeers
        { d with sock4 := some port, sock6 := some port, incomingPort := port })⌝⦄ := by
  have hh := hiddenUdp_range (fun k =>
    k.wg.map withoutPeers = some (withoutPeers d) ∧ clearedPeers initial k seen)
  simp [socketInit]
  mvcgen [socketReinit, sockFree, iputReport, branch,
    getDev, getK, modifyDev, modifyK, invariant, unsupported, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, clearedPeers]
  all_goals grind only

def zeroPortEffects (d : Device) (w : World) : Prop :=
  if d.incomingPort = 0 then w.k.wg = some d
  else clearedPeers d w.k d.peerList ∧
    if d.running then ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      w.k.wg.map withoutPeers = some (withoutPeers
        { d with sock4 := some port, sock6 := some port, incomingPort := port })
    else w.k.wg.map withoutPeers = some (withoutPeers { d with incomingPort := 0 })

theorem setPort_zero_bound (d : Device) (net : d.creatingNet = true) (bound : Nat → Bool) :
    Ensures (setPort 0) (fun w => w.k.wg = some d ∧ w.portBound = bound)
      (fun ret w => ret = 0 ∧ zeroPortEffects d w) := by
  have hc := fun pids => (ensures_iff _ _ _).mp
    (portClearLoop_effects d pids [] (some (withoutPeers d)) bound)
  have hs := socketInit_zero_projected d d d.peerList net
  rw [← setPort_source, ensures_iff]
  mvcgen [setPortSource, getDev, getK, modifyDev, modifyK, branch, invariant, hc, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  case vc3.h_1.isFalse.post.success.isTrue =>
    obtain ⟨hf, he⟩ := (show Option.map withoutPeers _ = some _ ∧ _ from by assumption)
    obtain ⟨current, hw, hf⟩ := Option.map_eq_some_iff.mp hf
    simp_all [withoutPeers, zeroPortEffects, clearedPeers]
  all_goals simp_all [withoutPeers, zeroPortEffects, clearedPeers, Option.map_map, Option.bind_map, Function.comp_def]
  all_goals grind only

theorem setPort_zero_effects (d : Device) (net : d.creatingNet = true) :
    Ensures (setPort 0) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ zeroPortEffects d w) := by
  intro w ret v hp hr
  exact setPort_zero_bound d net w.portBound w ret v ⟨hp, rfl⟩ hr

theorem setDevice_port_zero (d : Device) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (portAttrs d 0))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ zeroPortEffects
        { d with deviceUpdateGen := d.deviceUpdateGen + 1 } w) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hp := (ensures_iff _ _ _).mp (setPort_zero_effects updated net)
  rw [← wgSetDevice_source, ensures_iff]
  simp [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, devicePeersSource,
    portAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, zeroPortEffects]
  all_goals grind only

end Leanux.Proofs.WG.Config
