import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.SocketPorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem hidden_portBound (bound : Nat → Bool) (site : HiddenSite) :
    ⦃fun w => ⌜w.portBound = bound⌝⦄ hidden site
    ⦃⇓? _ w => ⌜w.portBound = bound⌝⦄ := by
  mvcgen [hidden, skipAmbient, noteNetRxStart]

theorem clearEndpointSource_portBound (pid : PeerId) (bound : Nat → Bool) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.portBound = bound)
      (fun _ w => w.portBound = bound) := by
  have hh := hidden_portBound bound
  rw [ensures_iff]
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, hiddenJiffies,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hh]

def portClearLoop (pids : List PeerId) : M Unit := do
  for pid in pids do
    _ ← branch .setPortPeerIter true
    clearPeerEndpointSrc pid

theorem portClearLoop_effects (initial : Device) (pids seen : List PeerId)
    (frame : Option Device) (bound : Nat → Bool) :
    Ensures (portClearLoop pids)
      (fun w => w.k.wg.map withoutPeers = frame ∧ clearedPeers initial w.k seen ∧ w.portBound = bound)
      (fun _ w => w.k.wg.map withoutPeers = frame ∧
        clearedPeers initial w.k (seen ++ pids) ∧ w.portBound = bound) := by
  induction pids generalizing seen with
  | nil =>
    rw [ensures_iff]
    simp [portClearLoop]
    mvcgen
  | cons pid rest ih =>
    have factor : portClearLoop (pid :: rest) = (do
        _ ← branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        portClearLoop rest) := by
      simp [portClearLoop, List.forIn_cons, bind_assoc]
    have hc : ⦃fun w => ⌜w.k.wg.map withoutPeers = frame ∧
        clearedPeers initial w.k seen ∧ w.portBound = bound⌝⦄ clearPeerEndpointSrc pid
        ⦃⇓? _ w => ⌜w.k.wg.map withoutPeers = frame ∧
          clearedPeers initial w.k (seen ++ [pid]) ∧ w.portBound = bound⌝⦄ := by
      rw [← ensures_iff]
      intro w ret v h hr
      obtain ⟨hf, he⟩ := (ensures_iff _ _ _).mpr
        (clearEndpointSource_effects_frame initial pid seen frame) w ret v ⟨h.1, h.2.1⟩ hr
      exact ⟨hf, he, clearEndpointSource_portBound pid bound w ret v h.2.2 hr⟩
    have ht := (ensures_iff _ _ _).mp (ih (seen ++ [pid]))
    rw [factor, ensures_iff]
    mvcgen [branch, hc, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [List.append_assoc]

def socketOutcome (d : Device) (port : Nat) (bound : Nat → Bool) : Int × Device :=
  if !d.creatingNet then (-ENONET, d)
  else if bound port || d.sock4 == some port || d.sock6 == some port then (-EADDRINUSE, d)
  else (0, { d with sock4 := some port, sock6 := some port, incomingPort := port })

theorem socketInit_nonzero_projected (d initial : Device) (seen : List PeerId)
    (port : Nat) (nonzero : port ≠ 0) (bound : Nat → Bool) :
    ⦃fun w => ⌜w.k.wg.map withoutPeers = some (withoutPeers d) ∧
      clearedPeers initial w.k seen ∧ w.portBound = bound⌝⦄ socketInit port
    ⦃⇓? ret w => ⌜ret = (socketOutcome d port bound).1 ∧
      w.k.wg.map withoutPeers = some (withoutPeers (socketOutcome d port bound).2) ∧
      clearedPeers initial w.k seen⌝⦄ := by
  simp [socketInit, nonzero]
  mvcgen [socketReinit, sockFree, iputReport, branch,
    getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, socketOutcome, clearedPeers]
  all_goals grind only

def setPortSource (port : Nat) : M Int := do
  let d ← getDev
  if ← branch .setPortSame (d.incomingPort == port) then return 0
  portClearLoop d.peerList
  _ ← branch .setPortPeerIter false
  if ← branch .setPortNotRunning !d.running then
    modifyDev fun d => { d with incomingPort := port }
    return 0
  socketInit port

theorem setPort_source (port : Nat) : setPortSource port = setPort port := by
  simp [setPortSource, setPort, portClearLoop, bind_assoc]

def portOutcome (d : Device) (port : Nat) (bound : Nat → Bool) : Int × Device :=
  if !d.running then (0, { d with incomingPort := port })
  else socketOutcome d port bound

theorem setPort_nonzero_effects (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) :
    Ensures (setPort port) (fun w => w.k.wg = some d ∧ w.portBound = bound)
      (fun ret w => if d.incomingPort = port then ret = 0 ∧ w.k.wg = some d
        else ret = (portOutcome d port bound).1 ∧
          w.k.wg.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧
          clearedPeers d w.k d.peerList) := by
  have hc := fun pids => (ensures_iff _ _ _).mp
    (portClearLoop_effects d pids [] (some (withoutPeers d)) bound)
  have hs := socketInit_nonzero_projected d d d.peerList port nonzero bound
  rw [← setPort_source, ensures_iff]
  mvcgen [setPortSource, getDev, getK, modifyDev, modifyK, branch, invariant, hc, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  case vc3.h_1.isFalse.post.success.isTrue =>
    obtain ⟨hf, he⟩ := (show Option.map withoutPeers _ = some _ ∧ _ from by assumption)
    obtain ⟨current, hw, hf⟩ := Option.map_eq_some_iff.mp hf
    simp_all [withoutPeers, portOutcome, clearedPeers]
  all_goals simp_all [withoutPeers, portOutcome, clearedPeers, Option.map_map, Option.bind_map, Function.comp_def]
  all_goals grind only

end Leanux.Proofs.WG.Config
