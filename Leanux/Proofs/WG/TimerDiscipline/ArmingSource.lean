import Leanux.Proofs.WG.TimerDiscipline.ArmingClaims
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Noise.Slots
import Leanux.WG.Timers
import Leanux.Proofs.WG.TimerDiscipline.ArmingBaseSource

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem modPeerTimer_effect (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimer site pid timer delay) (fun w => w.k.wg = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧
        if ok then ∃ expiry, peerAt w pid = some (p.setTimer timer (some expiry))
        else peerAt w pid = some p) := by
  rw [ensures_iff]
  have hh := hidden_kernel_spec (fun k => k.wg = some d)
  mvcgen [modPeerTimer, callerJiffies, hiddenJiffies, modPeerTimerGuard,
    Leanux.WG.andM, armTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, invariant, unsupported, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind only

theorem timersTraversal_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersTraversal pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false
        then ∃ expiry, peerAt w pid = some (p.setTimer .persistentKeepalive (some expiry))
        else peerAt w pid = some p) := by
  rw [ensures_iff]
  have hm := fun site timer delay => (ensures_iff _ _ _).mp
    (modPeerTimer_effect site pid timer delay d p resident)
  have hd := fun site timer delay => map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ (hm site timer delay)
  simp only [timersTraversal, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [getPeer, getDev, getK, branchCmp, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]
  all_goals first | exact hd _ (by assumption) | exact hd _ _ _ _ (by assumption) | grind only

theorem timersSessionDerived_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersSessionDerived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running && !p.isDead
        then ∃ expiry, peerAt w pid = some (p.setTimer .zeroKeyMaterial (some expiry))
        else peerAt w pid = some p) := by
  rw [ensures_iff]
  have hm := (ensures_iff _ _ _).mp
    (modPeerTimer_effect .timerJiffiesSessionDerived pid .zeroKeyMaterial
      ZERO_KEY_MATERIAL_TICKS d p resident)
  have hd := map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  simp only [timersSessionDerived, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals first | exact hd _ (by assumption) | exact hd _ _ _ _ (by assumption) | grind only


theorem timersDataReceived_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersDataReceived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running then
        if p.timerPending .sendKeepalive then
          peerAt w pid = some { p with timerNeedAnotherKeepalive := true }
        else if p.isDead then peerAt w pid = some p
        else ∃ expiry, peerAt w pid = some (p.setTimer .sendKeepalive (some expiry))
        else peerAt w pid = some p) := by
  rw [ensures_iff]
  have hm := (ensures_iff _ _ _).mp
    (modPeerTimer_effect .timerJiffiesDataReceived pid .sendKeepalive
      KEEPALIVE_TIMEOUT_TICKS d p resident)
  have hd := map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  simp only [timersDataReceived, Functor.discard, Functor.mapConst, Function.const]
  mvcgen [getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, Std.TreeMap.getElem?_insert]
  all_goals first | exact hd _ (by assumption) | grind only

theorem timersHandshakeComplete_effect (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Ensures (timersHandshakeComplete pid site) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ now, peerAt w pid = some
        { (p.setTimer .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false, walltimeLastHandshake := now }) := by
  let finish : M Unit := do
    modifyPeer pid (fun p => p.setTimer .retransmitHandshake none)
    modifyPeer pid (fun p => { p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false })
    let now ← hidden site
    modifyPeer pid (fun p => { p with walltimeLastHandshake := now })
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = finish := by
    simp only [timersHandshakeComplete, finish, delTimer, modify_eq, bind_assoc]
  rw [factor, ensures_iff]
  let p1 := p.setTimer .retransmitHandshake none
  let p2 := { p1 with timerHandshakeAttempts := 0, sentLastminuteHandshake := false }
  have h1 := modifyPeer_exact_spec pid (fun p => p.setTimer .retransmitHandshake none) p
  have h2 := modifyPeer_exact_spec pid
    (fun p => { p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false }) p1
  have h3 := fun now => modifyPeer_exact_spec pid (fun p => { p with walltimeLastHandshake := now }) p2
  have hh := hidden_kernel_spec (fun k => (k.wg.bind fun d => d.peers[pid]?) = some p2)
  mvcgen [finish, h1, h2, h3, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, p1, p2]
  all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
