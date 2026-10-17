import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- The old total absent-timer give-up domain admits a stream that ends after
its valid caller/arm records. The current full callback then asks for the
base-clock record and stops; no post-error state or reachability is asserted. -/
theorem absentGiveUp_missing_clock_counterexample :
    ∃ (input : GiveUpArmInput) (d : Device) (p : Peer) (g : WGWorld) (ambient : Ambient),
      input.Valid ∧ d.peers[0]? = some p ∧
      MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts ∧
      p.timerZeroKeyMaterial = none ∧ d.running = true ∧ p.isDead = false ∧
      g.dev = some d ∧ ambient.armRecords = true ∧
      ambient.hidden = some (input.records []) ∧
      ((expiredRetransmitHandshake 0).run g).run ambient =
        .error (.hidden "no record left for timer_clk") := by
  let input : GiveUpArmInput := {
    callerData := List.replicate 8 0
    armData := List.replicate 8 0 ++ [88, 15, 2] ++ List.replicate 13 0 }
  let p : Peer := {
    remoteStatic := []
    presharedKey := []
    precomputedStaticStatic := []
    internalId := 0
    timerHandshakeAttempts := 19 }
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    running := true
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 p }
  let g : WGWorld := {dev := some d}
  let ambient : Ambient := {
    env := fun _ _ => false
    timing := ⟨0, 0⟩
    armRecords := true
    hidden := some (input.records []) }
  refine ⟨input, d, p, g, ambient, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · unfold GiveUpArmInput.Valid
    decide
  · simp [d]
  · decide
  · dsimp [expiredRetransmitHandshake, getPeer, getDev, setPeer, modifyDev,
      branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
      delTimer, purgeStagedPackets, Peer.timerPending, Peer.timer,
      Peer.setTimer, Peer.setWheel, modPeerTimer, modPeerTimerGuard,
      WG.andM, callerJiffies, armTimer,
      hiddenJiffies, AmbientM.hiddenJiffies, hidden, AmbientM.hidden,
      AmbientM.skipAmbient, AmbientM.noteNetRxStart,
      GiveUpArmInput.records, g, d, p, ambient, input,
      HiddenSite.info, HiddenSite.passive, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT]
    rfl

end Leanux.Proofs.WG.TimerDiscipline
