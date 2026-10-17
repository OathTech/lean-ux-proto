import Leanux.Proofs.WG.Noise.Execution
import Leanux.WG.Timers
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- A well-formed pending timer loses its wheel entry on deletion. The older
exact-peer postcondition retained that entry, so its native retyping is false. -/
theorem delTimer_legacy_exact_counterexample (ambient : Ambient) :
    ∃ p g final,
      p.timer .sendKeepalive = some 1 ∧
      p.wheel .sendKeepalive = some ⟨2, 2, 1⟩ ∧
      TimerWheel.peerWheelProblem p = none ∧
      peerAt g 0 = some p ∧
      ((delTimer 0 .sendKeepalive).run g).run ambient = .ok (((), final), ambient) ∧
      peerAt final 0 ≠ some (p.setTimer .sendKeepalive none) := by
  let p : Peer := {
    remoteStatic := List.replicate 32 0
    presharedKey := List.replicate 32 0
    precomputedStaticStatic := List.replicate 32 0
    internalId := 0
    timerSendKeepalive := some 1
    wheelSendKeepalive := some ⟨2, 2, 1⟩ }
  let d : Device := {ifindex := 0, ifname := "wg0", peers := ({} : Std.TreeMap PeerId Peer).insert 0 p}
  let g : WGWorld := {dev := some d}
  let cleared := (p.setTimer .sendKeepalive none).setWheel .sendKeepalive none
  let final : WGWorld := {g with dev := some {d with peers := d.peers.insert 0 cleared}}
  refine ⟨p, g, final, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [peerAt, g, d]
  · simp [delTimer, getPeer, getDev, setPeer, modifyDev, g, d, final, cleared]
    rfl
  · intro same
    have wheel := congrArg (fun x : Option Peer => x.map Peer.wheelSendKeepalive) same
    simp [peerAt, final, d, p, cleared, Peer.setTimer, Peer.setWheel] at wheel

end Leanux.Proofs.WG.TimerDiscipline
