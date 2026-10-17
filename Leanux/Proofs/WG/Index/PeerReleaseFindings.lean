import Leanux.Proofs.WG.Index.Release

/-! Counterexamples to the legacy unconditional total peer-release contract.
Both witnesses satisfy its residency and positive-reference premises. The native
mirror stops at its final-release guards; no reachability or mirror-bug claim is
made, and the legacy theorem is not weakened here. -/
set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- One queued transmit batch suffices to refute the legacy totality premise.
The witness is a mathematical device state, without a reachability claim. -/
theorem peerPut_legacy_total_queued_counterexample (ambient : Ambient) :
    ∃ p d g,
      d.peers[0]? = some p ∧ p.refcount = 1 ∧ p.txQueue.items = [[0]] ∧
      g.dev = some d ∧
      ((peerPut (some 0)).run g).run ambient =
        .error (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)") ∧
      ¬ Returns (peerPut (some 0)) (fun g => g.dev = some d)
        (fun _ g => g.dev = some (releasedPeerDevice d 0 p)) := by
  let p : Peer := {
    remoteStatic := List.replicate 32 0
    presharedKey := List.replicate 32 0
    precomputedStaticStatic := List.replicate 32 0
    internalId := 0
    txQueue := {items := [[0]]}}
  let d : Device := {ifindex := 0, ifname := "wg0", peers := ({} : Std.TreeMap PeerId Peer).insert 0 p}
  let g : WGWorld := {dev := some d}
  have run : ((peerPut (some 0)).run g).run ambient =
      .error (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)") := by
    have removeForm : indexRemove (.handshake 0) = (do
      _ ← branch .idxRemoveHashed ((← get).any (·.owner == .handshake 0))
      modify fun table => table.filter fun e => !(e.owner == .handshake 0) : IndexM Unit) := rfl
    have lifted : (monadLift (indexRemove (.handshake 0)) : WG.M Unit) =
        liftIndex (indexRemove (.handshake 0)) := rfl
    simp only [peerPut, lifted]
    simp [requireNotPending, getPeer, getDev, setPeer, modifyDev, refcountDecAndTest,
      branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, removeForm, liftIndex,
      invariant, AmbientM.invariant, p, d, g]
    rfl
  refine ⟨p, d, g, ?_, rfl, rfl, rfl, run, ?_⟩
  · simp [d]
  · intro total
    obtain ⟨value, final, after, success, _⟩ := total g ambient rfl
    rw [run] at success
    cases success

/-- Empty queues do not suffice: a locally consistent pending timer and wheel
also cause the actual final-release stop. -/
theorem peerPut_legacy_total_timer_counterexample (ambient : Ambient) :
    ∃ p d g,
      d.peers[0]? = some p ∧ p.refcount = 1 ∧
      p.txQueue = ({} : PrevQueue (List SkbId)) ∧ p.rxQueue = ({} : PrevQueue SkbId) ∧
      p.timer .sendKeepalive = some 1 ∧ p.wheel .sendKeepalive = some ⟨2, 2, 1⟩ ∧
      TimerWheel.peerWheelProblem p = none ∧ g.dev = some d ∧
      ((peerPut (some 0)).run g).run ambient =
        .error (.invariant s!"peer {(0 : PeerId)} released with its {repr PeerTimer.sendKeepalive} timer pending") ∧
      ¬ Returns (peerPut (some 0)) (fun g => g.dev = some d)
        (fun _ g => g.dev = some (releasedPeerDevice d 0 p)) := by
  let p : Peer := {
    remoteStatic := List.replicate 32 0
    presharedKey := List.replicate 32 0
    precomputedStaticStatic := List.replicate 32 0
    internalId := 0
    timerSendKeepalive := some 1
    wheelSendKeepalive := some ⟨2, 2, 1⟩}
  let d : Device := {ifindex := 0, ifname := "wg0", peers := ({} : Std.TreeMap PeerId Peer).insert 0 p}
  let g : WGWorld := {dev := some d}
  have run : ((peerPut (some 0)).run g).run ambient =
      .error (.invariant s!"peer {(0 : PeerId)} released with its {repr PeerTimer.sendKeepalive} timer pending") := by
    have removeForm : indexRemove (.handshake 0) = (do
      _ ← branch .idxRemoveHashed ((← get).any (·.owner == .handshake 0))
      modify fun table => table.filter fun e => !(e.owner == .handshake 0) : IndexM Unit) := rfl
    have lifted : (monadLift (indexRemove (.handshake 0)) : WG.M Unit) =
        liftIndex (indexRemove (.handshake 0)) := rfl
    simp only [peerPut, lifted]
    simp [requireNotPending, getPeer, getDev, setPeer, modifyDev, refcountDecAndTest,
      branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, removeForm, liftIndex,
      invariant, AmbientM.invariant, p, d, g]
    rfl
  refine ⟨p, d, g, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, run, ?_⟩
  · simp [d]
  · intro total
    obtain ⟨value, final, after, success, _⟩ := total g ambient rfl
    rw [run] at success
    cases success

end Leanux.Proofs.WG.Index
