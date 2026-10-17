import Leanux.Proofs.WG.Config.QuietRemovalSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- A scheduled poll meets the old quiet/live premises but triggers the actual
crypt-work stop. No reachability assertion is made for this mathematical state. -/
theorem peerRemoveAfterDead_legacy_total_napi_counterexample (ambient : Ambient) :
    ∃ (p : Peer) (d : Device) (g : WGWorld),
      d.peers[0]? = some p ∧ p.isDead = true ∧ 0 < p.refcount ∧ 0 < d.numPeers ∧
      (p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none) ∧
      ClearReady d (clearKeys p) ∧ d.sendWorkQueue = [] ∧ d.clearWorkQueue = [] ∧
      p.napiScheduled = true ∧ g.dev = some d ∧
      (∃ site, ((peerRemoveAfterDead 0).run g).run ambient =
        .error (.outsideDomain site
          "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")) ∧
      ¬ Returns (peerRemoveAfterDead 0) (fun g => g.dev = some d) (fun _ _ => True) := by
  let p : Peer := {
    remoteStatic := List.replicate 32 0
    presharedKey := List.replicate 32 0
    precomputedStaticStatic := List.replicate 32 0
    internalId := 0
    refcount := 2
    isDead := true
    napiScheduled := true}
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    numPeers := 1
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 p}
  let g : WGWorld := {dev := some d}
  have resident : d.peers[0]? = some p := by simp [d]
  have empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none :=
    ⟨rfl, rfl, rfl⟩
  let guarded := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNotDead, outcome := false, netRx := ambient.netRxSection}}
  have guardRun : ((removalDeadGuard 0).run g).run ambient = .ok (((), g), guarded) := by
    simp [removalDeadGuard, getPeer, getDev, g, resident, p, branch, AmbientM.branch, guarded]
    rfl
  obtain ⟨clearResult, cleared, clearAmbient, clearRun, clearDevice⟩ :=
    keypairsClear_empty_returns 0 d p resident empty g guarded rfl
  cases clearResult
  obtain ⟨timerResult, timed, timerAmbient, timerRun, timedDevice⟩ :=
    timersStop_quiet_returns 0 (emptyKeysDevice d 0 p) (emptyKeysPeer p)
      (by simp [emptyKeysDevice, withPeer]) rfl cleared clearAmbient clearDevice
  cases timerResult
  have napi : (quietCleanupDevice d 0 p).peers.toList.any (·.2.napiScheduled) = true := by
    apply List.any_eq_true.mpr
    refine ⟨(0, quietCleanupPeer p), ?_, ?_⟩
    · apply Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
      exact deleteTimers_resident _ _ _ _ (by simp [emptyKeysDevice, withPeer])
    · simp [quietCleanupPeer, deleteTimersPeer, emptyKeysPeer, PeerTimer.all,
        Peer.setTimer, Peer.setWheel, p]
  let site := match timerAmbient.steps.back? with
    | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
    | none => "syscall entry"
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have stopped : ((peerRemoveAfterDead 0).run g).run ambient =
      .error (.outsideDomain site
        "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)") := by
    rw [peerRemoveAfterDead_source]
    simp only [bindRun, guardRun, okBind, clearRun, timerRun]
    change timed.dev = some (quietCleanupDevice d 0 p) at timedDevice
    simp [getDev, timedDevice, napi, unsupported, AmbientM.unsupported, site]
    rfl
  refine ⟨p, d, g, resident, rfl, by decide, by decide, empty,
    ?_, rfl, rfl, rfl, rfl, ⟨site, stopped⟩, ?_⟩
  · intro id positive
    simp [clearKeys, p] at positive
  · intro total
    obtain ⟨value, final, after, success, _⟩ := total g ambient rfl
    rw [stopped] at success
    cases success

end Leanux.Proofs.WG.Config
