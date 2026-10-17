import Leanux.Proofs.WG.Config.LiveRemovalFrames
import Leanux.Proofs.WG.Config.QuietRemovalLeaves
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseOutcomeModel
import Leanux.Proofs.WG.Noise.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Exact outcomes of the stated post-clear continuation. This legacy local sequence omits the crypt-work guard; the full caller checks it
after timersStop. -/
theorem removalAfterClear_returns (pid : PeerId) (cleared : Device) (p : Peer)
    (resident : cleared.peers[pid]? = some (emptyKeysPeer p))
    (live : 0 < p.refcount) (count : 0 < cleared.numPeers)
    (send : cleared.sendWorkQueue = []) (clear : cleared.clearWorkQueue = []) :
    Campaign2.Observes (do
      timersStop pid
      drainHandshakeSendWq none
      decrementPeerCount
      peerPut (some pid)) (fun s => s.wg.device = some cleared)
      (fun _ out => match Index.peerReleaseRefusal pid (quietCleanupPeer p) with
        | some stop => out = .error stop
        | none => ∃ final, out = .ok ((), final) ∧
            final.wg.device = some (removedAfterClear cleared pid p)) := by
  intro g ambient device
  change g.dev = some cleared at device
  let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
  have frame := deleteTimers_withoutPeers PeerTimer.all cleared pid (emptyKeysPeer p)
  have hs := congrArg Device.sendWorkQueue frame
  have hc := congrArg Device.clearWorkQueue frame
  have hn := congrArg Device.numPeers frame
  simp only [withoutPeers] at hs hc hn
  rw [send] at hs
  rw [clear] at hc
  change timed.sendWorkQueue = [] at hs
  change timed.clearWorkQueue = [] at hc
  have positive : 0 < timed.numPeers := by rw [hn]; exact count
  have hpeer : timed.peers[pid]? = some (quietCleanupPeer p) :=
    deleteTimers_resident _ _ _ _ resident
  have hlive : 0 < (quietCleanupPeer p).refcount := by
    rw [quietCleanup_refcount]; exact live
  obtain ⟨timerValue, timedState, timerAmbient, timerRun, timedDevice⟩ :=
    timersStop_quiet_returns pid cleared (emptyKeysPeer p) resident clear g ambient device
  cases timerValue
  change timedState.dev = some timed at timedDevice
  have drainRun : ((drainHandshakeSendWq none).run timedState).run timerAmbient =
      .ok (((), timedState), timerAmbient) := by
    unfold drainHandshakeSendWq
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size]
    rw [List.range'_succ, List.forIn_cons]
    simp [getDev, timedDevice, hs, hc, StateT.run, StateT.bind, StateT.pure,
      bind, pure, get, getThe, MonadStateOf.get, StateT.get, Except.bind, Except.pure]
  obtain ⟨countValue, counted, countAmbient, countRun, countDevice⟩ :=
    decrementPeerCount_returns timed positive timedState timerAmbient timedDevice
  cases countValue
  have release := Index.peerPut_exact pid {timed with numPeers := timed.numPeers - 1}
    (quietCleanupPeer p) hpeer hlive counted countAmbient countDevice
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  change (match Index.peerReleaseRefusal pid (quietCleanupPeer p) with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run counted).run countAmbient) = .error stop
    | none => ∃ final, Campaign2.observeResult (((peerPut (some pid)).run counted).run countAmbient) =
      .ok ((), final) ∧ final.wg.device = some (removedAfterClear cleared pid p)) at release
  cases refusal : Index.peerReleaseRefusal pid (quietCleanupPeer p)
  all_goals simpa only [bindRun, okBind, timerRun, drainRun, countRun, refusal] using release

/-- Source outcome with real clear/timer execution witnesses. No diagnostic
site or intermediate device is chosen independently of those executions. -/
theorem peerRemoveAfterDead_live_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    ∃ guarded clearedState clearAmbient cleared timedState timerAmbient,
      ((removalDeadGuard pid).run g).run ambient = .ok (((), g), guarded) ∧
      ((keypairsClear pid).run g).run guarded = .ok (((), clearedState), clearAmbient) ∧
      clearedState.dev = some cleared ∧ ClearRun pid d [.next, .previous, .current] cleared ∧
      cleared.peers[pid]? = some (emptyKeysPeer p) ∧
      ((timersStop pid).run clearedState).run clearAmbient = .ok (((), timedState), timerAmbient) ∧
      timedState.dev = some (deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)) ∧
      let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
      let out := Campaign2.observeResult (((peerRemoveAfterDead pid).run g).run ambient)
      if !timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
          timed.peers.toList.any (·.2.napiScheduled) then
        out = .error (.outsideDomain (match timerAmbient.steps.back? with
          | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
          | none => "syscall entry")
          "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
      else match Index.peerReleaseRefusal pid (quietCleanupPeer p) with
        | some stop => out = .error stop
        | none => ∃ final, out = .ok ((), final) ∧
            final.wg.device = some (removedAfterClear cleared pid p) ∧
            LiveRemovalEffect pid d p (removedAfterClear cleared pid p) := by
  let guarded := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNotDead, outcome := false, netRx := ambient.netRxSection}}
  have guardRun : ((removalDeadGuard pid).run g).run ambient = .ok (((), g), guarded) := by
    simp [removalDeadGuard, getPeer, getDev, device, resident, dead, branch, AmbientM.branch, guarded]
    rfl
  obtain ⟨value, clearedState, clearAmbient, clearRun, cleared, clearedDevice, steps⟩ :=
    keypairsClear_returns_ready pid d p resident ready g guarded device
  cases value
  have clearedPeer : cleared.peers[pid]? = some (emptyKeysPeer p) := by
    have hp := keypairsClear_peer pid p g guarded () clearedState clearAmbient
      (by simp [peerAt, device, resident]) clearRun
    simpa [peerAt, clearedDevice, emptyKeysPeer] using hp
  have context := clearRun_cleanupContext steps
  have sendCleared : cleared.sendWorkQueue = [] := (congrArg Prod.fst context).trans send
  have clearCleared : cleared.clearWorkQueue = [] := (congrArg (fun x => x.2.1) context).trans clear
  have countCleared : 0 < cleared.numPeers := by
    have eqCount := congrArg (fun x => x.2.2) context
    change cleared.numPeers = d.numPeers at eqCount
    rw [eqCount]
    exact count
  obtain ⟨value, timedState, timerAmbient, timerRun, timedDevice⟩ :=
    timersStop_quiet_returns pid cleared (emptyKeysPeer p) clearedPeer clearCleared
      clearedState clearAmbient clearedDevice
  cases value
  refine ⟨guarded, clearedState, clearAmbient, cleared, timedState, timerAmbient,
    guardRun, clearRun, clearedDevice, steps, clearedPeer, timerRun, timedDevice, ?_⟩
  let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
  change timedState.dev = some timed at timedDevice
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have factor : ((peerRemoveAfterDead pid).run g).run ambient =
      ((do
        if !timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
            timed.peers.toList.any (·.2.napiScheduled) then
          unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)"
        drainHandshakeSendWq none
        decrementPeerCount
        peerPut (some pid) : WG.M Unit).run timedState).run timerAmbient := by
    rw [peerRemoveAfterDead_source]
    simp only [bindRun, guardRun, okBind, clearRun, timerRun]
    simp [getDev, timedDevice]
  dsimp only
  rw [factor]
  cases crypt : (!timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
      timed.peers.toList.any (·.2.napiScheduled)) with
  | true =>
    simp only [ite_true]
    simp [unsupported, AmbientM.unsupported, Campaign2.observeResult]
    rfl
  | false =>
    have tail := removalAfterClear_returns pid cleared p clearedPeer live countCleared
      sendCleared clearCleared clearedState clearAmbient clearedDevice
    simp only [bindRun, timerRun, okBind] at tail
    simp only [Bool.false_eq_true, ite_false]
    simp only [bindRun]
    cases refusal : Index.peerReleaseRefusal pid (quietCleanupPeer p) with
    | some stop => simpa only [refusal] using tail
    | none =>
      rw [refusal] at tail
      obtain ⟨final, execution, finalDevice⟩ := tail
      exact ⟨final, execution, finalDevice, cleared, steps, rfl⟩

theorem peerRemove_live_returns (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :

    let afterNull := {ambient with steps := ambient.steps.push {
      decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
    ∃ current middle,
      ((peerMakeDead pid).run g).run afterNull = .ok (((), current), middle) ∧
      current.dev = some (deadPeerDevice removed pid p) ∧
    ∃ guarded clearedState clearAmbient cleared timedState timerAmbient,
      ((removalDeadGuard pid).run current).run middle = .ok (((), current), guarded) ∧
      ((keypairsClear pid).run current).run guarded = .ok (((), clearedState), clearAmbient) ∧
      clearedState.dev = some cleared ∧ ClearRun pid (deadPeerDevice removed pid p) [.next, .previous, .current] cleared ∧
      cleared.peers[pid]? = some (emptyKeysPeer {erasePeerList p.allowedipsList p with isDead := true}) ∧
      ((timersStop pid).run clearedState).run clearAmbient = .ok (((), timedState), timerAmbient) ∧
      timedState.dev = some (deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer {erasePeerList p.allowedipsList p with isDead := true})) ∧
      let timed := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer {erasePeerList p.allowedipsList p with isDead := true})
      let out := Campaign2.observeResult (((peerRemove (some pid)).run g).run ambient)
      if !timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
          timed.peers.toList.any (·.2.napiScheduled) then
        out = .error (.outsideDomain (match timerAmbient.steps.back? with
          | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
          | none => "syscall entry")
          "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
      else match Index.peerReleaseRefusal pid (quietCleanupPeer {erasePeerList p.allowedipsList p with isDead := true}) with
        | some stop => out = .error stop
        | none => ∃ final, out = .ok ((), final) ∧
            final.wg.device = some (removedAfterClear cleared pid {erasePeerList p.allowedipsList p with isDead := true}) ∧
            LiveRemovalEffect pid (deadPeerDevice removed pid p) {erasePeerList p.allowedipsList p with isDead := true} (removedAfterClear cleared pid {erasePeerList p.allowedipsList p with isDead := true}) := by
  have metadata := removalEffect_metadata steps
  have queues := removalEffect_queues steps
  have keys := removalEffect_keypairs steps
  have hp := erasePeerList_exceptList p.allowedipsList p
  have hkeys : clearKeys { erasePeerList p.allowedipsList p with isDead := true } = clearKeys p := by
    simpa only [clearKeys] using congrArg clearKeys hp
  have hready : ClearReady (deadPeerDevice removed pid p)
      (clearKeys { erasePeerList p.allowedipsList p with isDead := true }) := by
    rw [hkeys]
    intro id used
    obtain ⟨k, found, word, budget⟩ := ready id used
    refine ⟨k, ?_, word, budget⟩
    change removed.keypairs[id]? = some k
    rw [keys]
    exact found
  have hcount : 0 < (deadPeerDevice removed pid p).numPeers := by
    have h := congrArg (fun x => x.2.2.2) metadata
    change removed.numPeers = d.numPeers at h
    change 0 < removed.numPeers
    rwa [h]
  have hs : (deadPeerDevice removed pid p).sendWorkQueue = [] :=
    (congrArg Prod.fst queues).trans send
  have hc : (deadPeerDevice removed pid p).clearWorkQueue = [] :=
    (congrArg Prod.snd queues).trans clear
  have after := peerRemoveAfterDead_live_returns pid (deadPeerDevice removed pid p)
    { erasePeerList p.allowedipsList p with isDead := true }
    (by simp [deadPeerDevice, withPeer]) rfl
    (by simpa only [erasePeerList_refcount] using live) hcount hready hs hc
  let afterNull := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨value, current, middle, made, currentDevice⟩ :=
    peerMakeDead_returns pid p d removed resident steps g afterNull device
  cases value
  refine ⟨current, middle, made, currentDevice, ?_⟩
  have source : ((peerRemove (some pid)).run g).run ambient =
      ((peerRemoveAfterDead pid).run current).run middle := by
    change (((peerMakeDead pid).run g).run afterNull >>= fun ((_, state), inputs) =>
      ((peerRemoveAfterDead pid).run state).run inputs) = _
    rw [made]
    rfl
  rw [source]
  exact after current middle currentDevice

end Leanux.Proofs.WG.Config
