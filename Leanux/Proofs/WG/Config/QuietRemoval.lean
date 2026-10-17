import Leanux.Proofs.WG.Config.QuietRemovalLeaves
import Leanux.Proofs.WG.Config.QuietRemovalOutcomeModel
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private theorem clearOne_empty_run (pid : PeerId) (pick : Peer → Option KeypairId)
    (clear : Peer → Peer) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : pick p = none)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    ((clearOne pid pick clear).run g).run ambient =
      .ok (((), {g with dev := some (withPeer d pid (clear p))}),
        {ambient with steps := ambient.steps.push {
          decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}}) := by
  have modifySource (f : Peer → Peer) : modifyPeer pid f = (do
      let old ← getPeer pid
      setPeer pid (f old)) := rfl
  simp only [clearOne, modifySource, bind_assoc]
  simp [getPeer, getDev, device, resident, empty, setPeer, modifyDev,
    keypairPut, branch, AmbientM.branch, withPeer]
  rfl

private theorem deleteTimers_run (ts : List PeerTimer) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (g : WGWorld) (ambient : Ambient)
    (device : g.dev = some d) :
    ((forIn ts PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit)) : WG.M _).run g).run ambient =
      .ok (((), {g with dev := some (deleteTimersDevice ts d pid p)}), ambient) := by
  induction ts generalizing d p g with
  | nil =>
    change Except.ok (((), g), ambient) = Except.ok (((), {g with dev := some d}), ambient)
    have same : {g with dev := some d} = g := by rw [← device]
    rw [same]
  | cons t ts ih =>
    have deleted : ((delTimer pid t).run g).run ambient =
        .ok (((), {g with dev := some (withPeer d pid ((p.setTimer t none).setWheel t none))}), ambient) := by
      simp [delTimer, getPeer, getDev, device, resident, setPeer, modifyDev, withPeer]
      rfl
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    change (((delTimer pid t).run g).run ambient >>= fun ((_, current), after) =>
      ((forIn ts PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit)) : WG.M _).run current).run after) = _
    rw [deleted]
    change ((forIn ts PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit)) : WG.M _).run
      {g with dev := some (withPeer d pid ((p.setTimer t none).setWheel t none))}).run ambient = _
    simpa only [deleteTimersDevice] using ih (withPeer d pid ((p.setTimer t none).setWheel t none))
      ((p.setTimer t none).setWheel t none) (by simp [withPeer])
      {g with dev := some (withPeer d pid ((p.setTimer t none).setWheel t none))} rfl

private theorem keypairsClear_empty_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    ((keypairsClear pid).run g).run ambient =
      .ok (((), {g with dev := some (emptyKeysDevice d pid p)}),
        {ambient with steps := ((ambient.steps.push {
          decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}).push {
          decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}).push {
          decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}}) := by
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  rw [keypairsClear_source]
  simp only [bindRun, clearOne_empty_run pid _ _ d p resident empty.1 g ambient device, okBind]
  rw [clearOne_empty_run pid _ _ _ {p with keypairNext := none}
    (by simp [withPeer]) empty.2.1 _ _ rfl]
  simp only [okBind]
  rw [clearOne_empty_run pid _ _ _ {p with keypairNext := none, keypairPrevious := none}
    (by simp [withPeer]) empty.2.2 _ _ rfl]
  rfl

private theorem timersStop_quiet_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (quiet : d.clearWorkQueue = [])
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    ((timersStop pid).run g).run ambient =
      .ok (((), {g with dev := some (deleteTimersDevice PeerTimer.all d pid p)}), ambient) := by
  have hqueue : (deleteTimersDevice PeerTimer.all d pid p).clearWorkQueue = [] :=
    (congrArg Device.clearWorkQueue (deleteTimers_withoutPeers PeerTimer.all d pid p)).trans quiet
  change (((forIn PeerTimer.all PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit)) : WG.M _).run g).run ambient >>= fun ((_, current), after) =>
    ((do if (← getDev).clearWorkQueue.contains pid then drainHandshakeSendWq (some pid) : WG.M Unit).run current).run after) = _
  rw [deleteTimers_run _ pid d p resident g ambient device]
  simp [getDev, hqueue]
  rfl

/-- Exact success or refusal on the former totality domain. -/
theorem peerRemoveAfterDead_quiet_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true) (live : 0 < p.refcount)
    (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Observes (peerRemoveAfterDead pid) (fun s => s.wg.device = some d)
      (fun _ out => quietRemovalOutcome d pid p out) := by
  intro g ambient device
  change g.dev = some d at device
  let guarded := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNotDead, outcome := false, netRx := ambient.netRxSection}}
  let log := {guarded with steps := ((guarded.steps.push {
    decision := .keypairPutNull, outcome := true, netRx := guarded.netRxSection}).push {
    decision := .keypairPutNull, outcome := true, netRx := guarded.netRxSection}).push {
    decision := .keypairPutNull, outcome := true, netRx := guarded.netRxSection}}
  let cleaned := quietCleanupDevice d pid p
  let timed := {g with dev := some cleaned}
  have guardRun : ((removalDeadGuard pid).run g).run ambient = .ok (((), g), guarded) := by
    simp [removalDeadGuard, getPeer, getDev, device, resident, dead, branch, AmbientM.branch, guarded]
    rfl
  have keyRun := keypairsClear_empty_run pid d p resident empty g guarded device
  change ((keypairsClear pid).run g).run guarded =
    .ok (((), {g with dev := some (emptyKeysDevice d pid p)}), log) at keyRun
  have timerRun := timersStop_quiet_run pid (emptyKeysDevice d pid p) (emptyKeysPeer p)
    (by simp [emptyKeysDevice, withPeer]) clear
    {g with dev := some (emptyKeysDevice d pid p)} log rfl
  change ((timersStop pid).run {g with dev := some (emptyKeysDevice d pid p)}).run log =
    .ok (((), timed), log) at timerRun
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have factor : ((peerRemoveAfterDead pid).run g).run ambient =
      ((do
        if !cleaned.encryptQueue.empty || !cleaned.decryptQueue.empty || !cleaned.txWorkQueue.isEmpty ||
            cleaned.peers.toList.any (·.2.napiScheduled) then
          unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)"
        drainHandshakeSendWq none
        decrementPeerCount
        peerPut (some pid) : WG.M Unit).run timed).run log := by
    rw [peerRemoveAfterDead_source]
    simp only [bindRun, guardRun, okBind, keyRun, timerRun]
    simp [getDev, timed]
  rw [factor]
  unfold quietRemovalOutcome
  cases crypt : (!cleaned.encryptQueue.empty || !cleaned.decryptQueue.empty || !cleaned.txWorkQueue.isEmpty ||
      cleaned.peers.toList.any (·.2.napiScheduled)) with
  | true =>
    simp [crypt, cleaned, unsupported, AmbientM.unsupported, Campaign2.observeResult, log]
    rfl
  | false =>
    have frame := quietCleanup_frame d pid p
    have hs := congrArg Device.sendWorkQueue frame
    have hc := congrArg Device.clearWorkQueue frame
    have hn := congrArg Device.numPeers frame
    simp only [withoutPeers] at hs hc hn
    rw [send] at hs
    rw [clear] at hc
    change cleaned.sendWorkQueue = [] at hs
    change cleaned.clearWorkQueue = [] at hc
    have positive : 0 < cleaned.numPeers := by rw [hn]; exact count
    have drainRun : ((drainHandshakeSendWq none).run timed).run log = .ok (((), timed), log) := by
      unfold drainHandshakeSendWq
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size]
      rw [List.range'_succ, List.forIn_cons]
      simp [getDev, timed, hs, hc, StateT.run, StateT.bind, StateT.pure,
        bind, pure, get, getThe, MonadStateOf.get, StateT.get, Except.bind, Except.pure]
    obtain ⟨value, counted, afterCount, countRun, countDevice⟩ :=
      decrementPeerCount_returns cleaned positive timed log rfl
    cases value
    have release := Index.peerPut_exact pid {cleaned with numPeers := cleaned.numPeers - 1}
      (quietCleanupPeer p) (quietCleanup_resident d pid p)
      (by simpa only [quietCleanup_refcount] using live) counted afterCount countDevice
    simp only [cleaned] at crypt
    cases refusal : (if (quietCleanupPeer p).refcount = 1 then
      if (quietCleanupPeer p).txQueue.peeked.isSome || !(quietCleanupPeer p).txQueue.items.isEmpty ||
          (quietCleanupPeer p).rxQueue.peeked.isSome || !(quietCleanupPeer p).rxQueue.items.isEmpty then
        some (Stop.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
      else (PeerTimer.all.find? (fun t => (quietCleanupPeer p).timerPending t ||
          ((quietCleanupPeer p).wheel t).isSome)).map
        (fun t => Stop.invariant s!"peer {pid} released with its {repr t} timer pending")
    else none)
    all_goals simpa only [cleaned, crypt, Bool.false_eq_true, ite_false, bindRun, okBind,
      drainRun, countRun, quietRemovedDevice, refusal] using release

/-- Exact outer removal outcomes on the original removal-effect domain. -/
theorem peerRemove_quiet_returns (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Campaign2.Observes (peerRemove (some pid)) (fun s => s.wg.device = some d)
      (fun _ out => quietRemovalOutcome (deadPeerDevice removed pid p) pid
        {erasePeerList p.allowedipsList p with isDead := true} out) := by
  have metadata := removalEffect_metadata steps
  have queues := removalEffect_queues steps
  have hp := erasePeerList_exceptList p.allowedipsList p
  have slots : (erasePeerList p.allowedipsList p).keypairNext = none ∧
      (erasePeerList p.allowedipsList p).keypairPrevious = none ∧
      (erasePeerList p.allowedipsList p).keypairCurrent = none := by
    have hn := congrArg Peer.keypairNext hp
    have hv := congrArg Peer.keypairPrevious hp
    have hc := congrArg Peer.keypairCurrent hp
    exact ⟨hn.trans empty.1, hv.trans empty.2.1, hc.trans empty.2.2⟩
  have hcount : 0 < (deadPeerDevice removed pid p).numPeers := by
    have h := congrArg (fun x => x.2.2.2) metadata
    change removed.numPeers = d.numPeers at h
    change 0 < removed.numPeers
    rwa [h]
  have hs : (deadPeerDevice removed pid p).sendWorkQueue = [] :=
    (congrArg Prod.fst queues).trans send
  have hc : (deadPeerDevice removed pid p).clearWorkQueue = [] :=
    (congrArg Prod.snd queues).trans clear
  have after := peerRemoveAfterDead_quiet_returns pid (deadPeerDevice removed pid p)
    { erasePeerList p.allowedipsList p with isDead := true }
    (by simp [deadPeerDevice, withPeer]) rfl
    (by simpa only [erasePeerList_refcount] using live) hcount slots hs hc

  intro g ambient device
  change g.dev = some d at device
  let guarded := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨value, current, middle, made, currentDevice⟩ :=
    peerMakeDead_returns pid p d removed resident steps g guarded device
  cases value
  have source : ((peerRemove (some pid)).run g).run ambient =
      ((peerRemoveAfterDead pid).run current).run middle := by
    change (((peerMakeDead pid).run g).run guarded >>= fun ((_, state), inputs) =>
      ((peerRemoveAfterDead pid).run state).run inputs) = _
    rw [made]
    rfl
  rw [source]
  exact after current middle currentDevice

end Leanux.Proofs.WG.Config
