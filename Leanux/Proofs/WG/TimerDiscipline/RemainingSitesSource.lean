import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def dataReceivedPrefix (pid : PeerId) : M (Option Bool) := do
  if ← branch .timersDataReceivedRunning (← getDev).running then
    return some (← branch .timersDataReceivedNotPending !((← getPeer pid).timerPending .sendKeepalive))
  return none

def dataReceivedTail (pid : PeerId) (choice : Option Bool) : M Unit := do
  match choice with
  | none => pure ()
  | some true => discard <| modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
  | some false => setPeer pid { (← getPeer pid) with timerNeedAnotherKeepalive := true }

theorem dataReceived_source (pid : PeerId) :
    timersDataReceived pid = (do let choice ← dataReceivedPrefix pid; dataReceivedTail pid choice) := by
  simp only [timersDataReceived, dataReceivedPrefix, dataReceivedTail, bind_assoc]
  congr 1
  funext d
  congr 1
  funext running
  cases running <;> simp
  congr 1
  funext p
  congr 1
  funext absent
  cases absent <;> rfl

theorem dataReceivedPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) :
    Returns (dataReceivedPrefix pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun choice w => choice = some true ∧ w.k.wg = some d ∧ w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [dataReceivedPrefix, getPeer, getDev, getK, invariant, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem dataReceived_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersDataReceived pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (dataReceivedPrefix pid).run initial = .ok (some true, beforeRead) ∧
      (callerJiffies .timerJiffiesDataReceived).run beforeRead = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer .sendKeepalive
        (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  obtain ⟨choice, beforeRead, hprefix, value, hd, hm⟩ :=
    dataReceivedPrefix_returns pid d p resident absent running initial ⟨device, records⟩
  subst choice
  rw [dataReceived_source, StateT.run_bind, hprefix] at run
  change (discard (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive
    KEEPALIVE_TIMEOUT_TICKS) : M Unit).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS d p resident running alive
    beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩

def keepaliveRearmPrefix (pid : PeerId) : M Bool := do
  if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
    setPeer pid { (← getPeer pid) with timerNeedAnotherKeepalive := false }
    return true
  return false

theorem expiredKeepalive_source (pid : PeerId) :
    expiredSendKeepalive pid = (do
      sendKeepalive pid
      if ← keepaliveRearmPrefix pid then
        discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) := by
  simp only [expiredSendKeepalive, keepaliveRearmPrefix, bind_assoc]
  congr 1
  funext x
  congr 1
  funext p
  congr 1
  funext needed
  cases needed <;> simp

theorem keepaliveRearmPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (needed : p.timerNeedAnotherKeepalive = true) :
    Returns (keepaliveRearmPrefix pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = true ∧
        w.k.wg = some (withPeer d pid { p with timerNeedAnotherKeepalive := false }) ∧
        w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [keepaliveRearmPrefix, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    invariant, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]

theorem expiredKeepalive_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (needed : p.timerNeedAnotherKeepalive = true)
    (running : d.running = true) (alive : p.isDead = false)
    (initial afterSend final : World)
    (send : (sendKeepalive pid).run initial = .ok ((), afterSend))
    (device : afterSend.k.wg = some d) (records : afterSend.armRecords = true)
    (run : (expiredSendKeepalive pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (keepaliveRearmPrefix pid).run afterSend = .ok (true, beforeRead) ∧
      (callerJiffies .timerJiffiesExpiredKeepalive).run beforeRead = .ok (some caller, afterRead) ∧
      peerAt final pid = some (({ p with timerNeedAnotherKeepalive := false } : Peer).setTimer
        .sendKeepalive (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  obtain ⟨ready, beforeRead, hprefix, value, hd, hm⟩ :=
    keepaliveRearmPrefix_returns pid d p resident needed afterSend ⟨device, records⟩
  subst ready
  rw [expiredKeepalive_source, StateT.run_bind, send] at run
  change ((keepaliveRearmPrefix pid >>= fun ready => if ready then
    discard (modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)
    else pure ()) : M Unit).run afterSend = .ok ((), final) at run
  rw [StateT.run_bind, hprefix] at run
  change (discard (modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive
    KEEPALIVE_TIMEOUT_TICKS) : M Unit).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
    (withPeer d pid { p with timerNeedAnotherKeepalive := false })
    { p with timerNeedAnotherKeepalive := false } (by simp [withPeer]) running alive
    beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩

def giveUpArmPrefix (pid : PeerId) : M Bool := do
  delTimer pid .sendKeepalive
  purgeStagedPackets pid
  branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial)

theorem giveUpArm_source (pid : PeerId) :
    retransmitGiveUp pid = (do
      if ← giveUpArmPrefix pid then
        discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS) := by
  simp only [retransmitGiveUp, giveUpArmPrefix, bind_assoc]

theorem delKeepalive_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (delTimer pid .sendKeepalive) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun _ w => w.k.wg = some (withPeer d pid (p.setTimer .sendKeepalive none)) ∧
        w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [delTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]

theorem purgeStaged_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (purgeStagedPackets pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun _ w => w.k.wg = some
        (withPeer { d with txDropped := d.txDropped + p.staged.length } pid { p with staged := [] }) ∧
        w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [purgeStagedPackets, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]

theorem zeroKeyAbsent_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .zeroKeyMaterial = false) :
    Returns (do branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial))
      (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = true ∧ w.k.wg = some d ∧ w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [getPeer, getDev, getK, invariant, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem giveUpArmPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .zeroKeyMaterial = false) :
    Returns (giveUpArmPrefix pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = true ∧ w.k.wg = some (giveUpDevice d pid p) ∧ w.armRecords = true) := by
  unfold giveUpArmPrefix
  refine returns_bind _ _ (delKeepalive_returns pid d p resident) ?_
  intro u
  refine returns_bind _ _ (purgeStaged_returns pid (withPeer d pid (p.setTimer .sendKeepalive none))
    (p.setTimer .sendKeepalive none) (by simp [withPeer])) ?_
  intro u
  have hd : withPeer
      { (withPeer d pid (p.setTimer .sendKeepalive none)) with
        txDropped := (withPeer d pid (p.setTimer .sendKeepalive none)).txDropped +
          (p.setTimer .sendKeepalive none).staged.length }
      pid { (p.setTimer .sendKeepalive none) with staged := [] } = giveUpDevice d pid p := by
    simp [withPeer, giveUpDevice, giveUpPeer, Peer.setTimer]
  rw [hd]
  exact zeroKeyAbsent_returns pid (giveUpDevice d pid p) (giveUpPeer p)
    (by simp [giveUpDevice, withPeer]) (by simpa [giveUpPeer, Peer.setTimer, Peer.timerPending, Peer.timer] using absent)

def retransmitDecision (pid : PeerId) : M Bool := do
  let attempts := (← getPeer pid).timerHandshakeAttempts
  branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES

theorem retransmitDecision_source (pid : PeerId) :
    expiredRetransmitHandshake pid = (do
      if ← retransmitDecision pid then retransmitGiveUp pid
      else
        let p ← getPeer pid
        setPeer pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := by
  simp only [expiredRetransmit_source, retransmitDecision, bind_assoc]

theorem retransmitDecision_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) :
    Returns (retransmitDecision pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = true ∧ w.k.wg = some d ∧ w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [retransmitDecision, getPeer, getDev, getK, invariant, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem retransmitGiveUp_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (expiredRetransmitHandshake pid).run initial = .ok ((), final)) :
    ∃ afterDecision beforeRead caller afterRead,
      (retransmitDecision pid).run initial = .ok (true, afterDecision) ∧
      (giveUpArmPrefix pid).run afterDecision = .ok (true, beforeRead) ∧
      (callerJiffies .timerJiffiesRetransmitZeroKey).run beforeRead = .ok (some caller, afterRead) ∧
      peerAt final pid = some ((giveUpPeer p).setTimer .zeroKeyMaterial
        (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  obtain ⟨decision, afterDecision, hdecision, value, hd, hm⟩ :=
    retransmitDecision_returns pid d p resident limit initial ⟨device, records⟩
  subst decision
  rw [retransmitDecision_source, StateT.run_bind, hdecision] at run
  change (retransmitGiveUp pid).run afterDecision = .ok ((), final) at run
  obtain ⟨ready, beforeRead, hprefix, value, hd', hm'⟩ :=
    giveUpArmPrefix_returns pid d p resident absent afterDecision ⟨hd, hm⟩
  subst ready
  rw [giveUpArm_source, StateT.run_bind, hprefix] at run
  change (discard (modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS) : M Unit).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
    (giveUpDevice d pid p) (giveUpPeer p) (by simp [giveUpDevice, withPeer])
    running alive beforeRead final hd' hm' run
  exact ⟨afterDecision, beforeRead, caller, afterRead, hdecision, hprefix, hread, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
