import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesModel
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

-- Local form of campaign 1's Framing.liftWG_bind for actual product composition.
private theorem liftWG_bind_variant {α β : Type} (a : WG.M α) (f : α → WG.M β) :
    liftWG (a >>= f) = (liftWG a >>= fun x => liftWG (f x)) := by
  have lifted {γ : Type} (action : WG.M γ) (w) :
      (liftWG action).run w = ((action.run w.wg).run w.ambient).map
        (fun ((x, g), ambient) => (x, {w with wg := g, ambient})) := by
    unfold liftWG StateT.run
    cases action w.wg w.ambient <;> rfl
  funext w
  change (liftWG (a >>= f)).run w = (liftWG a >>= fun x => liftWG (f x)).run w
  rw [lifted]
  simp only [StateT.run_bind]
  rw [lifted]
  cases hr : (a.run w.wg).run w.ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨x, g⟩, ambient⟩
    simp only [Except.map]
    exact (lifted (f x) {w with wg := g, ambient}).symm

def dataReceivedPrefix (pid : PeerId) : WG.M (Option Bool) := do
  if ← branch .timersDataReceivedRunning (← getDev).running then
    return some (← branch .timersDataReceivedNotPending !((← getPeer pid).timerPending .sendKeepalive))
  return none

def dataReceivedTail (pid : PeerId) (choice : Option Bool) : WG.M Unit := do
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
    Config.Product.Returns (liftWG (dataReceivedPrefix pid)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun choice w => choice = some true ∧ w.wg.dev = some d ∧ w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let first := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .timersDataReceivedRunning, outcome := true, netRx := initial.ambient.netRxSection}}
  let inputs := {first with steps := first.steps.push {
    decision := .timersDataReceivedNotPending, outcome := true, netRx := first.netRxSection}}
  refine ⟨some true, {initial with ambient := inputs}, ?_, rfl, device, records⟩
  change (((dataReceivedPrefix pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ dataReceivedPrefix, getPeer, getDev, device, resident, absent,
    running, branch, AmbientM.branch, inputs, first]

theorem dataReceived_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersDataReceived pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (liftWG (dataReceivedPrefix pid)).run initial = .ok (some true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesDataReceived)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .sendKeepalive
        KEEPALIVE_TIMEOUT_TICKS caller (Campaign2.Product.snapshot final).wg := by
  obtain ⟨choice, beforeRead, hprefix, value, hd, hm⟩ :=
    dataReceivedPrefix_returns pid d p resident absent running initial ⟨device, records⟩
  subst choice
  rw [dataReceived_source, liftWG_bind_variant, StateT.run_bind, hprefix] at run
  change (liftWG (discard (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive
    KEEPALIVE_TIMEOUT_TICKS) : WG.M Unit)).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS d p resident running alive
    beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩

def keepaliveRearmPrefix (pid : PeerId) : WG.M Bool := do
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
    Config.Product.Returns (liftWG (keepaliveRearmPrefix pid)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = true ∧
        w.wg.dev = some (withPeer d pid { p with timerNeedAnotherKeepalive := false }) ∧
        w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let inputs := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .keepaliveNeedAnother, outcome := true, netRx := initial.ambient.netRxSection}}
  let changed := {initial.wg with dev := some (withPeer d pid {p with timerNeedAnotherKeepalive := false})}
  refine ⟨true, {initial with wg := changed, ambient := inputs}, ?_, rfl, rfl, records⟩
  change (((keepaliveRearmPrefix pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ keepaliveRearmPrefix, getPeer, getDev, device, resident, needed,
    branch, AmbientM.branch, setPeer, modifyDev, inputs, changed, withPeer]

theorem expiredKeepalive_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (needed : p.timerNeedAnotherKeepalive = true)
    (running : d.running = true) (alive : p.isDead = false)
    (initial afterSend final : World)
    (send : (liftWG (sendKeepalive pid)).run initial = .ok ((), afterSend))
    (device : afterSend.wg.dev = some d) (records : afterSend.ambient.armRecords = true)
    (run : (liftWG (expiredSendKeepalive pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (liftWG (keepaliveRearmPrefix pid)).run afterSend = .ok (true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesExpiredKeepalive)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid
        {p with timerNeedAnotherKeepalive := false} .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller
        (Campaign2.Product.snapshot final).wg := by
  obtain ⟨ready, beforeRead, hprefix, value, hd, hm⟩ :=
    keepaliveRearmPrefix_returns pid d p resident needed afterSend ⟨device, records⟩
  subst ready
  rw [expiredKeepalive_source, liftWG_bind_variant, StateT.run_bind, send] at run
  change (liftWG ((keepaliveRearmPrefix pid >>= fun ready => if ready then
    discard (modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)
    else pure ()) : WG.M Unit)).run afterSend = .ok ((), final) at run
  rw [liftWG_bind_variant, StateT.run_bind, hprefix] at run
  change (liftWG (discard (modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive
    KEEPALIVE_TIMEOUT_TICKS) : WG.M Unit)).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
    (withPeer d pid { p with timerNeedAnotherKeepalive := false })
    { p with timerNeedAnotherKeepalive := false } (by simp [withPeer]) running alive
    beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩


def giveUpArmPrefix (pid : PeerId) : WG.M Bool := do
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
    Config.Product.Returns (liftWG (delTimer pid .sendKeepalive)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun _ w => w.wg.dev = some (withPeer d pid ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none)) ∧
        w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let changed := {initial.wg with dev := some (withPeer d pid
    ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none))}
  refine ⟨(), {initial with wg := changed}, ?_, rfl, records⟩
  change (((delTimer pid .sendKeepalive).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ delTimer, getPeer, getDev, device, resident, setPeer, modifyDev, changed, withPeer]

theorem purgeStaged_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Config.Product.Returns (liftWG (purgeStagedPackets pid)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun _ w => w.wg.dev = some
        (withPeer { d with txDropped := d.txDropped + p.staged.length } pid { p with staged := [] }) ∧
        w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let changed := {initial.wg with dev := some (withPeer
    {d with txDropped := d.txDropped + p.staged.length} pid {p with staged := []})}
  refine ⟨(), {initial with wg := changed}, ?_, rfl, records⟩
  change (((purgeStagedPackets pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ purgeStagedPackets, getPeer, getDev, device, resident, setPeer, modifyDev, changed, withPeer]

theorem zeroKeyAbsent_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .zeroKeyMaterial = false) :
    Config.Product.Returns (liftWG (do branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial)))
      (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = true ∧ w.wg.dev = some d ∧ w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let inputs := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .retransmitZeroKeyNotPending, outcome := true, netRx := initial.ambient.netRxSection}}
  refine ⟨true, {initial with ambient := inputs}, ?_, rfl, device, records⟩
  change ((((do branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) : WG.M Bool)).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ getPeer, getDev, device, resident, absent, branch, AmbientM.branch, inputs]

theorem giveUpArmPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .zeroKeyMaterial = false) :
    Config.Product.Returns (liftWG (giveUpArmPrefix pid)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = true ∧ w.wg.dev = some (giveUpWheelDevice d pid p) ∧ w.ambient.armRecords = true) := by
  unfold giveUpArmPrefix
  rw [liftWG_bind_variant]
  refine Config.Product.returns_bind _ _ (delKeepalive_returns pid d p resident) ?_
  intro u
  rw [liftWG_bind_variant]
  refine Config.Product.returns_bind _ _ (purgeStaged_returns pid (withPeer d pid ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none))
    ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none) (by simp [withPeer])) ?_
  intro u
  have hd : withPeer
      { (withPeer d pid ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none)) with
        txDropped := (withPeer d pid ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none)).txDropped +
          ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none).staged.length }
      pid { ((p.setTimer .sendKeepalive none).setWheel .sendKeepalive none) with staged := [] } = giveUpWheelDevice d pid p := by
    simp [withPeer, giveUpWheelDevice, giveUpWheelPeer, Peer.setTimer, Peer.setWheel]
  rw [hd]
  exact zeroKeyAbsent_returns pid (giveUpWheelDevice d pid p) (giveUpWheelPeer p)
    (by simp [giveUpWheelDevice]) (by simpa [giveUpWheelPeer, Peer.setTimer, Peer.setWheel, Peer.timerPending, Peer.timer] using absent)

def retransmitDecision (pid : PeerId) : WG.M Bool := do
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
    Config.Product.Returns (liftWG (retransmitDecision pid)) (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = true ∧ w.wg.dev = some d ∧ w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let inputs := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .retransmitGiveUp, outcome := true,
    operands := some (Int.ofNat p.timerHandshakeAttempts, Int.ofNat MAX_TIMER_HANDSHAKES),
    netRx := initial.ambient.netRxSection}}
  refine ⟨true, {initial with ambient := inputs}, ?_, rfl, device, records⟩
  change (((retransmitDecision pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _
  simp [ retransmitDecision, getPeer, getDev, device, resident, limit,
    branchCmp, AmbientM.branchCmp, inputs]

theorem retransmitGiveUp_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (expiredRetransmitHandshake pid)).run initial = .ok ((), final)) :
    ∃ afterDecision beforeRead caller afterRead,
      (liftWG (retransmitDecision pid)).run initial = .ok (true, afterDecision) ∧
      (liftWG (giveUpArmPrefix pid)).run afterDecision = .ok (true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesRetransmitZeroKey)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid (giveUpWheelPeer p)
        .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller (Campaign2.Product.snapshot final).wg := by
  obtain ⟨decision, afterDecision, hdecision, value, hd, hm⟩ :=
    retransmitDecision_returns pid d p resident limit initial ⟨device, records⟩
  subst decision
  rw [retransmitDecision_source, liftWG_bind_variant, StateT.run_bind, hdecision] at run
  change (liftWG (retransmitGiveUp pid)).run afterDecision = .ok ((), final) at run
  obtain ⟨ready, beforeRead, hprefix, value, hd', hm'⟩ :=
    giveUpArmPrefix_returns pid d p resident absent afterDecision ⟨hd, hm⟩
  subst ready
  rw [giveUpArm_source, liftWG_bind_variant, StateT.run_bind, hprefix] at run
  change (liftWG (discard (modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS) : WG.M Unit)).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
    (giveUpWheelDevice d pid p) (giveUpWheelPeer p) (by simp [giveUpWheelDevice])
    running alive beforeRead final hd' hm' run
  exact ⟨afterDecision, beforeRead, caller, afterRead, hdecision, hprefix, hread, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
