import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (initial final : World) (result : Bool) (device : initial.wg.dev = some d)
    (records : initial.ambient.armRecords = true)
    (run : (liftWG (modPeerTimer site pid timer delay)).run initial = .ok (result, final)) :
    ∃ caller afterRead,
      (liftWG (callerJiffies site)).run initial = .ok (some caller, afterRead) ∧
      result = (d.running && !p.isDead) ∧
      if result then
        recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p timer delay caller
          (Campaign2.Product.snapshot final).wg
      else (Campaign2.Product.snapshot final).wg = (Campaign2.Product.snapshot initial).wg :=
  modPeerTimer_recorded_clock site pid timer delay d p resident initial final result device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersSessionDerived pid)).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (liftWG (callerJiffies .timerJiffiesSessionDerived)).run initial = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p .zeroKeyMaterial
        ZERO_KEY_MATERIAL_TICKS caller (Campaign2.Product.snapshot final).wg :=
  sessionDerived_recorded_clock pid d p resident running alive initial final device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersDataSent pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead jitter afterJitter,
      (liftWG (dataSentPrefix pid)).run initial = .ok (true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesDataSent)).run beforeRead = .ok (some caller, afterRead) ∧
      (liftWG (jitterBelowRekeyTimeout .newHandshakeJitter)).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .newHandshake
        (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller
        (Campaign2.Product.snapshot final).wg :=
  dataSent_recorded_clock pid d p resident absent running alive initial final device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersTraversal pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (liftWG (traversalPrefix pid)).run initial = .ok ((p.persistentKeepaliveInterval, true), beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesTraversal)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ) caller (Campaign2.Product.snapshot final).wg :=
  traversal_recorded_clock pid d p resident enabled running alive initial final device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersDataReceived pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (liftWG (dataReceivedPrefix pid)).run initial = .ok (some true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesDataReceived)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .sendKeepalive
        KEEPALIVE_TIMEOUT_TICKS caller (Campaign2.Product.snapshot final).wg :=
  dataReceived_recorded_clock pid d p resident absent running alive initial final device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
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
        (Campaign2.Product.snapshot final).wg :=
  expiredKeepalive_recorded_clock pid d p resident needed running alive initial afterSend final send device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
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
        .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller (Campaign2.Product.snapshot final).wg :=
  retransmitGiveUp_recorded_clock pid d p resident limit absent running alive initial final device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_initiation_arm_path (pid : PeerId) (initial final : World)
    (run : (liftWG (sendHandshakeInitiation pid)).run initial = .ok ((), final)) :
    ∃ reached beforeArm,
      (liftWG (initiationArmPrefix pid)).run initial = .ok (reached, beforeArm) ∧
      if reached then (liftWG (timersHandshakeInitiated pid)).run beforeArm = .ok ((), final)
      else final = beforeArm :=
  sendInitiation_arm_execution pid initial final run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial afterPrefix final : World)
    (hprefix : (liftWG (initiationArmPrefix pid)).run initial = .ok (true, afterPrefix))
    (device : afterPrefix.wg.dev = some d) (records : afterPrefix.ambient.armRecords = true)
    (run : (liftWG (sendHandshakeInitiation pid)).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (liftWG (callerJiffies .timerJiffiesHandshakeInitiated)).run afterPrefix = .ok (some caller, afterRead) ∧
      (liftWG (jitterBelowRekeyTimeout .retransmitJitter)).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      recordedTimerEffect (Campaign2.Product.snapshot afterPrefix).wg pid p .retransmitHandshake
        (REKEY_TIMEOUT_TICKS + jitter) caller (Campaign2.Product.snapshot final).wg :=
  sendInitiation_arm_recorded pid d p resident running alive initial afterPrefix final
    hprefix device records run

/-- Current source contract, retaining the original domain and actual execution cuts. -/
theorem source_send_worker_frame (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid) (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) :=
  handshakeSendWorker_workerView pid identity attempts refs retained

/-- Actual ordered caller/jitter reads with the complete wheel effect. -/
theorem source_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersHandshakeInitiated pid)).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (liftWG (callerJiffies .timerJiffiesHandshakeInitiated)).run initial = .ok (some caller, afterRead) ∧
      (liftWG (jitterBelowRekeyTimeout .retransmitJitter)).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter)
        caller (Campaign2.Product.snapshot final).wg := by
  rw [handshakeInitiated_source] at run
  exact jitteredArm_recorded_clock .timerJiffiesHandshakeInitiated .retransmitJitter
    pid .retransmitHandshake REKEY_TIMEOUT_TICKS d p resident running alive
    initial final device records run

end Leanux.Proofs.WG.TimerDiscipline
