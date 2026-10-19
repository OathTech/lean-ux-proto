import Leanux.Proofs.WG.TimerDiscipline.HookTransmitClaims
import Leanux.Proofs.WG.TimerDiscipline.HookJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUpCurveSource
import Leanux.Proofs.WG.TimerDiscipline.OutgoingTraversalAllModeClaims
import Leanux.Proofs.WG.TimerDiscipline.DataTraversalAllModeClaims
import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalAllModeClaims
import Leanux.Proofs.WG.TimerDiscipline.SessionOriginClaims
import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventClaims
import Leanux.Proofs.WG.TimerDiscipline.PartialExchangeArmClaims
import Leanux.Proofs.WG.TimerDiscipline.ActualRetryBlockClaims
import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentClaims
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeClaims
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstReceiptClaims
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryBoundaryClaims
import Leanux.Proofs.WG.TimerDiscipline.ArmingSourceClaims
import Leanux.Proofs.WG.TimerDiscipline.HookObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.ObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.JitterBoundClaims
import Leanux.Proofs.WG.TimerDiscipline.JitterOutcomeClaims
import Leanux.Proofs.WG.TimerDiscipline.SourceFrames
import Leanux.Proofs.WG.TimerDiscipline.RecordedSourceClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.PendingGiveUpSource
import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpClaims
import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.SendReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.WorkerReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.FireReadyClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- A normal recorded arm retains the caller-clock gap and exact current WG effect: timer registration, unchanged-expiry shortcut, and any wheel placement/counter update. The arbitrary entry snapshot adds no readiness condition. -/
theorem original_recorded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (armTimer pid timer delay (some caller))
      (fun s => s = entry ∧ s.ambient.armRecords = true ∧ s.peerAt pid = some p)
      (fun _ final => ∃ now unit,
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
        if p.timer timer = some (caller + delay.toUInt64) then
          final.wg = recordedArmPrefixView entry.wg pid timer now unit
        else ∃ clk, final.wg = wheelPlacementView
          {recordedArmPrefixView entry.wg pid timer now unit with timerClk := some clk}
          pid p timer (caller + delay.toUInt64) clk) :=
  source_recorded_arm pid timer delay caller p entry

/-- Deletion clears both the expiry and wheel entry and preserves every other native observation. -/
theorem original_delete (pid : PeerId) (timer : PeerTimer) (p : Peer)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (delTimer pid timer)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p timer) :=
  source_delete pid timer p entry

/-- The arm guard returns running and not dead and leaves the device unchanged. -/
theorem original_arm_guard (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (modPeerTimerGuard pid) (fun s => s.wg.device = some d)
      (fun allowed s => allowed = (d.running && !p.isDead) ∧ s.wg.device = some d) :=
  source_arm_guard pid d p resident

/-- A normal guarded arm reports the running/live guard and its complete current WG effect; the failed guard preserves the WG state. -/
theorem original_guarded_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (modPeerTimer site pid timer delay)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun allowed final => allowed = (d.running && !p.isDead) ∧
        if allowed then peerTimerArmEffect entry pid p timer delay final.wg
        else final.wg = entry.wg) :=
  source_guarded_arm site pid timer delay d p resident entry

/-- Traversal retains the interval/running/live guards and the complete current persistent-keepalive wheel effect. Disabled traversal preserves the WG state. -/
theorem original_traversal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersTraversal pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
        peerTimerArmEffect entry pid p .persistentKeepalive (p.persistentKeepaliveInterval * HZ) final.wg
      else final.wg = entry.wg) :=
  source_traversal pid d p resident entry

/-- Session-derived arming retains the running/live guards and the complete current zero-key wheel effect; the failed guard preserves the WG state. -/
theorem original_session_derived (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersSessionDerived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running && !p.isDead then
        peerTimerArmEffect entry pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final.wg
      else final.wg = entry.wg) :=
  source_session_derived pid d p resident entry

/-- Receipt preserves the original running/pending/dead cases. An absent live timer has the current wheel effect; a pending timer sets the additional-keepalive flag. -/
theorem original_data_received (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersDataReceived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running then
        if p.timerPending .sendKeepalive then
          final.wg = {entry.wg with device := some {d with peers := d.peers.insert pid {p with timerNeedAnotherKeepalive := true}}}
        else if p.isDead then final.wg = entry.wg
        else peerTimerArmEffect entry pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS final.wg
      else final.wg = entry.wg) :=
  source_data_received pid d p resident entry

/-- Handshake completion clears both retransmit expiry and wheel entry, resets attempts and the last-minute flag, and records the actual wall-clock bytes. -/
theorem original_handshake_complete (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Campaign2.Ensures (timersHandshakeComplete pid site)
      (fun s => s.peerAt pid = some p)
      (fun _ s => ∃ now, s.peerAt pid = some
        {((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
          walltimeLastHandshake := now}) :=
  source_handshake_complete pid site p

/-- Every successful jitter draw returns fewer than HZ/3 ticks and leaves
the WireGuard core unchanged. This normal-completion contract does not characterize errors. -/
theorem original_jitter_bound (site : HiddenSite) (initial : Core) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site) (fun s => s.wg.toCore = initial)
      (fun n s => s.wg.toCore = initial ∧ n < HZ / 3) :=
  projected_jitter_bound site initial

/-- Authenticated sending clears send-keepalive expiry and wheel entry, preserving the remaining native snapshot. -/
theorem original_authenticated_sent (pid : PeerId) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketSent pid)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p .sendKeepalive) :=
  source_authenticated_sent pid p entry

/-- Authenticated receipt clears new-handshake expiry and wheel entry, preserving the remaining native snapshot. -/
theorem original_authenticated_received (pid : PeerId) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketReceived pid)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p .newHandshake) :=
  source_authenticated_received pid p entry

/-- The original retransmit callback increments attempts through 18 to 19,
then leaves the count unchanged on give-up. Every normal completion preserves
the peer's allocation identity and retransmit-timer field; rearming belongs
to the later handshake worker. This is a callback contract, not a whole episode. -/
theorem original_retransmit_counter (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) (fun s => s.peerAt pid = some p)
      (fun _ s => ∃ q, s.peerAt pid = some q ∧ q.internalId = p.internalId ∧
        q.timerHandshakeAttempts =
          (if p.timerHandshakeAttempts > 18 then p.timerHandshakeAttempts else p.timerHandshakeAttempts + 1) ∧
        q.timerRetransmitHandshake = p.timerRetransmitHandshake) :=
  source_retransmit_counter pid p

/-- The actual recorded caller read and guarded arm retain full Product observations. Successful arming has its current registration and wheel effect; the failed guard preserves WG state. -/
theorem original_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (modPeerTimer site pid timer delay)) (liftWG (callerJiffies site)))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧ result.2 = (d.running && !p.isDead) ∧
        if result.2 then
          recordedTimerEffect entry.wg pid p timer delay caller final.wg
        else final.wg = entry.wg) :=
  projected_guarded_arm_recorded site pid timer delay d p resident entry

/-- A recorded session-derived hook on a running live peer uses the actual caller read and the complete zero-key wheel effect at its original delay. -/
theorem original_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (timersSessionDerived pid))
      (liftWG (callerJiffies .timerJiffiesSessionDerived)))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧
        recordedTimerEffect entry.wg pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller final.wg) :=
  projected_session_derived_recorded pid d p resident running alive entry

/-- Recorded handshake initiation observes the original caller then bounded jitter and retains the complete retransmit wheel effect, including same-expiry and placement cases. -/
theorem original_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (timersHandshakeInitiated pid))
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead jitter afterJitter,
        result.1 = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        recordedTimerEffect entry.wg pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller final.wg) :=
  projected_handshake_initiated_recorded pid d p resident running alive entry

/-- Recorded data sending preserves the original absent/running/live domain and ordered prefix, caller and jitter observations, with the complete new-handshake wheel effect. -/
theorem original_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersDataSent pid))
      (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead jitter afterJitter,
        result.1 = .ok ((true, beforeRead, some caller, afterRead, jitter), afterJitter) ∧
        jitter < HZ / 3 ∧ recordedTimerEffect beforeRead.wg pid p .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller final.wg) :=
  projected_data_sent_recorded pid d p resident absent running alive

/-- Recorded traversal preserves the original nonzero-interval/running/live domain and actual prefix/caller observations, with the complete persistent-keepalive wheel effect. -/
theorem original_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok (((p.persistentKeepaliveInterval, true), beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid p .persistentKeepalive
          (p.persistentKeepaliveInterval * HZ) caller final.wg) :=
  projected_traversal_recorded pid d p resident enabled running alive

/-- Recorded data receipt preserves the original absent/running/live domain and actual prefix/caller observations, with the complete send-keepalive wheel effect. -/
theorem original_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersDataReceived pid))
      (prefixClockPath (liftWG (dataReceivedPrefix pid)) .timerJiffiesDataReceived))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok ((some true, beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller final.wg) :=
  projected_data_received_recorded pid d p resident absent running alive

/-- The keepalive rearm contract applies at the actual post-send cut under the original needed/running/live premises. It clears the flag and records the complete wheel effect. -/
theorem original_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (needed : p.timerNeedAnotherKeepalive = true)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (expiredSendKeepalive pid))
      (prefixInspect (liftWG (sendKeepalive pid))
        (prefixClockPath (liftWG (keepaliveRearmPrefix pid)) .timerJiffiesExpiredKeepalive)))
      (fun _ => True)
      (fun result final => ∀ choice afterSend tail,
        result.1 = .ok ((choice, afterSend, tail), afterSend) →
        afterSend.wg.device = some d → afterSend.ambient.armRecords = true →
        ∃ beforeRead caller afterRead,
          tail = .ok ((true, beforeRead, some caller), afterRead) ∧
          recordedTimerEffect beforeRead.wg pid {p with timerNeedAnotherKeepalive := false}
            .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller final.wg) :=
  projected_expired_keepalive_recorded pid d p resident needed running alive

/-- Recorded give-up retains both actual decision cuts, the original attempt/absence/running/live domain, and the zero-key wheel effect after send-keepalive deletion and staged purge. -/
theorem original_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (expiredRetransmitHandshake pid)) (giveUpClockPath pid))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ afterDecision beforeRead caller afterRead,
        result.1 = .ok ((true, afterDecision, true, beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid (giveUpWheelPeer p) .zeroKeyMaterial
          ZERO_KEY_MATERIAL_TICKS caller final.wg) :=
  projected_retransmit_giveup_recorded pid d p resident limit absent running alive

/-- Corrected to an already selected wheel unit. Every normal completion retains
its actual prefix and final Product observations, validates the worker kind, and
preserves the entry device through the prefix. This does not establish outer
wheel selection, peer-list membership, a logical expiry, or readiness by a horizon. -/
theorem original_timer_dispatch_due (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (d : Device) :
    Campaign2.Product.Ensures (observed (timerDispatchUnit_variant worker pid timer we step)
      (timerExecutionPath worker pid timer we step))
      (fun s => s.wg.device = some d)
      (fun result final => ∃ selected,
        result.1 = .ok ((pid, timer, selected), final) ∧
        worker.timer? = some timer ∧ selected.wg.device = some d) :=
  projected_timer_dispatch_due worker pid timer we step d

/-- Corrected to the actual selected retransmit wheel unit. On normal completion,
its actual successful prefix observation gives the original identity, next-attempt
and detached-expiry postcondition. All Product snapshot fields remain observable.
No outer wheel selection, complete timer pass, or later worker rearming is asserted. -/
theorem original_retransmit_dispatch (pid : PeerId) (we : WheelEntry) (step : Option UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Campaign2.Product.Ensures (observed
      (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we step)
      (do timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step
          pure (pid, PeerTimer.retransmitHandshake)))
      (fun s => retryObservation s.toSnapshot pid = some (identity, attempts, timer))
      (fun result final => ∀ selected,
        result.1 = .ok ((pid, .retransmitHandshake), selected) →
        retryObservation final.toSnapshot pid = some (identity, nextAttempts attempts, none)) :=
  projected_retransmit_dispatch pid we step identity attempts timer

/-- Every normal original handshake send either exits in its actual prefix
or executes the final retransmit arm hook. Reaching the hook means creation
succeeded, not that the ignored socket-send result was successful. The prefix
retains rate-limit and creation decisions and every intervening operation. -/
theorem original_initiation_arm_path (pid : PeerId) :
    Campaign2.Product.Ensures (observed (liftWG (sendHandshakeInitiation pid)) (initiationExecutionPath pid))
      (fun _ => True)
      (fun result final => ∃ reached beforeArm,
        result.1 = .ok ((reached, beforeArm), final) ∧
        (reached = false → final = beforeArm)) :=
  projected_initiation_arm_path pid

/-- At the actual reached initiation hook, the original running/live/recorded conditions give ordered caller/jitter observations and the complete retransmit wheel effect. No completion or transmission guarantee is added. -/
theorem original_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (sendHandshakeInitiation pid))
      (prefixInspect (liftWG (initiationArmPrefix pid))
        (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter)))
      (fun _ => True)
      (fun result final => ∀ reached afterPrefix tail,
        result.1 = .ok ((reached, afterPrefix, tail), afterPrefix) → reached = true →
        afterPrefix.wg.device = some d → afterPrefix.ambient.armRecords = true →
        ∃ caller afterRead jitter afterJitter,
          tail = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
          recordedTimerEffect afterPrefix.wg pid p .retransmitHandshake
            (REKEY_TIMEOUT_TICKS + jitter) caller final.wg) :=
  projected_initiation_send_arm pid d p resident running alive

/-- At either original timer-jitter site, a finite contiguous rejected-draw
prefix followed by an accepted byte returns that byte's scaled jitter, consumes
exactly those records and preserves the entire remaining projected state. Records use the
original one-byte payload with seven padding zeros; arbitrary suffixes remain.
This is total execution of the original sampler, not a distribution claim. -/
theorem original_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some (jitterStream site rejected accepted rest))
      (fun initial out => out = .ok (jitterValue accepted,
        {initial with ambient := {initial.ambient with hidden := some rest}})) :=
  projected_jitter_records site rejected accepted rest bad good

/-- A finite contiguous stream containing only rejected jitter bytes ends at
the exact original missing-record error. The record-derived budget includes the
extra read, so this is hidden-input exhaustion before budget exhaustion. Empty
streams are included; recordless placeholder execution and ambient interleavings
are outside this contract. -/
theorem original_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some (rejected.map (jitterRecord site)))
      (fun _ out => out = .error (.hidden s!"no record left for {site.hiddenSite.info.label}")) :=
  projected_jitter_exhausted site rejected bad

/-- A normally completed original initiation-send prefix preserves the peer's
allocation identity, retry-attempt count, reference count and retransmit expiry.
This includes message construction, MAC, traversal, socket/cache/accounting
updates and the original early exits; the retransmit arm hook follows it. -/
theorem original_initiation_prefix_frame (pid : PeerId) (identity attempts refs : Nat)
    (expiry : Option UInt64) :
    Campaign2.Ensures (initiationArmPrefix pid)
      (fun w => initiationObservation w pid = some (identity, attempts, refs, expiry))
      (fun _ w => initiationObservation w pid = some (identity, attempts, refs, expiry)) := by
  intro g ambient value final after pre run
  exact source_initiation_prefix_frame pid identity attempts refs expiry g ambient value final after pre run

/-- Original initiation sending preserves peer identity, retry attempts and
references whenever it returns normally. Its final hook may change the
retransmit expiry. A normal return does not assert transmission success. -/
theorem original_handshake_send_frame (pid : PeerId) (identity attempts refs : Nat) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun w => workerObservation w pid = some (identity, attempts, refs))
      (fun _ w => workerObservation w pid = some (identity, attempts, refs)) := by
  intro g ambient value final after pre run
  exact source_handshake_send_frame pid identity attempts refs g ambient value final after pre run

/-- A normally returning original handshake-send worker preserves identity and
retry attempts and releases one reference. More than one entry reference keeps
the peer resident after that release. This is the worker body, before composition
with the environment's selection/dequeue and a complete retry episode. -/
theorem original_send_worker_frame (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Campaign2.Ensures (handshakeSendWorker pid)
      (fun w => workerObservation w pid = some (identity, attempts, refs))
      (fun _ w => workerObservation w pid = some (identity, attempts, refs - 1)) := by
  intro g ambient value final after pre run
  exact source_send_worker_frame pid identity attempts refs retained g ambient value final after pre run

/-- A normally completed original environment send dispatch selects the queue
head or the first matching named association, erases one queue occurrence, and
requires the selected peer's pending flag, then sets it to residual queue
membership before its section starts; duplicates can leave it true.
The observations retain the actual ordered section reads and worker execution.
The retained peer keeps its identity and attempt count and loses one reference.
No final queue or pending-flag frame, or successful transmission, is asserted. -/
theorem original_send_dispatch_path (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Product.Ensures (observed Env.runOneSendWorker sendWorkerExecution)
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun result final => ∃ execution, result.1 = .ok (execution, final) ∧
        CompletedSendWorker d units execution final) :=
  source_send_dispatch_path d units retained

/-- Original scope retained through the native or full Product projection. -/
theorem original_send_dispatch (d : Device) (retained : RetainedSendQueue d) :
    Campaign2.Product.Ensures Env.runOneSendWorker (fun s => s.wg.device = some d)
      (fun _ final => ∃ pid p, pid ∈ d.sendWorkQueue ∧ d.peers[pid]? = some p ∧
        p.handshakePending = true ∧ workerObservation final.toSnapshot pid =
          some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1)) :=
  source_send_dispatch d retained

/-- The supplied selected wheel-unit/send pair retains actual inspection,
empty final queue, cleared pending flag and acquired/released reference.
Exact erasure retains errors. Outer selection, successful transmission and
completion of a scheduler retry episode remain open. -/
theorem original_retry_dispatch (d : Device) (unit : RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetryDispatch unit)
      (fun s => s.wg.device = some d) (RetryDispatchCertificate d unit) :=
  source_retry_dispatch d unit empty

/-- The supplied wheel-unit/send pair retains its inspected retry certificate
and actual initiation prefix and pre-release observations. At a reached arm hook,
the original running/live/record conditions determine its complete wheel effect.
Rearming remains conditional; no outer selection or successful transmission
is asserted, and exact projection/erasure retain errors. -/
theorem original_retry_rearm (d : Device) (unit : RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetryRearm unit)
      (fun s => s.wg.device = some d) (RetryRearmCertificate d unit) :=
  source_retry_rearm d unit empty

/-- Consecutive supplied wheel-unit/send pairs retain adjacent full Product
observations, each pair's inspected eligibility and conditional rearm, and an
empty final send queue. Same-peer successful pairs preserve identity/reference
and increment attempts by the length; a nonempty chain clears pending and bounds
initial attempts plus length by 19. The empty chain preserves its entire snapshot.
This is not a selection or success guarantee for an outer scheduler episode. -/
theorem original_retry_sequence (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d) (RetrySequenceCertificate d units) :=
  source_retry_sequence d units empty

/-- From zero attempts, at most 19 consecutive supplied wheel-unit/send
pairs can return normally with the same actual selected peer. This excludes
20 successful pairs, without asserting that the twentieth callback fails
or that an outer scheduler selects any of these units. -/
theorem original_retry_sequence_zero_bound (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d)
      (fun result _ => SameRetryPeer pid result.2 → units.length ≤ 19) :=
  source_retry_sequence_zero_bound d units empty pid p resident zero

/-- Response-kind execution and its full Product transcript retain the original session cut and ordered session effect. The reached hook carries its actual guarded zero-key wheel effect; erasure retains all errors. -/
theorem original_response_session_arm (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (receiveHandshakePacket msg src))
      (responseSessionCallPrefix msg src >>= responseSessionCallSuffix msg) ∧
    Campaign2.Product.AgreesOn (fun _ => True) (observedResponseSession msg src)
      (responseSessionTranscript msg src) ∧
    Campaign2.Product.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation) := by
  constructor
  · intro entry pre
    rw [responseSessionCall_source msg src kind]
  · constructor
    · intro entry pre
      rw [observedResponseSession_source msg src kind]
    · exact observedResponseSession_facts msg src kind

/-- Outgoing response execution and its full Product transcript retain the actual creation/session cut and guarded zero-key wheel effect. Early rejection and every original error remain in scope. -/
theorem original_outgoing_response_session_arm (pid : PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (sendHandshakeResponse pid))
      (outgoingResponseSessionPrefix pid >>= outgoingResponseSessionSuffix pid) ∧
    Campaign2.Product.AgreesOn (fun _ => True) (observedOutgoingResponseSession pid)
      (outgoingResponseSessionTranscript pid) ∧
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation) := by
  constructor
  · intro entry pre
    rw [outgoingResponseSession_source pid]
  · constructor
    · intro entry pre
      rw [observedOutgoingResponseSession_source pid]
    · exact observedOutgoingResponseSession_facts pid

/-- Data completion retains ordered packet/send observations and the original hook-presence tests, including an empty item list. Hook facts now include their complete wheel effects; exact Product erasure retains all errors. -/
theorem original_data_done_timers (pid : PeerId) (items : List SkbId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedDataDone pid items; pure ()) (liftWG (createDataDone pid items)) ∧
    Campaign2.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun observation _ => DataDoneFacts pid items observation) := by
  constructor
  · intro entry pre
    rw [observedDataDone_erase pid items]
  · exact observedDataDone_facts pid items

/-- Raw data receipt retains traversal, the keepalive/receipt test, and the complete original suffix. Each actual hook cut records its current wheel effect; exact Product erasure retains the packet option and all errors. -/
theorem original_consume_data_done_timers (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let result ← observedRxDataTimers pid pkt e; pure result.2)
      (liftWG (consumeDataDone pid pkt e)) ∧
    Campaign2.Product.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1) := by
  constructor
  · intro entry pre
    rw [observedRxDataTimers_erase pid pkt e]
  · exact observedRxDataTimers_facts pid pkt e

/-- Outgoing response traversal retains its actual successful-session cut and complete guarded persistent-keepalive wheel effect. Exact Product erasure includes all errors and makes no final-expiry or delivery claim. -/
theorem original_outgoing_response_traversal (pid : PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedResponseTraversal pid; pure ()) (liftWG (sendHandshakeResponse pid)) ∧
    Campaign2.Product.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  constructor
  · intro entry pre
    rw [observedResponseTraversal_erase pid]
  · exact observedResponseTraversal_facts pid

/-- Outgoing initiation traversal retains its actual creation-prefix cut and complete guarded persistent-keepalive wheel effect. Both source factor and Product erasure preserve errors and early exits. -/
theorem original_outgoing_initiation_traversal (pid : PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftWG (initiationTraversalPrelude pid >>= initiationTraversalSuffix pid))
      (liftWG (sendHandshakeInitiation pid)) ∧
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationTraversal pid; pure ()) (liftWG (sendHandshakeInitiation pid)) ∧
    Campaign2.Product.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut) := by
  constructor
  · intro entry pre
    rw [initiationTraversal_source pid]
  · constructor
    · intro entry pre
      rw [observedInitiationTraversal_erase pid]
    · exact observedInitiationTraversal_facts pid

/-- Initiation receipt retains the actual accepted consumer/MAC certificate and traversal cut, including complete guarded wheel effects. Product erasure preserves every original error; rejected paths may have no cut. -/
theorem original_initiation_receive_traversal (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationReceiveTraversal msg src; pure ()) (liftWG (receiveHandshakePacket msg src)) ∧
    Campaign2.Product.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut) := by
  constructor
  · intro entry pre
    rw [observedInitiationReceiveTraversal_erase msg src kind]
  · exact observedInitiationReceiveTraversal_facts msg src

/-- Response receipt retains its actual consumer/MAC and session/keepalive prefix before traversal, with complete guarded wheel effects. Product erasure preserves every original error. -/
theorem original_response_receive_traversal (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedResponseReceiveTraversal msg src; pure ()) (liftWG (receiveHandshakePacket msg src)) ∧
    Campaign2.Product.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut) := by
  constructor
  · intro entry pre
    rw [observedResponseReceiveTraversal_erase msg src kind]
  · exact observedResponseReceiveTraversal_facts msg src

/-- At the actual exit of 19 successful same-peer supplied wheel-unit/send
pairs from zero attempts, the immediate callback follows its original give-up
decision and tail, including errors. Normal return preserves the empty queue,
identity and attempt count 19. No intervening scheduler action, further arm,
callback invocation or successful give-up return is assumed. -/
theorem original_retry_boundary (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) (nineteen : units.length = 19)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d)
      (fun result boundary => SameRetryPeer pid result.2 →
        Campaign2.Product.AgreesOn (fun s => s = boundary)
          (liftWG (expiredRetransmitHandshake pid))
          (liftWG (do let _ ← retransmitDecision pid; retransmitGiveUp pid)) ∧
        Campaign2.Product.Ensures (liftWG (expiredRetransmitHandshake pid)) (fun s => s = boundary)
          (fun _ final => final.wg.device.map Device.sendWorkQueue = some [] ∧
            ∃ q, final.toSnapshot.peerAt pid = some q ∧ q.internalId = p.internalId ∧
              q.timerHandshakeAttempts = 19)) :=
  source_retry_boundary d units empty nineteen pid p resident zero

/-- Pending-zero-key give-up remains total on the original resident/attempt domain. The full Product effect includes clearing send-keepalive expiry and wheel entry and purging staged packets. -/
theorem original_giveup_pending_zero_key (pid : PeerId) (d : Device) (p : Peer) (expiry : UInt64)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Returns (liftWG (expiredRetransmitHandshake pid))
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => final = pendingGiveUpView entry d pid p) :=
  pendingGiveUp_returns pid d p expiry resident limit pending entry

/-- The original supplied-record give-up domain gives exact Product agreement with the actual arm continuation, including timer-clock and wheel-record refusals. It no longer asserts unconditional completion. -/
theorem original_giveup_absent_zero_key (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : Product.Snapshot) :
    Product.AgreesOn
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (liftWG (expiredRetransmitHandshake pid))
      (absentGiveUpArmContinuation pid d p input rest) :=
  absentGiveUp_returns pid d p input rest resident limit absent running alive valid entry

/-- The original retransmit-hook record domain gives exact Product agreement with the actual caller/jitter/guard/arm continuation, including refusals and the inactive guard path. -/
theorem original_retransmit_hook_ready (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (valid : input.Valid) (entry : Product.Snapshot) :
    Product.AgreesOn
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (liftWG (timersHandshakeInitiated pid))
      (retransmitHookContinuation pid d p input rest) :=
  retransmitHook_returns pid d p input rest resident valid entry

/-- The original creation and send-tail domain gives exact Product agreement through actual creation and current wheel arming. All supplied records, allocation conditions and failures are retained; unconditional completion is not asserted. -/
theorem original_send_initiation_ready (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (rate last ephemeral clock tailClock : List UInt8)
    (rateLen : rate.length = 8) (lastLen : last.length = 8)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ SendReady.initiationTailClock rate)
    (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false)
    (createdPeer : Peer)
    (createdResident : (SendReady.sendCreationResult pid d p last ephemeral clock fresh.value).2.peers[pid]? = some createdPeer)
    (cookieInvalid : createdPeer.cookieIsValid = false)
    (interval : createdPeer.persistentKeepaliveInterval = 0)
    (endpoint : createdPeer.endpoint = none)
    (running : (SendReady.sendCreationResult pid d p last ephemeral clock fresh.value).2.running = true)
    (alive : createdPeer.isDead = false)
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid) :
    Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧ s.ambient.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
        {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
        Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)))
      (liftWG (sendHandshakeInitiation pid))
      (SendReady.sendInitiationContinuation pid d p createdPeer rate last ephemeral clock tailClock
        collisions fresh input rest) :=
  SendReady.sendInitiation_projected pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh createdPeer createdResident cookieInvalid interval endpoint running alive tailLen input valid

/-- The original ready domain applies to the actual selected retransmit wheel unit; horizon/due premises remain explicit. The full Product result includes wheel detachment, pass-step reset and queuedThisCall preservation. Outer wheel selection and whole runTimers completion are separate claims. -/
theorem original_fire_retry_ready (d : Device) (p : Peer) (pid : PeerId) (horizon : UInt64) (we : WheelEntry)
    (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (startLen : start.length=16) (stopLen : stop.length=8)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (nonzero : recordWordOf start 1 ≠ 0)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead=false) (pending : p.handshakePending=false)
    (positive : 0<p.refcount) (bounded : p.refcount+1<2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64*NSEC_PER_SEC64 ≤ (RetryReady.word clock).toInt64) :
    Campaign2.Product.Observes (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we none)
      (fun s => s.wg.device=some d ∧
        s.ambient.hidden=some (FireReady.suppliedRecords start cache clock queue stop suffix) ∧
        s.ambient.armRecords=true ∧ s.wg.dstCacheRecords=true ∧
        s.wg.timerUnits.find? (·.1 == recordWordOf start 1) =
          some (recordWordOf start 1,pid,.retransmitHandshake) ∧
        s.ambient.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
          some (recordWordOf queue 0,Worker.sendWorker.index,pid))
      (fun entry outcome => outcome=.ok ((),FireReady.fireView entry d p pid cache clock suffix)) :=
  FireReady.fire_outcome d p pid horizon we start cache clock queue stop suffix resident due
    startLen stopLen cacheLen clockLen queueLen nonzero limit alive pending positive bounded expired

/-- The original named-worker domain gives exact Product agreement through selection, dequeue, creation, arm, release and stop. Residual duplicate queue membership determines pending, and all arm/release/section refusals remain visible. -/
theorem original_send_worker_ready (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (rate last ephemeral clock tailClock : List UInt8)
    (rateLen : rate.length = 8) (lastLen : last.length = 8)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ SendReady.initiationTailClock rate)
    (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false)
    (createdPeer : Peer)
    (createdResident : (SendReady.sendCreationResult pid (dequeuedSendDevice d pid p) {p with handshakePending := false} last ephemeral clock fresh.value).2.peers[pid]? = some createdPeer)
    (cookieInvalid : createdPeer.cookieIsValid = false)
    (interval : createdPeer.persistentKeepaliveInterval = 0)
    (endpoint : createdPeer.endpoint = none)
    (running : (SendReady.sendCreationResult pid (dequeuedSendDevice d pid p) {p with handshakePending := false} last ephemeral clock fresh.value).2.running = true)
    (alive : createdPeer.isDead = false)
    (retained : 1 < createdPeer.refcount)
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid)

    (headPid unit : Nat) (head : d.sendWorkQueue.head? = some headPid)
    (queued : pid ∈ d.sendWorkQueue) (pending : p.handshakePending = true)
    (start stop : List UInt8) (startLen : start.length = 16) (stopLen : stop.length = 8)
    (address : recordWordOf start 1 = unit) (nonnullUnit : unit ≠ 0) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧
        s.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
          some (unit, Worker.sendWorker.index, pid) ∧
        s.ambient.hidden = some (WorkerReady.records start rate last ephemeral clock tailClock stop collisions fresh input rest))
      Env.runOneSendWorker
      (WorkerReady.runOneSendWorkerContinuation pid d p createdPeer rate last ephemeral clock tailClock stop
        collisions fresh input rest) :=
  WorkerReady.runOneSendWorker_projected pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh createdPeer createdResident cookieInvalid interval endpoint running alive retained tailLen input valid headPid unit head queued pending start stop startLen stopLen address nonnullUnit

/-- First-turn connection to the actual outer scheduler. This does not assert
that every due timer is selected, nor that the callback or suffix succeeds. -/
theorem original_run_timers_first_selected (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) :
    Campaign2.Product.AgreesOn (FirstTimerSelected jPass worker pid timer we)
      (Env.runTimers jPass) (firstTimerSelectedSource jPass worker pid timer we) :=
  runTimers_first_timer_agrees jPass worker pid timer we

/-- Receipt for the first actual outer retransmit unit, with its effect before
the original continuation. No final-state retry-count claim is made. -/
theorem original_run_timers_first_retransmit_receipt (jPass : UInt64) (pid : PeerId) (we : WheelEntry)
    (identity attempts : Nat) (expiry : Option UInt64) :
    Campaign2.Product.Ensures
      (observed (Env.runTimers jPass)
        (firstTimerReceiptPath jPass .timerRetransmit pid .retransmitHandshake we))
      (fun entry => FirstTimerSelected jPass .timerRetransmit pid .retransmitHandshake we entry ∧
        retryObservation entry.toSnapshot pid = some (identity, attempts, expiry))
      (fun result final => ∃ remaining selected afterUnit,
        result.1 = .ok ((remaining, (pid, .retransmitHandshake, selected),
          .ok (result.2, final)), afterUnit) ∧
        retryObservation selected.toSnapshot pid = some (identity, attempts, expiry) ∧
        retryObservation afterUnit.toSnapshot pid = some (identity, nextAttempts attempts, none)) :=
  runTimers_first_retransmit_receipt jPass pid we identity attempts expiry

/-- One actual complete `runTimers` episode, with every executed turn and its
immediate selected callback receipt. No supplied units, callback readiness,
no-due result or retry bound is assumed or concluded. Stops are retained by
`observedRunTimersEpisode_erase`. -/
theorem original_timer_episode_receipt (jPass : UInt64) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass)
      (fun initial => initial = entry)
      (fun result final => OuterTimerEpisodeValid jPass entry result.1 result.2 final) :=
  runTimers_episode_receipt jPass entry

/-- Conditional retry certificates for adjacent actual retransmit/send turns,
using their immediate snapshots inside a normal original timer episode. This
adds no whole-history pairing, no-due, fairness or retry-19 assertion. -/
theorem original_timer_adjacent_retry_pairs (jPass : UInt64) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass) (fun _ => True)
      (fun result _ => ∀ front suffix left right,
        result.1.turns = front ++ left :: right :: suffix → OuterAdjacentRetryPair jPass left right) :=
  runTimers_adjacent_retry_pairs jPass

/-- A nonempty contiguous block of qualifying same-peer retransmit/send pairs
inside one normal actual timer episode preserves identity and references and
increases attempts by the number of pairs. At its last send exit attempts are
at most 19, pending is false and the send queue is empty. This does not assert
that arbitrary episodes are paired, nor bound retry counts after later turns
or final delivery. All errors remain those of `observedRunTimersEpisode_erase`. -/
theorem original_timer_actual_retry_block_counts (jPass : UInt64) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass) (fun _ => True)
      (fun result _ => ∀ front suffix first rest pid,
        result.1.turns = front ++ actualRetryBlockTurns (first :: rest) ++ suffix →
        (∀ pair ∈ first :: rest, ActualRetryPairMatches jPass pid pair) →
        ActualRetryBlockEffect pid first rest) :=
  runTimers_actual_retry_block_counts jPass

/-- Local give-up execution can arm zero-key without creating a session:
all key slots and the key store remain empty, the handshake remains
CREATED_INITIATION, and the allocation counter stays zero while one wheel
enqueue occurs. This is not a reachable-history counterexample or a claim
about how many arms occurred during any past session. Ambient inputs are
arbitrary except that arm records are off. -/
theorem original_giveUp_arms_without_session_creation :
    Campaign2.Returns (expiredRetransmitHandshake 0)
      (fun s => s.wg = partialExchangeArmView ∧ s.ambient.armRecords = false)
      (fun _ s => s.wg.keypairCounter = 0 ∧ s.wg.timerEnqueues = 1 ∧
        s.wg.device.map (fun d => d.keypairs.isEmpty) = some true ∧
        (s.peerAt 0).map
          (fun p => (p.handshakeState,p.keypairPrevious,p.keypairCurrent,p.keypairNext,p.timerZeroKeyMaterial)) =
          some (HANDSHAKE_CREATED_INITIATION,none,none,none,some ZERO_KEY_MATERIAL_TICKS.toUInt64)) :=
  giveUp_arms_without_session_creation

/-- Each reached session hook in a normal full response call is attached to
its actual allocation serial. The receipt distinguishes a suppressed guard,
logical arming and zero or one wheel enqueue, in both timer-arm modes. It
makes no final-key residency or later-state expiry assertion; original observer
erasure retains all failures. -/
theorem original_response_session_arm_event (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) →
          SessionArmEvent cut.response.consumed.input.pid cut.session) :=
  observedResponseSession_arm_event msg src kind

/-- The full outgoing response carries the same serial-indexed hook receipt.
This counts the hook at an actual successful session cut, not all arms in a
mixed history or survival of a keypair after aliased rotation. Original Stops
remain those of the existing full-call observer. -/
theorem original_outgoing_response_session_arm_event (pid : PeerId) :
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) →
          SessionArmEvent pid cut.session) :=
  observedOutgoingResponseSession_arm_event pid

/-- A normal full outgoing response labels every reached session event from
its actual call-entry allocation serial. The all-mode hook effect and original
complete observation remain. This makes no final-call counter-delta,
cross-call uniqueness or final-key-residency claim; the original observer
erasure retains all Stops. -/
theorem original_outgoing_session_counter_origin (pid : PeerId)
    (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid)
      (fun initial => initial = entry)
      (fun observation _ => OutgoingResponseSessionObservation pid observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) →
          SessionArmEvent pid cut.session ∧
          cut.session.beforeSession.wg.keypairCounter = entry.wg.keypairCounter) :=
  observedOutgoingResponseSession_counter_origin pid entry

/-- Full original initiation receive erasure preserves every Stop. On a
normal authenticated return, the existing cut has its exact all-mode persistent
keepalive effect; the resident peer is derived and disabled guards are retained.
The claim concerns the immediate hook boundary, not final expiry or delivery. -/
theorem original_initiation_receive_traversal_all_modes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationReceiveTraversal msg src; pure ())
      (liftWG (receiveHandshakePacket msg src)) ∧
    Campaign2.Product.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut ∧
        TraversalAllModeEffect cut.authentication.consumed.pid
          cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedInitiationReceiveTraversal_erase msg src kind]
  · exact observedInitiationReceiveTraversal_all_modes msg src

/-- Full original response receive erasure preserves every Stop. On a
normal authenticated return, the existing cut has its exact all-mode persistent
keepalive effect; the resident peer is derived and disabled guards are retained.
The claim concerns the immediate hook boundary, not final expiry or delivery. -/
theorem original_response_receive_traversal_all_modes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedResponseReceiveTraversal msg src; pure ())
      (liftWG (receiveHandshakePacket msg src)) ∧
    Campaign2.Product.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut ∧
        TraversalAllModeEffect cut.authentication.consumed.input.pid
          cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedResponseReceiveTraversal_erase msg src kind]
  · exact observedResponseReceiveTraversal_all_modes msg src

/-- The actual outgoing initiation retains its optional creation/traversal
certificate and now the reached hook's all-mode WG effect. Erasure preserves
early exits and all original Stops; no final expiry or delivery is asserted. -/
theorem original_outgoing_initiation_traversal_all_modes (pid : PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationTraversal pid; pure ())
      (liftWG (sendHandshakeInitiation pid)) ∧
    Campaign2.Product.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut ∧
        ∀ hook, cut.traversal = some hook →
          TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedInitiationTraversal_erase pid]
  · exact observedInitiationTraversal_all_modes pid

/-- The actual outgoing response retains its session-selected traversal cut,
with the exact all-mode effect before the unchanged send suffix. Erasure
preserves refusals and every original Stop; session success is a result, not
an added entry premise. -/
theorem original_outgoing_response_traversal_all_modes (pid : PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedResponseTraversal pid; pure ())
      (liftWG (sendHandshakeResponse pid)) ∧
    Campaign2.Product.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut ∧
        ∀ hook, cut.traversal = some hook →
          TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedResponseTraversal_erase pid]
  · exact observedResponseTraversal_all_modes pid

/-- Actual encrypted-item completion has one initial traversal even for an
empty item list. Ordered packet/send and later data-sent facts are retained,
with an all-mode immediate traversal effect and exact original error erasure.
No per-packet traversal count or final expiry/delivery claim is made. -/
theorem original_data_done_traversal_all_modes (pid : PeerId) (items : List SkbId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedDataDone pid items; pure ())
      (liftWG (createDataDone pid items)) ∧
    Campaign2.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => DataDoneFacts pid items cut ∧
        TraversalAllModeEffect pid cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedDataDone_erase pid items]
  · exact observedDataDone_all_modes pid items

/-- Raw consumeDataDone invocation retains its original return, receipt gating
and cuts, now including the all-mode immediate traversal effect after its real
endpoint/confirmation/keep-fresh prelude. No upstream authentication or inner
packet acceptance is inferred. Erasure preserves the return and every Stop. -/
theorem original_consume_data_done_traversal_all_modes (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let result ← observedRxDataTimers pid pkt e; pure result.2)
      (liftWG (consumeDataDone pid pkt e)) ∧
    Campaign2.Product.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1 ∧
        TraversalAllModeEffect pid result.1.traversal.before.toSnapshot result.1.traversal.after.toSnapshot) := by
  constructor
  · intro entry pre
    rw [observedRxDataTimers_erase pid pkt e]
  · exact observedRxDataTimers_all_modes pid pkt e


/-- Every reached original runTimers invocation retains its actual bound, source
entry and exact outcome. Normal receipts carry every original wheel turn;
failed episodes retain their Stop without a completed turn-list claim. -/
theorem original_initialized_wheel_episode_journal (trace : Runner.Trace) (placeholders : Bool) :
    (EpisodeJournal.Initialized.inspection trace placeholders).1.map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (EpisodeJournal.Initialized.inspection trace placeholders).2,
      EpisodeJournal.Valid receipt :=
  EpisodeJournal.Initialized.original_initialized_episodes trace placeholders

/-- Original deferred callers preserve timer-episode receipts before later
failures, with the exact original outcome and successful wheel-chain facts. -/
theorem original_deferred_wheel_episode_journal (call : Lifetimes.EnvDeferredCall) :
    (do let result←EpisodeJournal.inspectDeferred call; pure result.1) =
      Campaign2.Product.inspect call.original ∧
    Campaign2.Product.Returns (EpisodeJournal.inspectDeferred call) (fun _=>True)
      (fun result _=>∀receipt∈result.2,EpisodeJournal.Valid receipt) :=
  EpisodeJournal.original_deferred_episodes call


/-- Each of the eight original hook invocations has a source-linked projected
receipt, including Stop. Caller occurrence is supplied by caller observers. -/
theorem original_timer_hook_receipt (hook : HookJournal.Hook) (peer : PeerId) :
    Campaign2.Observes (HookJournal.action hook peer) (fun _=>True)
      (fun before outcome=>(⟨hook,peer,before,outcome⟩ : HookJournal.Receipt).Valid) :=
  HookJournal.original_receipt hook peer

/-- A successful session-derived hook preserves its actual allocation stamp
and enqueues zero or one wheel entry; this is not a cross-call count. -/
theorem original_session_hook_receipt_counters {receipt : HookJournal.Receipt}
    (valid : receipt.Valid) (kind : receipt.hook = .sessionDerived)
    (device : Device) (peer : Peer)
    (present : receipt.before.wg.device = some device)
    (resident : device.peers[receipt.pid]? = some peer)
    {after : Campaign2.Snapshot} (normal : receipt.outcome = .ok ((),after)) :
    after.wg.keypairCounter = receipt.before.wg.keypairCounter ∧
    (after.wg.timerEnqueues = receipt.before.wg.timerEnqueues ∨
      after.wg.timerEnqueues = receipt.before.wg.timerEnqueues + 1) :=
  valid.sessionDerived_counters kind device peer present resident normal

/-- The complete original encrypted-data completion caller retains each
reached timer-hook receipt and the exact original result, including Stop. -/
theorem original_transmit_hook_journal (peer : PeerId) (items : List SkbId) :
    (do let result←HookJournal.Transmit.inspection peer items; pure result.1) =
      Campaign2.inspect (createDataDone peer items) ∧
    Campaign2.Returns (HookJournal.Transmit.inspection peer items) (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  HookJournal.Transmit.original peer items

end Leanux.Proofs.WG.TimerDiscipline
