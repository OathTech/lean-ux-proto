import Leanux.Proofs.WG.TimerDiscipline.WorkerReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.FireReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.SendReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpClaims
import Leanux.Proofs.WG.TimerDiscipline.PendingGiveUpSource
import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.ObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmClaims
import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryBoundaryClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionClaims

/-! The public H6 interface names only WireGuard and explicit execution
observations. Concrete source connections and residual frames are separate.
`observed_erase` retains exact original errors for decorated prefix claims. -/

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- A successful recorded arm stores exactly caller jiffies plus delay, with unsigned wrapping; the signed gap to the arm read is zero or one tick. -/
theorem original_recorded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) :
    Campaign2.Ensures (armTimer pid timer delay (some caller))
      (fun w => w.wg.armRecords = true ∧ w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, w.wg.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1) :=
  source_recorded_arm pid timer delay caller p

/-- Deleting a timer changes exactly that timer field to absent. -/
theorem original_delete (pid : PeerId) (timer : PeerTimer) (p : Peer) :
    Campaign2.Ensures (delTimer pid timer) (fun w => w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some (p.setTimer timer none)) :=
  source_delete pid timer p

/-- The arm guard returns running and not dead and leaves the device unchanged. -/
theorem original_arm_guard (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (modPeerTimerGuard pid) (fun w => w.wg.device = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧ w.wg.device = some d) :=
  source_arm_guard pid d p resident

/-- A normal guarded arm changes only the selected peer timer when running and alive; otherwise it preserves the peer. -/
theorem original_guarded_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (modPeerTimer site pid timer delay) (fun w => w.wg.device = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧
        if ok then ∃ expiry, w.peerAt pid = some (p.setTimer timer (some expiry))
        else w.peerAt pid = some p) :=
  source_guarded_arm site pid timer delay d p resident

/-- With a nonzero interval and running/live guard, normal traversal has the peer-state effect of setting persistent keepalive to some expiry; otherwise it preserves the peer. -/
theorem original_traversal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (timersTraversal pid) (fun w => w.wg.device = some d)
      (fun _ w => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false
        then ∃ expiry, w.peerAt pid = some (p.setTimer .persistentKeepalive (some expiry))
        else w.peerAt pid = some p) :=
  source_traversal pid d p resident

/-- On normal completion the session-derived hook sets only the zero-key timer to some expiry when running and alive, and otherwise preserves the peer. -/
theorem original_session_derived (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (timersSessionDerived pid) (fun w => w.wg.device = some d)
      (fun _ w => if d.running && !p.isDead
        then ∃ expiry, w.peerAt pid = some (p.setTimer .zeroKeyMaterial (some expiry))
        else w.peerAt pid = some p) :=
  source_session_derived pid d p resident

/-- Data receipt while running arms an absent keepalive timer on a live peer, or requests another keepalive when the timer is already pending. -/
theorem original_data_received (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (timersDataReceived pid) (fun w => w.wg.device = some d)
      (fun _ w => if d.running then
        if p.timerPending .sendKeepalive then
          w.peerAt pid = some { p with timerNeedAnotherKeepalive := true }
        else if p.isDead then w.peerAt pid = some p
        else ∃ expiry, w.peerAt pid = some (p.setTimer .sendKeepalive (some expiry))
        else w.peerAt pid = some p) :=
  source_data_received pid d p resident

/-- Handshake completion deletes the retransmit timer, resets attempts and the last-minute flag, and records the wall-clock bytes; other peer fields are preserved. -/
theorem original_handshake_complete (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Campaign2.Ensures (timersHandshakeComplete pid site) (fun w => w.peerAt pid = some p)
      (fun _ w => ∃ now, w.peerAt pid = some
        { (p.setTimer .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false, walltimeLastHandshake := now }) :=
  source_handshake_complete pid site p

/-- Every successful jitter draw returns fewer than HZ/3 ticks and leaves
the WireGuard core unchanged. This normal-completion contract does not characterize errors. -/
theorem original_jitter_bound (site : HiddenSite) (initial : Core) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site) (fun s => s.wg.toCore = initial)
      (fun n s => s.wg.toCore = initial ∧ n < HZ / 3) :=
  projected_jitter_bound site initial

/-- The authenticated-send hook deletes only the send-keepalive timer. -/
theorem original_authenticated_sent (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketSent pid) (fun w => w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some (p.setTimer .sendKeepalive none)) :=
  source_authenticated_sent pid p

/-- The authenticated-receive hook deletes only the new-handshake timer. -/
theorem original_authenticated_received (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketReceived pid) (fun w => w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some (p.setTimer .newHandshake none)) :=
  source_authenticated_received pid p

/-- The original retransmit callback increments attempts through 18 to 19,
then leaves the count unchanged on give-up. Every normal completion preserves
the peer's allocation identity and retransmit-timer field; rearming belongs
to the later handshake worker. This is a callback contract, not a whole episode. -/
theorem original_retransmit_counter (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) (fun w => w.peerAt pid = some p)
      (fun _ w => ∃ q, w.peerAt pid = some q ∧ q.internalId = p.internalId ∧
        q.timerHandshakeAttempts =
          (if p.timerHandshakeAttempts > 18 then p.timerHandshakeAttempts else p.timerHandshakeAttempts + 1) ∧
        q.timerRetransmitHandshake = p.timerRetransmitHandshake) :=
  source_retransmit_counter pid p

/-- With arm-record mode enabled, a normally completed guarded arm uses
the original callerJiffies operation at the supplied site. When the guard passes, expiry equals
that read plus delay; the arm's own read is zero or one signed tick later. -/
theorem original_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observed (modPeerTimer site pid timer delay) (callerJiffies site))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧ result.2 = (d.running && !p.isDead) ∧
        if result.2 then
          final.peerAt pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
          clockGap final caller
        else final.peerAt pid = some p) :=
  projected_guarded_arm_recorded site pid timer delay d p resident

/-- With arm-record mode enabled, the original session-derived hook on a
running live peer arms zero-key material at its original caller-read result
plus REJECT_AFTER_TIME * 3 * HZ ticks.
This exact site and delay contract covers one hook invocation. -/
theorem original_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersSessionDerived pid)
      (callerJiffies .timerJiffiesSessionDerived))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧
        final.peerAt pid = some (p.setTimer .zeroKeyMaterial
          (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧ clockGap final caller) :=
  projected_session_derived_recorded pid d p resident running alive

/-- With arm-record mode enabled, original handshake-initiated arming
uses its caller-read result plus REKEY_TIMEOUT * HZ and a jitter below HZ/3.
The caller read precedes the original jitter computation, and both executions
are witnessed; supplied records and permitted placeholders are both covered. -/
theorem original_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersHandshakeInitiated pid)
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead jitter afterJitter,
        result.1 = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        final.peerAt pid = some (p.setTimer .retransmitHandshake
          (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧ clockGap final caller) :=
  projected_handshake_initiated_recorded pid d p resident running alive

/-- With arm-record mode enabled and no pending new-handshake timer,
original data-sent arming on a running live peer uses its caller-read result
plus keepalive and rekey delays and bounded jitter, in original read order. -/
theorem original_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersDataSent pid)
      (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead jitter afterJitter,
        result.1 = .ok ((true, beforeRead, some caller, afterRead, jitter), afterJitter) ∧
        jitter < HZ / 3 ∧ final.peerAt pid = some (p.setTimer .newHandshake
          (some (caller + (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
        clockGap final caller) :=
  projected_data_sent_recorded pid d p resident absent running alive

/-- With arm-record mode enabled, original traversal on a running live peer
with nonzero interval sets persistent keepalive to its caller-read result plus
interval * HZ, even if that timer was already pending. -/
theorem original_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok (((p.persistentKeepaliveInterval, true), beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some (p.setTimer .persistentKeepalive
          (some (caller + (p.persistentKeepaliveInterval * HZ).toUInt64))) ∧ clockGap final caller) :=
  projected_traversal_recorded pid d p resident enabled running alive

/-- With arm-record mode enabled, original data receipt on a running live peer
with no send-keepalive timer arms that timer at its caller-read result plus
KEEPALIVE_TIMEOUT * HZ ticks, after the original running and pending tests. -/
theorem original_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersDataReceived pid)
      (prefixClockPath (dataReceivedPrefix pid) .timerJiffiesDataReceived))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok ((some true, beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some (p.setTimer .sendKeepalive
          (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧ clockGap final caller) :=
  projected_data_received_recorded pid d p resident absent running alive

/-- After the original keepalive send completes, a running live peer needing
another keepalive clears that flag and rearms at its caller-read result plus
KEEPALIVE_TIMEOUT * HZ. Residency and flag premises concern the actual post-send
state, not callback entry; arm-record mode is enabled there. -/
theorem original_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (needed : p.timerNeedAnotherKeepalive = true)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (expiredSendKeepalive pid)
      (prefixInspect (sendKeepalive pid)
        (prefixClockPath (keepaliveRearmPrefix pid) .timerJiffiesExpiredKeepalive)))
      (fun _ => True)
      (fun result final => ∀ choice afterSend tail,
        result.1 = .ok ((choice, afterSend, tail), afterSend) →
        afterSend.wg.device = some d → afterSend.wg.armRecords = true →
        ∃ beforeRead caller afterRead,
          tail = .ok ((true, beforeRead, some caller), afterRead) ∧
          final.peerAt pid = some (({ p with timerNeedAnotherKeepalive := false } : Peer).setTimer
            .sendKeepalive (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧ clockGap final caller) :=
  projected_expired_keepalive_recorded pid d p resident needed running alive

/-- With arm-record mode enabled, original retransmit give-up above the attempt
limit deletes send-keepalive, purges staged packets and arms an absent zero-key
timer on a running live peer. Expiry is the original site read plus
REJECT_AFTER_TIME * 3 * HZ; both original decision prefixes are witnessed. -/
theorem original_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (expiredRetransmitHandshake pid) (giveUpClockPath pid))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ afterDecision beforeRead caller afterRead,
        result.1 = .ok ((true, afterDecision, true, beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some ((giveUpPeer p).setTimer .zeroKeyMaterial
          (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧ clockGap final caller) :=
  projected_retransmit_giveup_recorded pid d p resident limit absent running alive

/-- Every normally completed original timer dispatch selects a resident peer's
pending timer of the worker's kind whose expiry precedes the supplied horizon
under the mirror's time comparison. The actual selection and detached section
suffix execute in sequence. Selection may consume ambient records; it preserves
the device. No firing-order or wall-clock theorem is claimed. -/
theorem original_timer_dispatch_due (worker : Worker) (jHi : UInt64) (d : Device) :
    Campaign2.Ensures (observed (Env.fireTimer worker jHi) (timerExecutionPath worker jHi))
      (fun s => s.wg.device = some d)
      (fun result final => ∃ pid timer selected,
        result.1 = .ok ((pid, timer, selected), final) ∧
        worker.timer? = some timer ∧ selected.wg.device = some d ∧
        pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
          p.timer timer = some expiry ∧ timeBefore expiry jHi = true) :=
  projected_timer_dispatch_due worker jHi d

/-- When original selection chooses this peer's retransmit timer, a normally
completed original dispatch preserves its allocation identity, increments the
attempt counter at or below the limit, and retains it above the limit. The
retransmit timer is detached and remains detached through this callback; later
worker rearming is outside this call. Selection is an actual prefix run, not an
assumed callback outcome. This is not a universal retry-episode theorem. -/
theorem original_retransmit_dispatch (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Campaign2.Ensures (observed (Env.fireTimer .timerRetransmit jHi)
      (timerSelection .timerRetransmit jHi))
      (fun s => retryObservation s pid = some (identity, attempts, timer))
      (fun result final => ∀ selected,
        result.1 = .ok ((pid, .retransmitHandshake), selected) →
        retryObservation final pid = some (identity, nextAttempts attempts, none)) :=
  projected_retransmit_dispatch pid jHi identity attempts timer

/-- Every normal original handshake send either exits in its actual prefix
or executes the final retransmit arm hook. Reaching the hook means creation
succeeded, not that the ignored socket-send result was successful. The prefix
retains rate-limit and creation decisions and every intervening operation. -/
theorem original_initiation_arm_path (pid : PeerId) :
    Campaign2.Ensures (observed (sendHandshakeInitiation pid) (initiationExecutionPath pid))
      (fun _ => True)
      (fun result final => ∃ reached beforeArm,
        result.1 = .ok ((reached, beforeArm), final) ∧
        (reached = false → final = beforeArm)) :=
  projected_initiation_arm_path pid

/-- When the original initiation-send prefix reaches the hook with a live peer
on a running device, a normal arm-record-mode completion stores the original
caller-read result plus rekey delay and bounded jitter. Premises concern the actual
post-prefix state; this does not frame the send from function entry, establish
a full retry episode or prove a successful network transmission. -/
theorem original_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (sendHandshakeInitiation pid)
      (prefixInspect (initiationArmPrefix pid)
        (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter)))
      (fun _ => True)
      (fun result final => ∀ reached afterPrefix tail,
        result.1 = .ok ((reached, afterPrefix, tail), afterPrefix) → reached = true →
        afterPrefix.wg.device = some d → afterPrefix.wg.armRecords = true →
        ∃ caller afterRead jitter afterJitter,
          tail = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
          final.peerAt pid = some (p.setTimer .retransmitHandshake
            (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧ clockGap final caller) :=
  projected_initiation_send_arm pid d p resident running alive

/-- At either original timer-jitter site, a finite contiguous rejected-draw
prefix followed by an accepted byte returns that byte's scaled jitter, consumes
exactly those records and preserves the entire remaining projected state. Records use the
original one-byte payload with seven padding zeros; arbitrary suffixes remain.
This is total execution of the original sampler, not a distribution claim. -/
theorem original_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) :
    Campaign2.Observes (jitterBelowRekeyTimeout site.hiddenSite)
      (fun s => s.ambient.hidden = some (jitterStream site rejected accepted rest))
      (fun initial out => out = .ok (jitterValue accepted, withRecords initial rest)) :=
  projected_jitter_records site rejected accepted rest bad good

/-- A finite contiguous stream containing only rejected jitter bytes ends at
the exact original missing-record error. The record-derived budget includes the
extra read, so this is hidden-input exhaustion before budget exhaustion. Empty
streams are included; recordless placeholder execution and ambient interleavings
are outside this contract. -/
theorem original_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte) :
    Campaign2.Observes (jitterBelowRekeyTimeout site.hiddenSite)
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
      (fun _ w => initiationObservation w pid = some (identity, attempts, refs, expiry)) :=
  source_initiation_prefix_frame pid identity attempts refs expiry

/-- Original initiation sending preserves peer identity, retry attempts and
references whenever it returns normally. Its final hook may change the
retransmit expiry. A normal return does not assert transmission success. -/
theorem original_handshake_send_frame (pid : PeerId) (identity attempts refs : Nat) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun w => workerObservation w pid = some (identity, attempts, refs))
      (fun _ w => workerObservation w pid = some (identity, attempts, refs)) :=
  source_handshake_send_frame pid identity attempts refs

/-- A normally returning original handshake-send worker preserves identity and
retry attempts and releases one reference. More than one entry reference keeps
the peer resident after that release. This is the worker body, before composition
with the environment's selection/dequeue and a complete retry episode. -/
theorem original_send_worker_frame (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Campaign2.Ensures (handshakeSendWorker pid)
      (fun w => workerObservation w pid = some (identity, attempts, refs))
      (fun _ w => workerObservation w pid = some (identity, attempts, refs - 1)) :=
  source_send_worker_frame pid identity attempts refs retained

/-- A normally completed original environment send dispatch selects the queue
head or the first matching named association, erases one queue occurrence, and
requires then clears the selected peer's pending flag before its section starts.
The observations retain the actual ordered section reads and worker execution.
The retained peer keeps its identity and attempt count and loses one reference.
No final queue or pending-flag frame, or successful transmission, is asserted. -/
theorem original_send_dispatch_path (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Ensures (observed Env.runOneSendWorker sendWorkerExecution)
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun result final => ∃ execution, result.1 = .ok (execution, final) ∧
        CompletedSendWorker d units execution final) :=
  source_send_dispatch_path d units retained

/-- A successful original environment dispatch releases one reference from an
originally queued, pending peer, preserving that allocation's identity and retry
attempts. The entry reference assumption ensures the selected peer remains resident.
This normal-return preservation contract does not promise successful completion. -/
theorem original_send_dispatch (d : Device) (retained : RetainedSendQueue d) :
    Campaign2.Ensures Env.runOneSendWorker (fun s => s.wg.device = some d)
      (fun _ final => ∃ pid p, pid ∈ d.sendWorkQueue ∧ d.peers[pid]? = some p ∧
        p.handshakePending = true ∧ workerObservation final pid =
          some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1)) :=
  source_send_dispatch d retained

/-- A normally completed original retransmit-timer dispatch followed immediately
by one original send-worker dispatch, starting with no queued send work, exposes
the actual selected due peer and post-timer state. Successful worker selection
forces fresh retry queueing: the entry peer was alive, not pending, had a positive
reference count and was at or below the retry limit. Queueing acquires one
reference and the callback increments attempts once. The worker releases the
reference, preserving identity and the incremented attempt count, leaves the send
queue empty and the selected pending flag false. The observations
record the original timer selection/result and ordered worker section observations.
Erasure to the original pair is exact, including errors, by
observedRetryDispatch_erase. Scheduler coverage, rearming, successful transmission and a complete retry episode remain open. -/
theorem original_retry_dispatch (d : Device) (horizon : UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetryDispatch horizon)
      (fun s => s.wg.device = some d)
      (RetryDispatchCertificate d horizon) :=
  source_retry_dispatch d horizon empty

/-- A normal original timer/send pair retains the retry certificate, including
final empty queue, cleared pending flag and acquired/released reference, and
exposes its actual initiation prefix and pre-release state. If that prefix
reaches the arm hook with a running device, live selected peer and arm-record
mode, the original caller read plus rekey delay and bounded jitter determines
the exact wrapped retransmit expiry. That expiry survives retained release and
section stop; the clock-gap fact stays at the actual pre-release snapshot.
These are conditions at beforeArm, not added assumptions at retry entry.
Exact projection/erasure retain original errors. Reaching the hook and successful
network transmission are not guaranteed, and a full retry episode remains open. -/
theorem original_retry_rearm (d : Device) (horizon : UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetryRearm horizon)
      (fun s => s.wg.device = some d) (RetryRearmCertificate d horizon) :=
  source_retry_rearm d horizon empty

/-- A normal sequence of consecutive original timer/send pairs has adjacent actual
snapshots and retains every pair's conditional rearm certificate. The send queue
ends empty. If every actual timer selection names one initial resident peer, its
identity/reference count are preserved and attempts increase by the sequence
length; a nonempty sequence also clears pending and bounds initial attempts plus
length by 19. An empty sequence preserves the entire snapshot, with no attempt or
pending restriction. observedRetrySequence_erase preserves original errors exactly.
This is a sequence of the original calls, not an environment scheduler theorem or
a promise that any positive number of retries completes. -/
theorem original_retry_sequence (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d) (RetrySequenceCertificate d horizons) :=
  source_retry_sequence d horizons empty

/-- Starting at zero attempts, at most 19 consecutive pairs can return normally
with this same actual selected peer. In particular 20 such successful pairs are
excluded; this does not say that the twentieth timer callback itself fails. -/
theorem original_retry_sequence_zero_bound (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d)
      (fun result _ => SameRetryPeer pid result.2 → horizons.length ≤ 19) :=
  source_retry_sequence_zero_bound d horizons empty pid p resident zero

/-- For response-kind packets, the exact original caller and its decorated
execution factor through the actual session-derived hook. Normal full return
reports whether the session stage was reached. A present session cut records
the entry, returned Bool and before/after-hook observations, and derives H1's
ordered SessionEffect. The hook is present exactly when that session returned
true; this successful case derives a counter increment and live resident peer.
At a reached hook, running-device and arm-record conditions at that actual cut
give caller-jiffies plus wrapped zero-key delay and clockGap immediately after
the hook. Caller reads may use permitted placeholders. No successful caller,
final expiry preservation, failed-call prefix retention or global once-per-session
arm count is asserted. Erasure retains every original error. -/
theorem original_response_session_arm (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.AgreesOn (fun _ => True) (receiveHandshakePacket msg src)
      (responseSessionCallPrefix msg src >>= responseSessionCallSuffix msg) ∧
    Campaign2.AgreesOn (fun _ => True) (observedResponseSession msg src)
      (responseSessionTranscript msg src) ∧
    Campaign2.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation) := by
  constructor
  · intro entry pre
    rw [responseSessionCall_source msg src kind]
  · constructor
    · intro entry pre
      rw [observedResponseSession_source msg src kind]
    · exact observedResponseSession_facts msg src kind

/-- The original outgoing response sender and its decorated execution factor
through the actual session-derived hook. On normal full return, response creation
may have rejected the call without reaching the session stage. A present cut
records the actual session result and ordered SessionEffect; its hook observation
is present exactly when beginSession returned true. That case derives the counter
increment and a live resident peer. Running-device and arm-record conditions at
the actual before-hook cut give the caller-jiffies read, exact wrapped zero-key
expiry and clockGap at the after-hook cut. The remaining original timer hooks,
second clock/write and socket send execute unchanged. No successful completion,
transmission, final expiry preservation, failed-call prefix retention or global
once-per-session count is asserted. Erasure preserves every original error. -/
theorem original_outgoing_response_session_arm (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (sendHandshakeResponse pid)
      (outgoingResponseSessionPrefix pid >>= outgoingResponseSessionSuffix pid) ∧
    Campaign2.AgreesOn (fun _ => True) (observedOutgoingResponseSession pid)
      (outgoingResponseSessionTranscript pid) ∧
    Campaign2.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation) := by
  constructor
  · intro entry pre
    rw [outgoingResponseSession_source pid]
  · constructor
    · intro entry pre
      rw [observedOutgoingResponseSession_source pid]
    · exact observedOutgoingResponseSession_facts pid

/-- The original data-completion caller invokes traversal once before the whole
supplied list, including an empty list. Its ordered observations retain each
actual packet read and send Boolean. The data-sent hook is reached exactly when
some actual send returned true for a packet whose length is not the keepalive
length. Each hook's own running/live/recorded-mode guards (and interval or pending
guard) give its caller-clock observation and exact wrapped expiry; data-sent also
records bounded jitter. These expiry and clock-gap facts hold at each hook's
after-state. The authenticated-sent hook, loop markers and keepKeyFresh suffix
remain original. Erasure preserves all errors; the certificate describes normal
full returns and promises neither transmission nor final expiry preservation. -/
theorem original_data_done_timers (pid : PeerId) (items : List SkbId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observedDataDone pid items; pure ()) (createDataDone pid items) ∧
    Campaign2.Ensures (observedDataDone pid items) (fun _ => True)
      (fun observation _ => DataDoneFacts pid items observation) := by
  constructor
  · intro entry pre
    rw [observedDataDone_erase pid items]
  · exact observedDataDone_facts pid items

/-- The original consumeDataDone caller invokes traversal before its keepalive
test and invokes data-received exactly for nonzero packet length. Its endpoint
write, confirmation/handshake-complete path, staged sends, freshness check and
authenticated-received deletion remain original, as do the zero-byte statistics
return and complete inner-packet validation/routing suffix. On normal full
return each captured hook has its own guarded timer effect: traversal's enabled
live/running recorded arm has the exact persistent expiry; data receipt while
running requests another keepalive when one is pending, and an absent timer on
a live peer has its recorded caller-plus-delay expiry. The expiry and clock-gap
facts refer to each hook's after-state. Erasure preserves the original returned
packet option and every error. This raw-packet contract establishes neither
authentication nor delivery, final expiry preservation or failed-call cut retention. -/
theorem original_consume_data_done_timers (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.AgreesOn (fun _ => True)
      (do let result ← observedRxDataTimers pid pkt e; pure result.2)
      (consumeDataDone pid pkt e) ∧
    Campaign2.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1) := by
  constructor
  · intro entry pre
    rw [observedRxDataTimers_erase pid pkt e]
  · exact observedRxDataTimers_facts pid pkt e

/-- The original outgoing response sender reaches traversal exactly when its
actual creation/session prefix returns a present successful session. The cut
retains the original session effect and zero-key hook facts, and traversal starts
at that prefix's end. Its enabled/live/running/recorded guards give the exact
caller-plus-interval persistent expiry and clock gap at the hook's after-state.
The authenticated-sent deletion, later clock/write and socket send remain in
the original continuation. Erasure preserves every error; normal certificates
do not promise transmission, final expiry preservation or failed-call retention. -/
theorem original_outgoing_response_traversal (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observedResponseTraversal pid; pure ()) (sendHandshakeResponse pid) ∧
    Campaign2.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  constructor
  · intro entry pre
    rw [observedResponseTraversal_erase pid]
  · exact observedResponseTraversal_facts pid

/-- The original initiation sender invokes traversal exactly when its original
rate-check/creation/MAC prefix yields a message. Early exits yield no hook. On
normal full return, the actual hook's enabled/live/running/recorded guards give
the exact persistent expiry and clock gap at its after-state. Authenticated-sent
deletion, the second clock/write, socket send and final retransmit hook remain
unchanged. Erasure includes errors; no transmission, final expiry or retained
failed-call certificate is asserted. -/
theorem original_outgoing_initiation_traversal (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (initiationTraversalPrelude pid >>= initiationTraversalSuffix pid)
      (sendHandshakeInitiation pid) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationTraversal pid; pure ()) (sendHandshakeInitiation pid) ∧
    Campaign2.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut) := by
  constructor
  · intro entry pre
    rw [initiationTraversal_source pid]
  · constructor
    · intro entry pre
      rw [observedInitiationTraversal_erase pid]
    · exact observedInitiationTraversal_facts pid

/-- For an initiation message, the original receive caller's common traversal
hook carries the actual accepted consumer/MAC certificate and its selected peer.
The endpoint setter, response sender, statistics, authenticated-received deletion
and final release remain original. A normal present cut gives guarded recorded
persistent expiry at the traversal hook; rejected paths may return no cut. Exact
erasure retains errors. No final expiry or failed-call retention is claimed. -/
theorem original_initiation_receive_traversal (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observedInitiationReceiveTraversal msg src; pure ()) (receiveHandshakePacket msg src) ∧
    Campaign2.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut) := by
  constructor
  · intro entry pre
    rw [observedInitiationReceiveTraversal_erase msg src kind]
  · exact observedInitiationReceiveTraversal_facts msg src

/-- For a response message, the common receive traversal follows the actual
accepted consumer/MAC certificate, endpoint setter and original session/keepalive
branch. A normal present cut gives the selected peer's guarded recorded persistent
expiry at the hook. Statistics, authenticated-received deletion and final release
remain original; exact erasure retains all errors. Hook facts neither require a
successful new session nor assert final expiry or failed-call retention. -/
theorem original_response_receive_traversal (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observedResponseReceiveTraversal msg src; pure ()) (receiveHandshakePacket msg src) ∧
    Campaign2.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut) := by
  constructor
  · intro entry pre
    rw [observedResponseReceiveTraversal_erase msg src kind]
  · exact observedResponseReceiveTraversal_facts msg src

/-- After 19 consecutive normal retry/send pairs from zero, if all selected the
same peer, an immediately invoked retransmit callback takes the give-up branch.
The comparison log and entire tail are retained, including errors. A normal
callback return preserves attempt count 19 and the empty send queue. This does
not assert another timer is armed, selected, or invoked, or that give-up returns;
there is no intervening scheduler/environment action in this boundary contract. -/
theorem original_retry_boundary (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) (nineteen : horizons.length = 19)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d)
      (fun result boundary => SameRetryPeer pid result.2 →
        Campaign2.AgreesOn (fun s => s = boundary)
          (expiredRetransmitHandshake pid)
          (do let _ ← retransmitDecision pid; retransmitGiveUp pid) ∧
        Campaign2.Ensures (expiredRetransmitHandshake pid) (fun s => s = boundary)
          (fun _ final => final.wg.device.map Device.sendWorkQueue = some [] ∧
            ∃ q, final.peerAt pid = some q ∧ q.internalId = p.internalId ∧
              q.timerHandshakeAttempts = 19)) :=
  source_retry_boundary d horizons empty nineteen pid p resident zero

/-- Above the retry limit, an already-pending zero-key timer makes the original
callback return without any clock or arm-record read. It deletes send-keepalive,
purges staged packets and accounts their original length in txDropped, retaining
the existing zero-key expiry. Exactly two original decisions are appended, with
the give-up comparison operands and the entry section stamp. Every other
projected field is unchanged, including hidden records, clocks, attempts and
work queues. No running/live/record-mode premise is needed. This is one callback,
not a whole scheduler episode or a once-per-session count. -/
theorem original_giveup_pending_zero_key (pid : PeerId) (d : Device) (p : Peer)
    (expiry : UInt64) (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (pending : p.timerZeroKeyMaterial = some expiry) (entry : Campaign2.Snapshot) :
    Campaign2.Returns (expiredRetransmitHandshake pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => final = pendingGiveUpView entry d pid p) :=
  pendingGiveUp_returns pid d p expiry resident limit pending entry

/-- Above the retry limit, a running live peer with zero-key absent returns
from the original give-up callback when its two contiguous supplied records
have the original sizes, caller-derived expiry and signed zero-or-one-tick gap.
The complete projected effect deletes send-keepalive, purges staged packets and
accounts their length, arms zero-key, consumes exactly these two records, stores
the arm clock and applies the original zero/nonzero timer-address registration.
Four original decisions are appended; all other projected fields are unchanged.
The suffix is arbitrary, and successful execution is a conclusion, not a premise.
This is one callback; no session provenance or scheduler episode is asserted. -/
theorem original_giveup_absent_zero_key (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : Campaign2.Snapshot) :
    Campaign2.Returns (expiredRetransmitHandshake pid)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (fun _ final => final = absentGiveUpView entry d pid p input rest) :=
  absentGiveUp_returns pid d p input rest resident limit absent running alive valid entry

/-- The original retransmit hook completes from valid supplied caller, jitter
and arm records. Running/live peers receive the exact wrapped expiry and timer
registration; otherwise the guard skips the arm after consuming the caller and
jitter reads, preserving the arm record. This is a hook contract, not a complete
send-worker or scheduler episode. -/
theorem original_retransmit_hook_ready (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (valid : input.Valid) (entry : Snapshot) :
    Campaign2.Returns (timersHandshakeInitiated pid)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (fun _ final => final = if d.running && !p.isDead
        then retransmitReadyView entry d pid p input rest
        else retransmitSkippedView entry d input rest) :=
  retransmitHook_returns pid d p input rest resident valid entry

/-- The full original initiation-send call completes from static creation and
tail readiness with supplied rate-test, first last-sent, ephemeral, timestamp,
index, second last-sent and retransmit records. It returns the exact ordered
Device effect, consumes that prefix, preserves recorded mode and observes the
final arm clock. Readiness for the send tail names the pure creation result.
This covers a live peer on a running device with no endpoint, invalid cookie,
zero keepalive interval and unarmed send-buffer allocation: the original ignores
the failed no-endpoint send and still rearms. No successful-run premise, packet
delivery, reachable-state invariant or arbitrary callback history is asserted. -/
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
    Campaign2.Returns (sendHandshakeInitiation pid)
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧ s.ambient.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
        {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
        Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)))
      (fun _ s =>
        let made := SendReady.sendCreationResult pid d p last ephemeral clock fresh.value
        s.wg.device = some {SendReady.initiationTailDevice made.2 pid createdPeer made.1 tailClock with
          peers := (SendReady.initiationTailDevice made.2 pid createdPeer made.1 tailClock).peers.insert pid
            ((SendReady.initiationTailPeer createdPeer made.1 tailClock).setTimer .retransmitHandshake
              (some (input.caller + input.delay.toUInt64)))} ∧
        s.ambient.hidden = some rest ∧ s.wg.armRecords = true ∧ s.wg.jiffiesLast = some input.now) :=
  SendReady.sendInitiation_projected pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity
    word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive tailLen input valid

/-- The original timer dispatcher selects a named due retransmit timer, detaches
it, consumes its section records and runs the ready callback. Static readiness
and explicit records suffice for success: no callback-success premise is used.
The exact projection includes the attempt increment, endpoint/cache reset,
acquired reference and queued send work, fired symbol, section-start pending-work
filter, decisions and unused record suffix. This does not claim send completion
or rearming by the later worker. -/
theorem original_fire_retry_ready (d : Device) (p : Peer) (pid : PeerId) (horizon : UInt64)
    (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (startLen : start.length=16) (stopLen : stop.length=8)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (nonzero : recordWordOf start 1 ≠ 0)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead=false) (pending : p.handshakePending=false)
    (positive : 0<p.refcount) (bounded : p.refcount+1<2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64*NSEC_PER_SEC64 ≤ (RetryReady.word clock).toInt64) :
    Campaign2.Observes (Env.fireTimer .timerRetransmit horizon)
      (fun s => s.wg.device=some d ∧
        s.ambient.hidden=some (FireReady.suppliedRecords start cache clock queue stop suffix) ∧
        s.wg.armRecords=true ∧ s.wg.dstCacheRecords=true ∧
        s.wg.timerUnits.find? (·.1 == recordWordOf start 1) =
          some (recordWordOf start 1,pid,.retransmitHandshake) ∧
        s.ambient.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
          some (recordWordOf queue 0,Worker.sendWorker.index,pid))
      (fun entry outcome => outcome=.ok ((),FireReady.fireView entry d p pid cache clock suffix)) :=
  FireReady.fire_outcome d p pid horizon start cache clock queue stop suffix resident due
    startLen stopLen cacheLen clockLen queueLen nonzero limit alive pending positive bounded expired

/-- One original named send-worker dispatch completes from a queued resident
peer with its pending flag set and a matching nonzero recorded unit. It performs
the actual selection, dequeue, pending clear, section start, initiation/send/rearm,
retained reference decrement and section stop, with exact Device, record suffix,
mode and final clock. Readiness names the pure creation result after dequeue;
the tail has no endpoint, an invalid cookie, zero keepalive interval and an
unarmed send allocation. The original still rearms after that failed send.
This is one complete dispatch, not an arbitrary history or packet-delivery claim. -/
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
    Campaign2.Returns Env.runOneSendWorker
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧
        s.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
          some (unit, Worker.sendWorker.index, pid) ∧
        s.ambient.hidden = some (WorkerReady.records start rate last ephemeral clock tailClock stop collisions fresh input rest))
      (fun _ s => s.wg.device = some (WorkerReady.result pid d p createdPeer last ephemeral clock tailClock fresh.value input) ∧
        s.ambient.hidden = some rest ∧ s.wg.armRecords = true ∧ s.wg.jiffiesLast = some input.now) :=
  WorkerReady.runOneSendWorker_projected pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity word
    nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive retained tailLen input valid
    headPid unit head queued pending start stop startLen stopLen address nonnullUnit

end Leanux.Proofs.WG.TimerDiscipline
