import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.ObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmClaims
import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceClaims
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

end Leanux.Proofs.WG.TimerDiscipline
