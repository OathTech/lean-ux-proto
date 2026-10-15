import Leanux.Proofs.WG.TimerDiscipline.SourceFrames
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.JitterExhaustionSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.RetrySource
import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- A successful recorded arm stores exactly caller jiffies plus delay, with unsigned wrapping; the signed gap to the arm read is zero or one tick. -/
theorem source_recorded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) :
    Ensures (armTimer pid timer delay (some caller))
      (fun w => w.armRecords = true ∧ peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, w.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1) :=
  armTimer_recorded pid timer delay caller p

/-- Deleting a timer changes exactly that timer field to absent. -/
theorem source_delete (pid : PeerId) (timer : PeerTimer) (p : Peer) :
    Ensures (delTimer pid timer) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer timer none)) :=
  delTimer_exact pid timer p

/-- The arm guard returns running and not dead and leaves the device unchanged. -/
theorem source_arm_guard (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimerGuard pid) (fun w => w.k.wg = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧ w.k.wg = some d) :=
  modPeerTimerGuard_exact pid d p resident

/-- A normal guarded arm changes only the selected peer timer when running and alive; otherwise it preserves the peer. -/
theorem source_guarded_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimer site pid timer delay) (fun w => w.k.wg = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧
        if ok then ∃ expiry, peerAt w pid = some (p.setTimer timer (some expiry))
        else peerAt w pid = some p) :=
  modPeerTimer_effect site pid timer delay d p resident

/-- With a nonzero interval and running/live guard, normal traversal has the peer-state effect of setting persistent keepalive to some expiry; otherwise it preserves the peer. -/
theorem source_traversal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersTraversal pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false
        then ∃ expiry, peerAt w pid = some (p.setTimer .persistentKeepalive (some expiry))
        else peerAt w pid = some p) :=
  timersTraversal_effect pid d p resident

/-- On normal completion the session-derived hook sets only the zero-key timer to some expiry when running and alive, and otherwise preserves the peer. -/
theorem source_session_derived (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersSessionDerived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running && !p.isDead
        then ∃ expiry, peerAt w pid = some (p.setTimer .zeroKeyMaterial (some expiry))
        else peerAt w pid = some p) :=
  timersSessionDerived_effect pid d p resident

/-- Data receipt while running arms an absent keepalive timer on a live peer, or requests another keepalive when the timer is already pending. -/
theorem source_data_received (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersDataReceived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running then
        if p.timerPending .sendKeepalive then
          peerAt w pid = some { p with timerNeedAnotherKeepalive := true }
        else if p.isDead then peerAt w pid = some p
        else ∃ expiry, peerAt w pid = some (p.setTimer .sendKeepalive (some expiry))
        else peerAt w pid = some p) :=
  timersDataReceived_effect pid d p resident

/-- Handshake completion deletes the retransmit timer, resets attempts and the last-minute flag, and records the wall-clock bytes; other peer fields are preserved. -/
theorem source_handshake_complete (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Ensures (timersHandshakeComplete pid site) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ now, peerAt w pid = some
        { (p.setTimer .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false, walltimeLastHandshake := now }) :=
  timersHandshakeComplete_effect pid site p


/-- The authenticated-send hook deletes only the send-keepalive timer. -/
theorem source_authenticated_sent (pid : PeerId) (p : Peer) :
    Ensures (timersAnyAuthenticatedPacketSent pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer .sendKeepalive none)) :=
  delTimer_exact pid .sendKeepalive p

/-- The authenticated-receive hook deletes only the new-handshake timer. -/
theorem source_authenticated_received (pid : PeerId) (p : Peer) :
    Ensures (timersAnyAuthenticatedPacketReceived pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer .newHandshake none)) :=
  delTimer_exact pid .newHandshake p

/-- The original retransmit callback increments attempts through 18 to 19,
then leaves the count unchanged on give-up. Every normal completion preserves
the peer's allocation identity and retransmit-timer field; rearming belongs
to the later handshake worker. This is a callback contract, not a whole episode. -/
theorem source_retransmit_counter (pid : PeerId) (p : Peer) :
    Ensures (expiredRetransmitHandshake pid) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ q, peerAt w pid = some q ∧ q.internalId = p.internalId ∧
        q.timerHandshakeAttempts =
          (if p.timerHandshakeAttempts > 18 then p.timerHandshakeAttempts else p.timerHandshakeAttempts + 1) ∧
        q.timerRetransmitHandshake = p.timerRetransmitHandshake) := by
  intro w result final pre run
  have effect := expiredRetransmit_retryView pid p.internalId p.timerHandshakeAttempts
    p.timerRetransmitHandshake w result final (by simp [retryAt, retryView, pre]) run
  cases resident : peerAt final pid with
  | none => simp [retryAt, resident] at effect
  | some q =>
    refine ⟨q, rfl, ?_⟩
    simpa [retryAt, retryView, resident, nextAttempts, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT] using effect

/-- With arm-record mode enabled, a normally completed guarded arm uses
the original callerJiffies operation at the supplied site. When the guard passes, expiry equals
that read plus delay; the arm's own read is zero or one signed tick later. -/
theorem source_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (initial final : World) (result : Bool) (device : initial.k.wg = some d)
    (records : initial.armRecords = true)
    (run : (modPeerTimer site pid timer delay).run initial = .ok (result, final)) :
    ∃ caller afterRead,
      (callerJiffies site).run initial = .ok (some caller, afterRead) ∧
      result = (d.running && !p.isDead) ∧
      if result then
        peerAt final pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, final.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1
      else peerAt final pid = some p :=
  modPeerTimer_recorded_clock site pid timer delay d p resident initial final result device records run

/-- With arm-record mode enabled, the original session-derived hook on a
running live peer arms zero-key material at its original caller-read result
plus REJECT_AFTER_TIME * 3 * HZ ticks.
This exact site and delay contract covers one hook invocation. -/
theorem source_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersSessionDerived pid).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (callerJiffies .timerJiffiesSessionDerived).run initial = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer .zeroKeyMaterial
        (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  sessionDerived_recorded_clock pid d p resident running alive initial final device records run

/-- With arm-record mode enabled, original handshake-initiated arming
uses its caller-read result plus REKEY_TIMEOUT * HZ and a jitter below HZ/3.
The caller read precedes the original jitter computation, and both executions
are witnessed; supplied records and permitted placeholders are both covered. -/
theorem source_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersHandshakeInitiated pid).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (callerJiffies .timerJiffiesHandshakeInitiated).run initial = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout .retransmitJitter).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer .retransmitHandshake
        (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  rw [handshakeInitiated_source] at run
  exact jitteredArm_recorded_clock .timerJiffiesHandshakeInitiated .retransmitJitter
    pid .retransmitHandshake REKEY_TIMEOUT_TICKS d p resident running alive
    initial final device records run

/-- With arm-record mode enabled and no pending new-handshake timer,
original data-sent arming on a running live peer uses its caller-read result
plus keepalive and rekey delays and bounded jitter, in original read order. -/
theorem source_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersDataSent pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead jitter afterJitter,
      (dataSentPrefix pid).run initial = .ok (true, beforeRead) ∧
      (callerJiffies .timerJiffiesDataSent).run beforeRead = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout .newHandshakeJitter).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer .newHandshake
        (some (caller + (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  dataSent_recorded_clock pid d p resident absent running alive initial final device records run

/-- With arm-record mode enabled, original traversal on a running live peer
with nonzero interval sets persistent keepalive to its caller-read result plus
interval * HZ, even if that timer was already pending. -/
theorem source_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersTraversal pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (traversalPrefix pid).run initial = .ok ((p.persistentKeepaliveInterval, true), beforeRead) ∧
      (callerJiffies .timerJiffiesTraversal).run beforeRead = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer .persistentKeepalive
        (some (caller + (p.persistentKeepaliveInterval * HZ).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  traversal_recorded_clock pid d p resident enabled running alive initial final device records run

/-- With arm-record mode enabled, original data receipt on a running live peer
with no send-keepalive timer arms that timer at its caller-read result plus
KEEPALIVE_TIMEOUT * HZ ticks, after the original running and pending tests. -/
theorem source_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
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
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  dataReceived_recorded_clock pid d p resident absent running alive initial final device records run

/-- After the original keepalive send completes, a running live peer needing
another keepalive clears that flag and rearms at its caller-read result plus
KEEPALIVE_TIMEOUT * HZ. Residency and flag premises concern the actual post-send
state, not callback entry; arm-record mode is enabled there. -/
theorem source_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
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
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  expiredKeepalive_recorded_clock pid d p resident needed running alive initial afterSend final send device records run

/-- With arm-record mode enabled, original retransmit give-up above the attempt
limit deletes send-keepalive, purges staged packets and arms an absent zero-key
timer on a running live peer. Expiry is the original site read plus
REJECT_AFTER_TIME * 3 * HZ; both original decision prefixes are witnessed. -/
theorem source_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
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
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  retransmitGiveUp_recorded_clock pid d p resident limit absent running alive initial final device records run

/-- Every normally completed original timer dispatch selects a resident peer's
pending timer of the worker's kind whose expiry precedes the supplied horizon
under the mirror's time comparison. The actual selection and detached section
suffix execute in sequence. Selection may consume ambient records; it preserves
the kernel state. No firing-order or wall-clock theorem is claimed. -/
theorem source_timer_dispatch_due (worker : Worker) (jHi : UInt64) (initial final : World) (d : Device)
    (device : initial.k.wg = some d) (run : (Env.fireTimer worker jHi).run initial = .ok ((), final)) :
    ∃ pid timer selected,
      (timerSelection worker jHi).run initial = .ok ((pid, timer), selected) ∧
      (fireSelected worker pid timer).run selected = .ok ((), final) ∧
      worker.timer? = some timer ∧ selected.k.wg = some d ∧
      pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
        p.timer timer = some expiry ∧ timeBefore expiry jHi = true :=
  fireTimer_execution worker jHi initial final d device run

/-- When original selection chooses this peer's retransmit timer, a normally
completed original dispatch preserves its allocation identity, increments the
attempt counter at or below the limit, and retains it above the limit. The
retransmit timer is detached and remains detached through this callback; later
worker rearming is outside this call. Selection is an actual prefix run, not an
assumed callback outcome. This is not a universal retry-episode theorem. -/
theorem source_retransmit_dispatch (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Ensures (Env.fireTimer .timerRetransmit jHi)
      (fun w => retryAt w pid = some (identity, attempts, timer) ∧
        ∃ selected, (timerSelection .timerRetransmit jHi).run w =
          .ok ((pid, .retransmitHandshake), selected))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, none)) :=
  fireTimer_retransmit pid jHi identity attempts timer

/-- Every normal original handshake send either exits in its actual prefix
or executes the final retransmit arm hook. Reaching the hook means creation
succeeded, not that the ignored socket-send result was successful. The prefix
retains rate-limit and creation decisions and every intervening operation. -/
theorem source_initiation_arm_path (pid : PeerId) (initial final : World)
    (run : (sendHandshakeInitiation pid).run initial = .ok ((), final)) :
    ∃ reached beforeArm,
      (initiationArmPrefix pid).run initial = .ok (reached, beforeArm) ∧
      if reached then (timersHandshakeInitiated pid).run beforeArm = .ok ((), final)
      else final = beforeArm :=
  sendInitiation_arm_execution pid initial final run

/-- When the original initiation-send prefix reaches the hook with a live peer
on a running device, a normal arm-record-mode completion stores the original
caller-read result plus rekey delay and bounded jitter. Premises concern the actual
post-prefix state; this does not frame the send from function entry, establish
a full retry episode or prove a successful network transmission. -/
theorem source_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial afterPrefix final : World)
    (hprefix : (initiationArmPrefix pid).run initial = .ok (true, afterPrefix))
    (device : afterPrefix.k.wg = some d) (records : afterPrefix.armRecords = true)
    (run : (sendHandshakeInitiation pid).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (callerJiffies .timerJiffiesHandshakeInitiated).run afterPrefix = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout .retransmitJitter).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer .retransmitHandshake
        (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 :=
  sendInitiation_arm_recorded pid d p resident running alive initial afterPrefix final
    hprefix device records run

/-- At either original timer-jitter site, a finite contiguous rejected-draw
prefix followed by an accepted byte returns that byte's scaled jitter, consumes
exactly those records and preserves the entire remaining World. Records use the
original one-byte payload with seven padding zeros; arbitrary suffixes remain.
This is total execution of the original sampler, not a distribution claim. -/
theorem source_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (w : World)
    (records : w.hidden = some (jitterStream site rejected accepted rest)) :
    (jitterBelowRekeyTimeout site.hiddenSite).run w =
      .ok (jitterValue accepted, { w with hidden := some rest }) :=
  jitter_records site rejected accepted rest bad good w records

/-- A finite contiguous stream containing only rejected jitter bytes ends at
the exact original missing-record error. The record-derived budget includes the
extra read, so this is hidden-input exhaustion before budget exhaustion. Empty
streams are included; recordless placeholder execution and ambient interleavings
are outside this contract. -/
theorem source_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (w : World) (records : w.hidden = some (rejected.map (jitterRecord site))) :
    (jitterBelowRekeyTimeout site.hiddenSite).run w =
      .error (.hidden s!"no record left for {site.hiddenSite.info.label}") :=
  jitter_exhausted site rejected bad w records



/-- A normally returning original handshake-send worker preserves identity and
retry attempts and releases one reference. More than one entry reference keeps
the peer resident after that release. This is the worker body, before composition
with the environment's selection/dequeue and a complete retry episode. -/
theorem source_send_worker_frame (pid : PeerId) (identity attempts refs : Nat)
    (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid)
      (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs - 1)) :=
  handshakeSendWorker_workerView pid identity attempts refs retained

end Leanux.Proofs.WG.TimerDiscipline
