import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge
import Leanux.Proofs.WG.TimerDiscipline.JitterBoundClaims

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem projected_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) :
    Campaign2.Observes (jitterBelowRekeyTimeout site.hiddenSite)
      (fun s => s.ambient.hidden = some (jitterStream site rejected accepted rest))
      (fun initial out => out = .ok (jitterValue accepted, withRecords initial rest)) := by
  intro w records
  rw [source_jitter_records site rejected accepted rest bad good w records]
  rfl

theorem projected_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte) :
    Campaign2.Observes (jitterBelowRekeyTimeout site.hiddenSite)
      (fun s => s.ambient.hidden = some (rejected.map (jitterRecord site)))
      (fun _ out => out = .error (.hidden s!"no record left for {site.hiddenSite.info.label}")) := by
  intro w records
  rw [source_jitter_exhausted site rejected bad w records]
  rfl


/-- Caller provenance is observed from the same entry as the original guarded arm. -/
theorem projected_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observed (modPeerTimer site pid timer delay) (callerJiffies site))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧ result.2 = (d.running && !p.isDead) ∧
        if result.2 then
          final.peerAt pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
          clockGap final caller
        else final.peerAt pid = some p) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨caller, afterRead, read, guard, effect⟩ :=
    source_guarded_arm_recorded site pid timer delay d p resident initial final result pre.1 pre.2 run
  exact ⟨caller, snapshot afterRead, observe_ok read, guard, effect⟩

theorem projected_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersSessionDerived pid)
      (callerJiffies .timerJiffiesSessionDerived))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧
        final.peerAt pid = some (p.setTimer .zeroKeyMaterial
          (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨caller, afterRead, read, peer, gap⟩ :=
    source_session_derived_recorded pid d p resident running alive initial final pre.1 pre.2 run
  exact ⟨caller, snapshot afterRead, observe_ok read, peer, gap⟩

theorem projected_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersHandshakeInitiated pid)
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ caller afterRead jitter afterJitter,
        result.1 = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        final.peerAt pid = some (p.setTimer .retransmitHandshake
          (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bound, peer, gap⟩ :=
    source_handshake_initiated_recorded pid d p resident running alive initial final pre.1 pre.2 run
  exact ⟨caller, snapshot afterRead, jitter, snapshot afterJitter,
    observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bound, peer, gap⟩

theorem projected_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersDataSent pid)
      (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead jitter afterJitter,
        result.1 = .ok ((true, beforeRead, some caller, afterRead, jitter), afterJitter) ∧
        jitter < HZ / 3 ∧ final.peerAt pid = some (p.setTimer .newHandshake
          (some (caller + (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
        clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, jitter, afterJitter, first, read, draw, bound, peer, gap⟩ :=
    source_data_sent_recorded pid d p resident absent running alive initial final pre.1 pre.2 run
  exact ⟨snapshot beforeRead, caller, snapshot afterRead, jitter, snapshot afterJitter,
    observe_ok (prefixClockJitterPath_run _ _ _ _ _ _ _ _ _ _ first read draw), bound, peer, gap⟩

theorem projected_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok (((p.persistentKeepaliveInterval, true), beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some (p.setTimer .persistentKeepalive
          (some (caller + (p.persistentKeepaliveInterval * HZ).toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, first, read, peer, gap⟩ :=
    source_traversal_recorded pid d p resident enabled running alive initial final pre.1 pre.2 run
  exact ⟨snapshot beforeRead, caller, snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), peer, gap⟩

theorem projected_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (timersDataReceived pid)
      (prefixClockPath (dataReceivedPrefix pid) .timerJiffiesDataReceived))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok ((some true, beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some (p.setTimer .sendKeepalive
          (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, first, read, peer, gap⟩ :=
    source_data_received_recorded pid d p resident absent running alive initial final pre.1 pre.2 run
  exact ⟨snapshot beforeRead, caller, snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), peer, gap⟩


/-- The conditional premises concern the actual post-send snapshot. -/
theorem projected_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
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
            .sendKeepalive (some (caller + KEEPALIVE_TIMEOUT_TICKS.toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  apply prefixInspect_property
  intro choice afterSend send
  cases choice
  intro device records
  obtain ⟨beforeRead, caller, afterRead, first, read, peer, gap⟩ :=
    source_expired_keepalive_recorded pid d p resident needed running alive initial afterSend final
      send device records run
  exact ⟨snapshot beforeRead, caller, snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), peer, gap⟩

theorem projected_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Ensures (observed (expiredRetransmitHandshake pid) (giveUpClockPath pid))
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true)
      (fun result final => ∃ afterDecision beforeRead caller afterRead,
        result.1 = .ok ((true, afterDecision, true, beforeRead, some caller), afterRead) ∧
        final.peerAt pid = some ((giveUpPeer p).setTimer .zeroKeyMaterial
          (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨afterDecision, beforeRead, caller, afterRead, decision, first, read, peer, gap⟩ :=
    source_retransmit_giveup_recorded pid d p resident limit absent running alive initial final
      pre.1 pre.2 run
  refine ⟨snapshot afterDecision, snapshot beforeRead, caller, snapshot afterRead, ?_, peer, gap⟩
  apply observe_ok
  simp only [giveUpClockPath, StateT.run_bind, decision]
  change ((prefixClockPath (giveUpArmPrefix pid) .timerJiffiesRetransmitZeroKey).run afterDecision
    >>= fun out => Except.ok ((true, snapshot afterDecision, out.1), out.2)) = _
  rw [prefixClockPath_run _ _ _ _ _ _ _ first read]; rfl

theorem projected_timer_dispatch_due (worker : Worker) (jHi : UInt64) (d : Device) :
    Campaign2.Ensures (observed (Env.fireTimer worker jHi) (timerExecutionPath worker jHi))
      (fun s => s.wg.device = some d)
      (fun result final => ∃ pid timer selected,
        result.1 = .ok ((pid, timer, selected), final) ∧
        worker.timer? = some timer ∧ selected.wg.device = some d ∧
        pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
          p.timer timer = some expiry ∧ timeBefore expiry jHi = true) := by
  apply observed_effect
  intro initial result final device run
  cases result
  obtain ⟨pid, timer, selected, selection, callback, kind, same, due⟩ :=
    source_timer_dispatch_due worker jHi initial final d device run
  refine ⟨pid, timer, snapshot selected, ?_, kind, same, due⟩
  apply observe_ok
  simp only [timerExecutionPath, StateT.run_bind, selection]
  change ((fireSelected worker pid timer).run selected >>= fun out =>
    Except.ok ((pid, timer, snapshot selected), out.2)) = _
  rw [callback]; rfl

theorem projected_retransmit_dispatch (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Campaign2.Ensures (observed (Env.fireTimer .timerRetransmit jHi)
      (timerSelection .timerRetransmit jHi))
      (fun s => retryObservation s pid = some (identity, attempts, timer))
      (fun result final => ∀ selected,
        result.1 = .ok ((pid, .retransmitHandshake), selected) →
        retryObservation final pid = some (identity, nextAttempts attempts, none)) := by
  apply observed_effect
  intro initial result final pre run selected selection
  cases hp : (timerSelection .timerRetransmit jHi).run initial with
  | error e => simp [observeResult, hp, Except.map] at selection
  | ok pair =>
    obtain ⟨⟨actualPid, actualTimer⟩, middle⟩ := pair
    rw [observe_ok hp] at selection
    obtain ⟨values, _⟩ := Prod.mk.inj (Except.ok.inj selection)
    obtain ⟨pidEq, timerEq⟩ := Prod.mk.inj values
    subst actualPid
    subst actualTimer
    exact source_retransmit_dispatch pid jHi identity attempts timer initial result final
      ⟨pre, middle, hp⟩ run

theorem projected_initiation_arm_path (pid : PeerId) :
    Campaign2.Ensures (observed (sendHandshakeInitiation pid) (initiationExecutionPath pid))
      (fun _ => True)
      (fun result final => ∃ reached beforeArm,
        result.1 = .ok ((reached, beforeArm), final) ∧
        (reached = false → final = beforeArm)) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  obtain ⟨reached, beforeArm, first, finish⟩ := source_initiation_arm_path pid initial final run
  refine ⟨reached, snapshot beforeArm, ?_, ?_⟩
  · apply observe_ok
    simp only [initiationExecutionPath, StateT.run_bind, first]
    cases reached with
    | false =>
      change final = beforeArm at finish
      rw [finish]; rfl
    | true =>
      change ((timersHandshakeInitiated pid).run beforeArm >>= fun out =>
        Except.ok ((true, snapshot beforeArm), out.2)) = _
      rw [finish]; rfl
  · intro h
    subst reached
    change final = beforeArm at finish
    rw [finish]

theorem projected_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
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
            (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧ clockGap final caller) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  apply prefixInspect_property
  intro reached afterPrefix first reachedTrue device records
  subst reached
  obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bound, peer, gap⟩ :=
    source_initiation_send_arm pid d p resident running alive initial afterPrefix final
      first device records run
  exact ⟨caller, snapshot afterRead, jitter, snapshot afterJitter,
    observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bound, peer, gap⟩

end Leanux.Proofs.WG.TimerDiscipline
