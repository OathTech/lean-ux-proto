import Leanux.Proofs.WG.TimerDiscipline.HookObservationPaths

/-! Full Product observations of original timer hooks. Recorded arm conclusions
explicitly include current wheel, clock, unit and enqueue effects. Every source
witness comes from the actual execution, including post-prefix snapshots. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Caller provenance is observed from the same entry as the original guarded arm. -/
theorem projected_guarded_arm_recorded (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (modPeerTimer site pid timer delay)) (liftWG (callerJiffies site)))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧ result.2 = (d.running && !p.isDead) ∧
        if result.2 then
          recordedTimerEffect entry.wg pid p timer delay caller final.wg
        else final.wg = entry.wg) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨rfl, device, mode⟩ := pre
  obtain ⟨caller, afterRead, read, guard, effect⟩ :=
    modPeerTimer_recorded_clock site pid timer delay d p resident initial final result device mode run
  exact ⟨caller, Product.snapshot afterRead, observe_ok read, guard, effect⟩

theorem projected_session_derived_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (timersSessionDerived pid))
      (liftWG (callerJiffies .timerJiffiesSessionDerived)))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead,
        result.1 = .ok (some caller, afterRead) ∧
        recordedTimerEffect entry.wg pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨rfl, device, mode⟩ := pre
  cases result
  obtain ⟨caller, afterRead, read, effect⟩ :=
    sessionDerived_recorded_clock pid d p resident running alive initial final device mode run
  exact ⟨caller, Product.snapshot afterRead, observe_ok read, effect⟩

theorem projected_handshake_initiated_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false) (entry : Product.Snapshot) :
    Campaign2.Product.Ensures (observed (liftWG (timersHandshakeInitiated pid))
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ caller afterRead jitter afterJitter,
        result.1 = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        recordedTimerEffect entry.wg pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  obtain ⟨rfl, device, mode⟩ := pre
  cases result
  obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bound, effect⟩ :=
    jitteredArm_recorded_clock .timerJiffiesHandshakeInitiated .retransmitJitter pid
      .retransmitHandshake REKEY_TIMEOUT_TICKS d p resident running alive initial final device mode
      (by simpa only [handshakeInitiated_source] using run)
  exact ⟨caller, Product.snapshot afterRead, jitter, Product.snapshot afterJitter,
    observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bound, effect⟩

theorem projected_data_sent_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersDataSent pid))
      (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead jitter afterJitter,
        result.1 = .ok ((true, beforeRead, some caller, afterRead, jitter), afterJitter) ∧
        jitter < HZ / 3 ∧ recordedTimerEffect beforeRead.wg pid p .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, jitter, afterJitter, first, read, draw, bound, effect⟩ :=
    dataSent_recorded_clock pid d p resident absent running alive initial final pre.1 pre.2 run
  exact ⟨Product.snapshot beforeRead, caller, Product.snapshot afterRead, jitter, Product.snapshot afterJitter,
    observe_ok (prefixClockJitterPath_run _ _ _ _ _ _ _ _ _ _ first read draw), bound, effect⟩

theorem projected_traversal_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok (((p.persistentKeepaliveInterval, true), beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid p .persistentKeepalive
          (p.persistentKeepaliveInterval * HZ) caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, first, read, effect⟩ :=
    traversal_recorded_clock pid d p resident enabled running alive initial final pre.1 pre.2 run
  exact ⟨Product.snapshot beforeRead, caller, Product.snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), effect⟩

theorem projected_data_received_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .sendKeepalive = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (timersDataReceived pid))
      (prefixClockPath (liftWG (dataReceivedPrefix pid)) .timerJiffiesDataReceived))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ beforeRead caller afterRead,
        result.1 = .ok ((some true, beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨beforeRead, caller, afterRead, first, read, effect⟩ :=
    dataReceived_recorded_clock pid d p resident absent running alive initial final pre.1 pre.2 run
  exact ⟨Product.snapshot beforeRead, caller, Product.snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), effect⟩


/-- The conditional premises concern the actual post-send Product snapshot. -/
theorem projected_expired_keepalive_recorded (pid : PeerId) (d : Device) (p : Peer)
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
            .sendKeepalive KEEPALIVE_TIMEOUT_TICKS caller final.wg) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  apply prefixInspect_property
  intro choice afterSend send
  cases choice
  intro device records
  obtain ⟨beforeRead, caller, afterRead, first, read, effect⟩ :=
    expiredKeepalive_recorded_clock pid d p resident needed running alive initial afterSend final
      send device records run
  exact ⟨Product.snapshot beforeRead, caller, Product.snapshot afterRead,
    observe_ok (prefixClockPath_run _ _ _ _ _ _ _ first read), effect⟩

theorem projected_retransmit_giveup_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (limit : p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES)
    (absent : p.timerPending .zeroKeyMaterial = false)
    (running : d.running = true) (alive : p.isDead = false) :
    Campaign2.Product.Ensures (observed (liftWG (expiredRetransmitHandshake pid)) (giveUpClockPath pid))
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => ∃ afterDecision beforeRead caller afterRead,
        result.1 = .ok ((true, afterDecision, true, beforeRead, some caller), afterRead) ∧
        recordedTimerEffect beforeRead.wg pid (giveUpWheelPeer p) .zeroKeyMaterial
          ZERO_KEY_MATERIAL_TICKS caller final.wg) := by
  apply observed_effect
  intro initial result final pre run
  cases result
  obtain ⟨afterDecision, beforeRead, caller, afterRead, decision, first, read, effect⟩ :=
    retransmitGiveUp_recorded_clock pid d p resident limit absent running alive initial final
      pre.1 pre.2 run
  refine ⟨Product.snapshot afterDecision, Product.snapshot beforeRead, caller, Product.snapshot afterRead, ?_, effect⟩
  apply observe_ok
  simp only [giveUpClockPath, StateT.run_bind, decision]
  change ((prefixClockPath (liftWG (giveUpArmPrefix pid)) .timerJiffiesRetransmitZeroKey).run afterDecision
    >>= fun out => Except.ok ((true, Product.snapshot afterDecision, out.1), out.2)) = _
  rw [prefixClockPath_run _ _ _ _ _ _ _ first read]; rfl

theorem projected_initiation_arm_path (pid : PeerId) :
    Campaign2.Product.Ensures (observed (liftWG (sendHandshakeInitiation pid)) (initiationExecutionPath pid))
      (fun _ => True)
      (fun result final => ∃ reached beforeArm,
        result.1 = .ok ((reached, beforeArm), final) ∧
        (reached = false → final = beforeArm)) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  obtain ⟨reached, beforeArm, first, finish⟩ := sendInitiation_arm_execution pid initial final run
  refine ⟨reached, Product.snapshot beforeArm, ?_, ?_⟩
  · apply observe_ok
    simp only [initiationExecutionPath, StateT.run_bind, first]
    cases reached with
    | false =>
      change final = beforeArm at finish
      rw [finish]; rfl
    | true =>
      change ((liftWG (timersHandshakeInitiated pid)).run beforeArm >>= fun out =>
        Except.ok ((true, Product.snapshot beforeArm), out.2)) = _
      rw [finish]; rfl
  · intro h
    subst reached
    change final = beforeArm at finish
    rw [finish]

theorem projected_initiation_send_arm (pid : PeerId) (d : Device) (p : Peer)
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
            (REKEY_TIMEOUT_TICKS + jitter) caller final.wg) := by
  apply observed_effect
  intro initial result final _ run
  cases result
  apply prefixInspect_property
  intro reached afterPrefix first reachedTrue device records
  subst reached
  obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bound, effect⟩ :=
    sendInitiation_arm_recorded pid d p resident running alive initial afterPrefix final
      first device records run
  exact ⟨caller, Product.snapshot afterRead, jitter, Product.snapshot afterJitter,
    observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bound, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
