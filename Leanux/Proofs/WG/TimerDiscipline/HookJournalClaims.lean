import Leanux.Proofs.WG.TimerDiscipline.HookJournalSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingSourceClaims
import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventFrames

/-! Immediate effects of source-linked hook receipts. Existing local contracts supply the effects; no global arming count, final stopped state or initialized occurrence claim is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG

theorem Receipt.Valid.sessionDerived {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .sessionDerived) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    if d.running && !p.isDead then
      peerTimerArmEffect r.before r.pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS after.wg
    else after.wg = r.before.wg := by
  apply valid.ensures (P := fun s => s = r.before ∧ s.wg.device = some d)
    (Q := fun _ final => if d.running && !p.isDead then
      peerTimerArmEffect r.before r.pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final.wg
      else final.wg = r.before.wg) ?_ ⟨rfl,device⟩ normal
  simpa only [kind,action] using source_session_derived r.pid d p resident r.before

theorem Receipt.Valid.traversal {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .traversal) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
      peerTimerArmEffect r.before r.pid p .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ) after.wg
    else after.wg = r.before.wg := by
  apply valid.ensures (P := fun s => s = r.before ∧ s.wg.device = some d)
    (Q := fun _ final => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
      peerTimerArmEffect r.before r.pid p .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ) final.wg
      else final.wg = r.before.wg) ?_ ⟨rfl,device⟩ normal
  simpa only [kind,action] using source_traversal r.pid d p resident r.before

theorem Receipt.Valid.authenticatedSent {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .authenticatedSent) (p : Peer)
    (resident : r.before.peerAt r.pid = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    after = delTimerView r.before r.pid p .sendKeepalive := by
  apply valid.ensures (P := fun s => s = r.before ∧ s.peerAt r.pid = some p)
    (Q := fun _ final => final = delTimerView r.before r.pid p .sendKeepalive)
    ?_ ⟨rfl,resident⟩ normal
  simpa only [kind,action] using source_authenticated_sent r.pid p r.before

theorem Receipt.Valid.authenticatedReceived {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .authenticatedReceived) (p : Peer)
    (resident : r.before.peerAt r.pid = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    after = delTimerView r.before r.pid p .newHandshake := by
  apply valid.ensures (P := fun s => s = r.before ∧ s.peerAt r.pid = some p)
    (Q := fun _ final => final = delTimerView r.before r.pid p .newHandshake)
    ?_ ⟨rfl,resident⟩ normal
  simpa only [kind,action] using source_authenticated_received r.pid p r.before

theorem Receipt.Valid.dataReceived {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .dataReceived) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    if d.running then
      if p.timerPending .sendKeepalive then
        after.wg = {r.before.wg with device := some {d with peers := d.peers.insert r.pid {p with timerNeedAnotherKeepalive := true}}}
      else if p.isDead then after.wg = r.before.wg
      else peerTimerArmEffect r.before r.pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS after.wg
    else after.wg = r.before.wg := by
  apply valid.ensures (P := fun s => s = r.before ∧ s.wg.device = some d)
    (Q := fun _ final => if d.running then
      if p.timerPending .sendKeepalive then
        final.wg = {r.before.wg with device := some {d with peers := d.peers.insert r.pid {p with timerNeedAnotherKeepalive := true}}}
      else if p.isDead then final.wg = r.before.wg
      else peerTimerArmEffect r.before r.pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS final.wg
      else final.wg = r.before.wg) ?_ ⟨rfl,device⟩ normal
  simpa only [kind,action] using source_data_received r.pid d p resident r.before

theorem Receipt.Valid.handshakeComplete {r : Receipt} (valid : r.Valid)
    (site : HiddenSite) (kind : r.hook = .handshakeComplete site) (p : Peer)
    (resident : r.before.peerAt r.pid = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    ∃ now, after.peerAt r.pid = some
      {((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
        timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
        walltimeLastHandshake := now} := by
  apply valid.ensures (P := fun s => s.peerAt r.pid = some p)
    (Q := fun _ final => ∃ now, final.peerAt r.pid = some
      {((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
        timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
        walltimeLastHandshake := now}) ?_ resident normal
  simpa only [kind,action] using source_handshake_complete r.pid site p

/-- A completed session-derived hook retains the allocation label and adds
zero or one wheel enqueue. Invocation count and enqueue count are distinct. -/
theorem Receipt.Valid.sessionDerived_counters {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .sessionDerived) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    after.wg.keypairCounter = r.before.wg.keypairCounter ∧
    (after.wg.timerEnqueues = r.before.wg.timerEnqueues ∨
      after.wg.timerEnqueues = r.before.wg.timerEnqueues + 1) := by
  have effect := valid.sessionDerived kind d p device resident normal
  split at effect
  · exact peerTimerArmEffect_counters _ _ _ _ _ _ effect
  · rw [effect]
    exact ⟨rfl,Or.inl rfl⟩

/-- Projected source agreement for the singleton receipt. Stops remain Stops
and carry no invented successor. This is a hook invocation, not proof of
where a caller reached it. -/
theorem original_receipt (hook : Hook) (pid : PeerId) :
    Campaign2.Observes (action hook pid) (fun _ => True)
      (fun before outcome => (⟨hook,pid,before,outcome⟩ : Receipt).Valid) := by
  intro g ambient _
  exact fresh_valid hook pid g ambient

end Leanux.Proofs.WG.TimerDiscipline.HookJournal
