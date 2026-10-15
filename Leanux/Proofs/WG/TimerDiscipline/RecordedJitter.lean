import Leanux.Proofs.WG.TimerDiscipline.RecordedSite

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Recorded-mode variant of jitter_bounded, also framing the mode bit. -/
theorem jitter_recorded_bounded (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k ∧ w.armRecords = true⌝⦄ jitterBelowRekeyTimeout site
      ⦃⇓? n w => ⌜(P w.k ∧ w.armRecords = true) ∧ n < HZ / 3⌝⦄ := by
  have byte_bound (bs : List UInt8) : 83 * (bs[0]?.getD default).toNat / 256 < 83 := by
    have hb := UInt8.toNat_lt_size (bs[0]?.getD default)
    change _ < 256 at hb
    omega
  have hh := hidden_recorded_kernel_spec P
  mvcgen [jitterBelowRekeyTimeout, recordBudget, budgetExhausted, invariant, unsupported, hh]
  case inv1 => exact (⇓? r w => ⌜(P w.k ∧ w.armRecords = true) ∧
    ∀ n, r.2.1 = some n → n < HZ / 3⌝)
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [HZ, ExceptConds.true, ExceptConds.const]
  all_goals try omega
  all_goals exact byte_bound _

def armIfGuard (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : UInt64) : M Unit := do
  if ← modPeerTimerGuard pid then armTimer pid timer delay (some caller)

theorem armIfGuard_recorded (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false) :
    Ensures (armIfGuard pid timer delay caller)
      (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun _ w => peerAt w pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, w.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1) := by
  have ha := (ensures_iff _ _ _).mp (armTimer_recorded pid timer delay caller p)
  rw [ensures_iff]
  mvcgen [armIfGuard, modPeerTimerGuard, Leanux.WG.andM,
    getPeer, getDev, getK, branch, invariant, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]
  all_goals grind only

def jitteredArm (callerSite jitterSite : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (baseDelay : Nat) : M Unit := do
  let caller ← callerJiffies callerSite
  let jitter ← jitterBelowRekeyTimeout jitterSite
  if ← modPeerTimerGuard pid then armTimer pid timer (baseDelay + jitter) caller

theorem handshakeInitiated_source (pid : PeerId) :
    timersHandshakeInitiated pid = jitteredArm .timerJiffiesHandshakeInitiated
      .retransmitJitter pid .retransmitHandshake REKEY_TIMEOUT_TICKS := rfl

theorem jitteredArm_recorded_clock (callerSite jitterSite : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (baseDelay : Nat)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (jitteredArm callerSite jitterSite pid timer baseDelay).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (callerJiffies callerSite).run initial = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout jitterSite).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer timer (some (caller + (baseDelay + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  simp only [jitteredArm, StateT.run_bind] at run
  cases hr : (callerJiffies callerSite).run initial with
  | error err => rw [hr] at run; cases run
  | ok pair =>
    obtain ⟨value, afterRead⟩ := pair
    have info := (ensures_iff _ _ _).mpr (callerJiffies_recorded_spec callerSite d)
      initial value afterRead ⟨device, records⟩ hr
    cases value with
    | none => simp at info
    | some caller =>
      rw [hr] at run
      change ((jitterBelowRekeyTimeout jitterSite).run afterRead >>= fun out =>
        (armIfGuard pid timer (baseDelay + out.1) caller).run out.2) = .ok ((), final) at run
      cases hj : (jitterBelowRekeyTimeout jitterSite).run afterRead with
      | error err => rw [hj] at run; cases run
      | ok pair =>
        obtain ⟨jitter, afterJitter⟩ := pair
        have jitterInfo := (ensures_iff _ _ _).mpr
          (jitter_recorded_bounded (fun k => k.wg = some d) jitterSite)
          afterRead jitter afterJitter info.2 hj
        rw [hj] at run
        have effect := armIfGuard_recorded pid timer (baseDelay + jitter) caller d p
          resident running alive afterJitter () final jitterInfo.1 run
        exact ⟨caller, afterRead, jitter, afterJitter, rfl, hj, jitterInfo.2, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
