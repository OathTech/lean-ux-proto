import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterFrames
import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def armIfGuard (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : UInt64) : WG.M Unit := do
  if ← modPeerTimerGuard pid then armTimer pid timer delay (some caller)

/-- Correct the old expiry-only Peer prediction to the complete current WG effect. -/
theorem armIfGuard_recorded (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (armIfGuard pid timer delay caller)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun _ final => recordedTimerEffect entry.wg pid p timer delay caller final.wg) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, device, mode⟩
  change g.dev = some d at device
  change (((modPeerTimerGuard pid).run g).run ambient >>= fun ((allowed, current), checked) =>
    ((if allowed then armTimer pid timer delay (some caller) else pure () : WG.M Unit).run current).run checked) = _ at run
  cases guard : ((modPeerTimerGuard pid).run g).run ambient with
  | error stop => rw [guard] at run; cases run
  | ok pair =>
    obtain ⟨⟨allowed, current⟩, checked⟩ := pair
    obtain ⟨value, same, checkedMode⟩ := modPeerTimerGuard_input_effect pid d p resident
      g current ambient checked allowed device guard
    subst current
    have yes : allowed = true := by simpa [running, alive] using value
    rw [yes] at guard
    rw [guard] at run
    change ((armTimer pid timer delay (some caller)).run g).run checked = _ at run
    exact armTimer_recorded pid timer delay caller p (Campaign2.snapshot g checked)
      g checked result final after
      ⟨rfl, checkedMode.trans mode, by change peerAt g pid = some p; simp [peerAt, device, resident]⟩ run

def jitteredArm (callerSite jitterSite : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (baseDelay : Nat) : WG.M Unit := do
  let caller ← callerJiffies callerSite
  let jitter ← jitterBelowRekeyTimeout jitterSite
  if ← modPeerTimerGuard pid then armTimer pid timer (baseDelay + jitter) caller

theorem handshakeInitiated_source (pid : PeerId) :
    timersHandshakeInitiated pid = jitteredArm .timerJiffiesHandshakeInitiated
      .retransmitJitter pid .retransmitHandshake REKEY_TIMEOUT_TICKS := rfl

/-- Technical source witness retaining both actual product intermediate states.
The exact current WG arm effect uses the caller and jitter from those runs. -/
theorem jitteredArm_recorded_clock (callerSite jitterSite : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (baseDelay : Nat)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (jitteredArm callerSite jitterSite pid timer baseDelay)).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (liftWG (callerJiffies callerSite)).run initial = .ok (some caller, afterRead) ∧
      (liftWG (jitterBelowRekeyTimeout jitterSite)).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p timer (baseDelay + jitter)
        caller (Campaign2.Product.snapshot final).wg := by
  change ((((callerJiffies callerSite).run initial.wg).run initial.ambient >>=
    fun ((caller, current), inputs) =>
      ((do
        let jitter ← jitterBelowRekeyTimeout jitterSite
        if ← modPeerTimerGuard pid then armTimer pid timer (baseDelay + jitter) caller : WG.M Unit).run current).run inputs) >>=
      fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  rw [bind_assoc] at run
  cases read : ((callerJiffies callerSite).run initial.wg).run initial.ambient with
  | error stop => rw [read] at run; cases run
  | ok pair =>
    obtain ⟨⟨caller, current⟩, inputs⟩ := pair
    obtain ⟨same, mode, supplied⟩ := callerJiffies_input_effect callerSite initial.wg current initial.ambient inputs caller read
    subst current
    cases caller with
    | none => simp [records] at supplied
    | some caller =>
      rw [read] at run
      change ((((jitterBelowRekeyTimeout jitterSite).run initial.wg).run inputs >>=
        fun ((jitter, current), drawn) => ((armIfGuard pid timer (baseDelay + jitter) caller).run current).run drawn) >>=
        fun ((value, current), ending) => .ok (value, {initial with wg := current, ambient := ending})) = _ at run
      rw [bind_assoc] at run
      cases drawn : ((jitterBelowRekeyTimeout jitterSite).run initial.wg).run inputs with
      | error stop => rw [drawn] at run; cases run
      | ok pair =>
        obtain ⟨⟨jitter, current⟩, middle⟩ := pair
        let afterRead := {initial with ambient := inputs}
        let afterJitter := {initial with wg := current, ambient := middle}
        have readProduct : (liftWG (callerJiffies callerSite)).run initial = .ok (some caller, afterRead) := by
          change (((callerJiffies callerSite).run initial.wg).run initial.ambient >>=
            fun ((value, current), after) => .ok (value, {initial with wg := current, ambient := after})) = _
          rw [read]
          rfl
        have jitterProduct : (liftWG (jitterBelowRekeyTimeout jitterSite)).run afterRead =
            .ok (jitter, afterJitter) := by
          change (((jitterBelowRekeyTimeout jitterSite).run initial.wg).run inputs >>=
            fun ((value, current), after) => .ok (value, {afterRead with wg := current, ambient := after})) = _
          rw [drawn]
          rfl
        obtain ⟨⟨same, jitterMode⟩, bound⟩ :=
          jitter_recorded_bounded (fun g _ _ _ => g = initial.wg) jitterSite
            afterRead jitter afterJitter ⟨rfl, mode.trans records⟩ jitterProduct
        change current = initial.wg at same
        subst current
        rw [drawn] at run
        change (((armIfGuard pid timer (baseDelay + jitter) caller).run initial.wg).run middle >>=
          fun ((value, current), ending) => .ok (value, {initial with wg := current, ambient := ending})) = _ at run
        cases armed : ((armIfGuard pid timer (baseDelay + jitter) caller).run initial.wg).run middle with
        | error stop => rw [armed] at run; cases run
        | ok pair =>
          obtain ⟨⟨value, current⟩, ending⟩ := pair
          rw [armed] at run
          cases run
          have effect := armIfGuard_recorded pid timer (baseDelay + jitter) caller d p
            resident running alive (Campaign2.snapshot initial.wg middle)
            initial.wg middle () current ending ⟨rfl, device, jitterMode⟩ armed
          exact ⟨caller, afterRead, jitter, afterJitter, readProduct, jitterProduct, bound, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
