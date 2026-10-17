import Leanux.Proofs.WG.TimerDiscipline.RecordedFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def afterCaller (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : UInt64) : WG.M Bool := do
  if ← modPeerTimerGuard pid then
    armTimer pid timer delay (some caller)
    return true
  return false

/-- Exact WG effect after a specific, actually witnessed caller read. -/
def recordedTimerEffect (entry : Campaign2.State) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (delay : Nat) (caller : UInt64) (final : Campaign2.State) : Prop :=
  ∃ now unit, 0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
    if p.timer timer = some (caller + delay.toUInt64) then
      final = recordedArmPrefixView entry pid timer now unit
    else ∃ clk, final = wheelPlacementView
      {recordedArmPrefixView entry pid timer now unit with timerClk := some clk}
      pid p timer (caller + delay.toUInt64) clk

theorem afterCaller_recorded (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (afterCaller pid timer delay caller)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true)
      (fun result final => result = (d.running && !p.isDead) ∧
        if result then recordedTimerEffect entry.wg pid p timer delay caller final.wg
        else final.wg = entry.wg) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, device, mode⟩
  change g.dev = some d at device
  change (((modPeerTimerGuard pid).run g).run ambient >>= fun ((allowed, current), checked) =>
    ((if allowed then do armTimer pid timer delay (some caller); pure true else pure false : WG.M Bool).run current).run checked) = _ at run
  cases guard : ((modPeerTimerGuard pid).run g).run ambient with
  | error stop => rw [guard] at run; cases run
  | ok pair =>
    obtain ⟨⟨allowed, current⟩, checked⟩ := pair
    obtain ⟨value, same, checkedMode⟩ := modPeerTimerGuard_input_effect pid d p resident
      g current ambient checked allowed device guard
    subst current
    rw [guard] at run
    cases allowed with
    | false => cases run; exact ⟨value, rfl⟩
    | true =>
      change (((armTimer pid timer delay (some caller)).run g).run checked >>= fun ((_, current), inputs) =>
        .ok ((true, current), inputs)) = _ at run
      cases armed : ((armTimer pid timer delay (some caller)).run g).run checked with
      | error stop => rw [armed] at run; cases run
      | ok pair =>
        obtain ⟨⟨u, current⟩, inputs⟩ := pair
        cases u
        rw [armed] at run
        cases run
        refine ⟨value, ?_⟩
        exact armTimer_recorded pid timer delay caller p (Campaign2.snapshot g checked)
          g checked () final after
          ⟨rfl, checkedMode.trans mode, by change peerAt g pid = some p; simp [peerAt, device, resident]⟩ armed

/-- Technical source witness: the caller read is an actual product execution
from the original entry state. The current wheel effect is tied to its result. -/
theorem modPeerTimer_recorded_clock (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
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
      else (Campaign2.Product.snapshot final).wg = (Campaign2.Product.snapshot initial).wg := by
  change (((modPeerTimer site pid timer delay).run initial.wg).run initial.ambient >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  change ((((callerJiffies site).run initial.wg).run initial.ambient >>= fun ((caller, current), inputs) =>
    ((do
      if ← modPeerTimerGuard pid then
        armTimer pid timer delay caller
        return true
      return false : WG.M Bool).run current).run inputs) >>= fun ((value, last), after) =>
      .ok (value, {initial with wg := last, ambient := after})) = _ at run
  rw [bind_assoc] at run
  cases read : ((callerJiffies site).run initial.wg).run initial.ambient with
  | error stop => rw [read] at run; cases run
  | ok pair =>
    obtain ⟨⟨caller, current⟩, inputs⟩ := pair
    obtain ⟨same, mode, supplied⟩ := callerJiffies_input_effect site initial.wg current initial.ambient inputs caller read
    subst current
    cases caller with
    | none => simp [records] at supplied
    | some caller =>
      rw [read] at run
      change (((afterCaller pid timer delay caller).run initial.wg).run inputs >>= fun ((value, last), after) =>
        .ok (value, {initial with wg := last, ambient := after})) = _ at run
      cases rest : ((afterCaller pid timer delay caller).run initial.wg).run inputs with
      | error stop => rw [rest] at run; cases run
      | ok pair =>
        obtain ⟨⟨value, last⟩, after⟩ := pair
        rw [rest] at run
        cases run
        have effects := afterCaller_recorded pid timer delay caller d p resident
          (Campaign2.snapshot initial.wg inputs) initial.wg inputs result last after
          ⟨rfl, device, mode.trans records⟩ rest
        refine ⟨caller, {initial with ambient := inputs}, ?_, effects⟩
        change (((callerJiffies site).run initial.wg).run initial.ambient >>= fun ((value, current), after) =>
          .ok (value, {initial with wg := current, ambient := after})) = _
        rw [read]
        rfl

/-- Technical product execution witness for the original session-derived hook. -/
theorem sessionDerived_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersSessionDerived pid)).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (liftWG (callerJiffies .timerJiffiesSessionDerived)).run initial = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p .zeroKeyMaterial
        ZERO_KEY_MATERIAL_TICKS caller (Campaign2.Product.snapshot final).wg := by
  change ((((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run initial.wg).run initial.ambient >>=
    fun ((_, current), inputs) => .ok (((), current), inputs)) >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  cases arm : ((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run initial.wg).run initial.ambient with
  | error stop => rw [arm] at run; cases run
  | ok pair =>
    obtain ⟨⟨allowed, current⟩, inputs⟩ := pair
    rw [arm] at run
    cases run
    have productRun : (liftWG (modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)).run initial =
        .ok (allowed, {initial with wg := current, ambient := inputs}) := by
      change (((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run initial.wg).run initial.ambient >>=
        fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _
      rw [arm]
      rfl
    obtain ⟨caller, afterRead, read, value, effect⟩ := modPeerTimer_recorded_clock
      .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      d p resident initial _ allowed device records productRun
    have yes : allowed = true := by simpa [running, alive] using value
    exact ⟨caller, afterRead, read, by simpa [yes] using effect⟩

end Leanux.Proofs.WG.TimerDiscipline
