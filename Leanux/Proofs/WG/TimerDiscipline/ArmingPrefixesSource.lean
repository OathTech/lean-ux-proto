import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

-- Local form of campaign 1's Framing.liftWG_bind for actual product composition.
private theorem liftWG_bind_variant {α β : Type} (a : WG.M α) (f : α → WG.M β) :
    liftWG (a >>= f) = (liftWG a >>= fun x => liftWG (f x)) := by
  have lifted {γ : Type} (action : WG.M γ) (w) :
      (liftWG action).run w = ((action.run w.wg).run w.ambient).map
        (fun ((x, g), ambient) => (x, {w with wg := g, ambient})) := by
    unfold liftWG StateT.run
    cases action w.wg w.ambient <;> rfl
  funext w
  change (liftWG (a >>= f)).run w = (liftWG a >>= fun x => liftWG (f x)).run w
  rw [lifted]
  simp only [StateT.run_bind]
  rw [lifted]
  cases hr : (a.run w.wg).run w.ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨x, g⟩, ambient⟩
    simp only [Except.map]
    exact (lifted (f x) {w with wg := g, ambient}).symm

def dataSentPrefix (pid : PeerId) : WG.M Bool := do
  branch .timersDataSentNotPending !((← getPeer pid).timerPending .newHandshake)

theorem dataSent_source (pid : PeerId) :
    timersDataSent pid = (do
      if ← dataSentPrefix pid then
        jitteredArm .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS)) := by
  simp only [timersDataSent, dataSentPrefix, jitteredArm, bind_assoc]

theorem dataSentPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false) :
    Config.Product.Returns (liftWG (dataSentPrefix pid))
      (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = true ∧ w.wg.dev = some d ∧ w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let inputs := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .timersDataSentNotPending, outcome := true,
    netRx := initial.ambient.netRxSection}}
  have native : ((dataSentPrefix pid).run initial.wg).run initial.ambient =
      .ok ((true, initial.wg), inputs) := by
    simp [dataSentPrefix, getPeer, getDev, device, resident, absent, branch, AmbientM.branch, inputs]
    rfl
  refine ⟨true, {initial with ambient := inputs}, ?_, rfl, device, records⟩
  change (((dataSentPrefix pid).run initial.wg).run initial.ambient >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _
  rw [native]
  rfl

/-- The recorded effect retains the actual prefix/caller/jitter runs and all
current wheel metadata, rather than the former expiry-only Peer update. -/
theorem dataSent_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersDataSent pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead jitter afterJitter,
      (liftWG (dataSentPrefix pid)).run initial = .ok (true, beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesDataSent)).run beforeRead = .ok (some caller, afterRead) ∧
      (liftWG (jitterBelowRekeyTimeout .newHandshakeJitter)).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .newHandshake
        (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller
        (Campaign2.Product.snapshot final).wg := by
  obtain ⟨ready, beforeRead, hprefix, readyValue, hd, hm⟩ :=
    dataSentPrefix_returns pid d p resident absent initial ⟨device, records⟩
  subst ready
  rw [dataSent_source, liftWG_bind_variant, StateT.run_bind, hprefix] at run
  change (liftWG (jitteredArm .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
    (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS))).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, jitter, afterJitter, hread, hjitter, bound, effect⟩ :=
    jitteredArm_recorded_clock .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
      (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS) d p resident running alive
      beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, jitter, afterJitter, hprefix, hread, hjitter, bound, effect⟩

theorem discardedArm_recorded_clock (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (discard (modPeerTimer site pid timer delay) : WG.M Unit)).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (liftWG (callerJiffies site)).run initial = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot initial).wg pid p timer delay caller
        (Campaign2.Product.snapshot final).wg := by
  change ((((modPeerTimer site pid timer delay).run initial.wg).run initial.ambient >>=
    fun ((_, current), inputs) => .ok (((), current), inputs)) >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  cases arm : ((modPeerTimer site pid timer delay).run initial.wg).run initial.ambient with
  | error stop => rw [arm] at run; cases run
  | ok pair =>
    obtain ⟨⟨allowed, current⟩, inputs⟩ := pair
    rw [arm] at run
    cases run
    have productRun : (liftWG (modPeerTimer site pid timer delay)).run initial =
        .ok (allowed, {initial with wg := current, ambient := inputs}) := by
      change (((modPeerTimer site pid timer delay).run initial.wg).run initial.ambient >>=
        fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _
      rw [arm]
      rfl
    obtain ⟨caller, afterRead, read, value, effect⟩ := modPeerTimer_recorded_clock
      site pid timer delay d p resident initial _ allowed device records productRun
    have yes : allowed = true := by simpa [running, alive] using value
    exact ⟨caller, afterRead, read, by simpa [yes] using effect⟩

def traversalPrefix (pid : PeerId) : WG.M (Nat × Bool) := do
  let interval := (← getPeer pid).persistentKeepaliveInterval
  let enabled ← branchCmp .traversalKeepalive (interval != 0) interval 0
  return (interval, enabled)

theorem traversal_source (pid : PeerId) :
    timersTraversal pid = (do
      let (interval, enabled) ← traversalPrefix pid
      if enabled then
        discard <| modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)) := by
  simp only [timersTraversal, traversalPrefix, bind_assoc, pure_bind]

theorem traversalPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0) :
    Config.Product.Returns (liftWG (traversalPrefix pid))
      (fun w => w.wg.dev = some d ∧ w.ambient.armRecords = true)
      (fun result w => result = (p.persistentKeepaliveInterval, true) ∧
        w.wg.dev = some d ∧ w.ambient.armRecords = true) := by
  intro initial pre
  obtain ⟨device, records⟩ := pre
  let inputs := {initial.ambient with steps := initial.ambient.steps.push {
    decision := .traversalKeepalive, outcome := true,
    operands := some (Int.ofNat p.persistentKeepaliveInterval, 0),
    netRx := initial.ambient.netRxSection}}
  have enabledBool : (p.persistentKeepaliveInterval != 0) = true := by simpa using enabled
  have native : ((traversalPrefix pid).run initial.wg).run initial.ambient =
      .ok (((p.persistentKeepaliveInterval, true), initial.wg), inputs) := by
    simp [traversalPrefix, getPeer, getDev, device, resident, enabledBool, branchCmp, AmbientM.branchCmp, inputs]
    rfl
  refine ⟨(p.persistentKeepaliveInterval, true), {initial with ambient := inputs}, ?_, rfl, device, records⟩
  change (((traversalPrefix pid).run initial.wg).run initial.ambient >>=
    fun ((value, current), inputs) => .ok (value, {initial with wg := current, ambient := inputs})) = _
  rw [native]
  rfl

theorem traversal_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.wg.dev = some d) (records : initial.ambient.armRecords = true)
    (run : (liftWG (timersTraversal pid)).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (liftWG (traversalPrefix pid)).run initial = .ok ((p.persistentKeepaliveInterval, true), beforeRead) ∧
      (liftWG (callerJiffies .timerJiffiesTraversal)).run beforeRead = .ok (some caller, afterRead) ∧
      recordedTimerEffect (Campaign2.Product.snapshot beforeRead).wg pid p .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ) caller (Campaign2.Product.snapshot final).wg := by
  obtain ⟨ready, beforeRead, hprefix, readyValue, hd, hm⟩ :=
    traversalPrefix_returns pid d p resident enabled initial ⟨device, records⟩
  subst ready
  rw [traversal_source, liftWG_bind_variant, StateT.run_bind, hprefix] at run
  change (liftWG (discard (modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive
    (p.persistentKeepaliveInterval * HZ)) : WG.M Unit)).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesTraversal pid .persistentKeepalive (p.persistentKeepaliveInterval * HZ)
    d p resident running alive beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
