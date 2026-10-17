import Leanux.Proofs.WG.TimerDiscipline.ArmingChangedExpirySource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The recorded prefix keeps all WG observations except the current jiffies
and, when nonzero, the timer-address registration. -/
def recordedArmPrefixView (entry : Campaign2.State) (pid : PeerId) (timer : PeerTimer)
    (now : UInt64) (unit : Nat) : Campaign2.State :=
  {entry with jiffiesLast := some now, timerUnits :=
    if unit != 0 then (unit, pid, timer) :: entry.timerUnits.filter (·.1 != unit)
    else entry.timerUnits}

/-- Exact kept-slot or enqueue effect, including the original wheel stamp counter. -/
def wheelPlacementView (entry : Campaign2.State) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) : Campaign2.State :=
  match TimerWheel.place p timer expires clk with
  | .kept _ =>
    {entry with device := entry.device.map fun d =>
      {d with peers := d.peers.insert pid (p.setTimer timer (some expires))}}
  | .enqueued slot bucketExpiry =>
    let stamp := entry.timerEnqueues + 1
    let updated := (p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bucketExpiry, stamp⟩)
    {entry with timerEnqueues := stamp, device := entry.device.map fun d =>
      {d with peers := d.peers.insert pid updated}}

/-- Deletion clears both the expiry and wheel entry; all other observations remain. -/
def delTimerView (entry : Campaign2.Snapshot) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) : Campaign2.Snapshot :=
  {entry with wg := {entry.wg with device := entry.wg.device.map fun d =>
    {d with peers := d.peers.insert pid ((p.setTimer timer none).setWheel timer none)}}}

/-- Correct the legacy exact-peer conclusion for the wheel representation.
The original resident-peer, recorded-mode and normal-return domain is unchanged. -/
theorem armTimer_recorded (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (armTimer pid timer delay (some caller))
      (fun s => s = entry ∧ s.ambient.armRecords = true ∧ s.peerAt pid = some p)
      (fun _ final => ∃ now unit,
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
        if p.timer timer = some (caller + delay.toUInt64) then
          final.wg = recordedArmPrefixView entry.wg pid timer now unit
        else ∃ clk, final.wg = wheelPlacementView
          {recordedArmPrefixView entry.wg pid timer now unit with timerClk := some clk}
          pid p timer (caller + delay.toUInt64) clk) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, mode, resident⟩
  cases result
  change peerAt g pid = some p at resident
  by_cases same : p.timer timer = some (caller + delay.toUInt64)
  · obtain ⟨now, unit, low, high, effect⟩ :=
      armTimer_sameExpiry_effect pid timer delay caller g p resident same
        ambient after final mode run
    refine ⟨now, unit, low, high, ?_⟩
    rw [ite_eq_left same, effect]
    rfl
  · obtain ⟨now, unit, clk, low, high, effect⟩ :=
      armTimer_changedExpiry_effect pid timer delay caller g p resident same
        ambient after final mode run
    refine ⟨now, unit, low, high, ?_⟩
    rw [ite_eq_right same]
    refine ⟨clk, ?_⟩
    rw [effect]
    cases placement : TimerWheel.place p timer (caller + delay.toUInt64) clk <;>
      simp only [wheelPlacementState, wheelPlacementView, placement]
    all_goals rfl

/-- Exact deletion now includes the wheel entry, retaining the entire initial
snapshot outside the selected peer update. -/
theorem delTimer_exact (pid : PeerId) (timer : PeerTimer) (p : Peer)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (delTimer pid timer)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p timer) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, resident⟩
  change peerAt g pid = some p at resident
  cases device : g.dev with
  | none => simp [peerAt, device] at resident
  | some d =>
    have found : d.peers[pid]? = some p := by simpa [peerAt, device] using resident
    simp [delTimer, getPeer, getDev, setPeer, modifyDev, device, found] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [delTimerView, Campaign2.snapshot, Campaign2.core, device]

end Leanux.Proofs.WG.TimerDiscipline
