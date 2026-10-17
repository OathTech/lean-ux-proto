import Leanux.Proofs.WG.Noise.Slots
import Leanux.WG.Timers

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The complete WireGuard state update of a normally returning placement.
Record validation is operational; this calculation does not assume it succeeds. -/
def wheelPlacementState (entry : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) : WGWorld :=
  match TimerWheel.place p timer expires clk with
  | .kept _ => {entry with dev := entry.dev.map fun d =>
      {d with peers := d.peers.insert pid (p.setTimer timer (some expires))}}
  | .enqueued slot bucketExpiry =>
      let stamp := entry.timerEnqueues + 1
      let updated := (p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bucketExpiry, stamp⟩)
      {entry with timerEnqueues := stamp, dev := entry.dev.map (fun d => {d with peers := d.peers.insert pid updated})}

/-- Successful placement has the exact kept-slot or enqueue update. No
wheel-consistency, record-readiness or arithmetic-admission premise is added. -/
theorem placeOnWheel_effect (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64)
    (unit? : Option Nat) (entry : WGWorld) (p : Peer)
    (resident : peerAt entry pid = some p) :
    Ensures (placeOnWheel pid timer expires clk unit?) (fun g => g = entry)
      (fun _ g => g = wheelPlacementState entry pid p timer expires clk) := by
  have hread : Ensures (getPeer pid) (fun g => g = entry)
      (fun value g => value = p ∧ g = entry) := by
    intro g ambient value final after same run
    obtain ⟨state, found⟩ := (ensures_iff _ _ _).mpr
      (getPeer_spec pid (fun g => g = entry)) g ambient value final after same run
    subst final
    exact ⟨Option.some.inj (found.symm.trans resident), rfl⟩
  have hfinish (expected : WGWorld) :
      Ensures (do
        if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
          invariant s!"peer {pid}'s timers: {what}" : WG.M Unit)
        (fun g => g = expected) (fun _ g => g = expected) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun g => g = expected))) ?_
    intro peer
    cases problem : TimerWheel.peerWheelProblem peer with
    | none =>
      intro g ambient result final after pre run
      cases run
      exact pre.1
    | some what =>
      intro g ambient result final after pre run
      cases run
  unfold placeOnWheel
  refine ensures_bind _ _ hread ?_
  intro found g ambient result final after pre run
  obtain ⟨same, state⟩ := pre
  subst found
  subst g
  have rest : Ensures (do
      match TimerWheel.place p timer expires clk with
      | .kept _ =>
        setPeer pid (p.setTimer timer (some expires))
        if unit?.isSome then
          if (← peekHiddenSite) == some HiddenSite.timerEnqueue.info.id then
            throw (.hidden s!"Linux re-enqueued peer {pid}'s {repr timer} timer, which the mirror keeps in its slot (expires {expires}, base clock {clk})")
      | .enqueued slot bexp =>
        if let some u := unit? then
          let eb ← hidden .timerEnqueue
          let (ridx, rbexp, u3) := (recordWord eb 0, recordWord64 eb 1, recordWord eb 2)
          if u != 0 && u3 != u then
            throw (.hidden s!"the enqueue record names timer {u3}, the arm record {u}")
          if ridx != slot || rbexp != bexp then
            throw (.hidden s!"wheel arithmetic differs from Linux for peer {pid}'s {repr timer} timer: expires {expires}, base clock {clk}: the mirror puts it in slot {slot} at bucket expiry {bexp}, Linux in slot {ridx} at {rbexp}")
        let lvl := TimerWheel.levelOf slot
        if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
          invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
        let stamp := (← get).timerEnqueues + 1
        modify fun k => {k with timerEnqueues := stamp}
        setPeer pid ((p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bexp, stamp⟩))
      if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
        invariant s!"peer {pid}'s timers: {what}")
      (fun g => g = entry)
      (fun _ g => g = wheelPlacementState entry pid p timer expires clk) := by
    cases placement : TimerWheel.place p timer expires clk with
    | kept we =>
      simp only [placement, wheelPlacementState]
      refine ensures_bind
        (Q := fun _ g => g = {entry with dev := entry.dev.map (fun d =>
          {d with peers := d.peers.insert pid (p.setTimer timer (some expires))})}) _ _ ?_ ?_
      · intro g ambient value final after same run
        subst g
        cases run
        rfl
      · intro _
        cases unit? with
        | none => exact hfinish _
        | some u =>
          refine ensures_bind _ _
            ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant AmbientM.peekHiddenSite _)) ?_
          intro site
          split
          · intro g ambient value final after same run
            cases run
          · exact hfinish _
    | enqueued slot bexp =>
      simp only [placement, wheelPlacementState]
      let expected : WGWorld :=
        {entry with timerEnqueues := entry.timerEnqueues + 1, dev := entry.dev.map (fun d => {d with peers := d.peers.insert pid ((p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bexp, entry.timerEnqueues + 1⟩))})}
      have writeReady : Ensures (do
          let stamp := (← get).timerEnqueues + 1
          modify fun k => {k with timerEnqueues := stamp}
          setPeer pid ((p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bexp, stamp⟩))
          if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
            invariant s!"peer {pid}'s timers: {what}" : WG.M Unit)
          (fun g => g = entry) (fun _ g => g = expected) := by
        intro g ambient value final after same run
        subst g
        exact hfinish expected expected ambient value final after rfl run
      have admitted : Ensures (do
          let lvl := TimerWheel.levelOf slot
          if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
            invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
          let stamp := (← get).timerEnqueues + 1
          modify fun k => {k with timerEnqueues := stamp}
          setPeer pid ((p.setTimer timer (some expires)).setWheel timer (some ⟨slot, bexp, stamp⟩))
          if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
            invariant s!"peer {pid}'s timers: {what}" : WG.M Unit)
          (fun g => g = entry) (fun _ g => g = expected) := by
        dsimp only
        split
        · intro g ambient value final after same run
          cases run
        · exact writeReady
      cases unit? with
      | none => exact admitted
      | some u =>
        refine ensures_bind _ _
          ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden .timerEnqueue) _)) ?_
        intro bytes
        split
        · intro g ambient value final after same run
          cases run
        · split
          · intro g ambient value final after same run
            cases run
          · exact admitted
  exact rest entry ambient result final after rfl run

end Leanux.Proofs.WG.TimerDiscipline
