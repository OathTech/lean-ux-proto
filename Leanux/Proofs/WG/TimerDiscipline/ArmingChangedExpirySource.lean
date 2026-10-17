import Leanux.Proofs.WG.TimerDiscipline.ArmingSameExpirySource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem armTimer_changedExpiry_effect (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (entry : WGWorld) (p : Peer)
    (resident : peerAt entry pid = some p)
    (changed : p.timer timer ≠ some (caller + delay.toUInt64))
    (ambient after : Ambient) (final : WGWorld)
    (mode : ambient.armRecords = true)
    (run : ((armTimer pid timer delay (some caller)).run entry).run ambient =
      .ok (((), final), after)) :
    ∃ now unit clk, 0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
      final = wheelPlacementState
        {recordedArmPrefixState entry pid timer now unit with timerClk := some clk}
        pid p timer (caller + delay.toUInt64) clk := by
  cases device : entry.dev with
  | none => simp [peerAt, device] at resident
  | some d =>
    have hp : d.peers[pid]? = some p := by simpa [peerAt, device] using resident
    have nativeBind {α β : Type} (a : WG.M α) (f : α → WG.M β) (g : WGWorld) (b : Ambient) :
        ((StateT.bind a f).run g).run b =
          (((a.run g).run b) >>= fun ((value, next), ambient') =>
            ((f value).run next).run ambient') := rfl
    have modifyRun (f : WGWorld → WGWorld) (g : WGWorld) (a : Ambient) :
        ((modify f : WG.M PUnit).run g).run a = .ok ((⟨⟩, f g), a) := rfl
    have devRun (g : WGWorld) (hd : g.dev = some d) :
        getDev.run g = pure (d, g) := by
      simp [getDev, hd]
    have peerRead (g : WGWorld) (a : Ambient) (hd : g.dev = some d) :
        ((getPeer pid).run g).run a = .ok ((p, g), a) := by
      simp [getPeer, getDev, hd, hp]
      rfl
    let clockSuffix (now expires : UInt64) (unit : Nat) (cb : List UInt8) : WG.M Unit := do
      let clk := recordWord64 cb 0
      let u2 := recordWord cb 1
      if unit != 0 && u2 != unit then
        throw (.hidden s!"the base-clock record names timer {u2}, the arm record {unit}")
      if timeAfter clk (now + 1) then
        throw (.hidden s!"the timer base's clock {clk} is more than one past mod_timer's read {now}")
      if let some prev := (← get).timerClk then
        if timeBefore clk prev then
          throw (.hidden s!"the timer base's clock went back: {clk} after {prev}")
      if let some b := TimerWheel.earliestDue (← getDev) now then
        if timeAfter clk b then
          throw (.hidden s!"the timer base's clock {clk} is past the overdue modeled bucket {b} (forward_timer_base stops at next_expiry)")
      if let some step := entry.timerPassStep then
        if !timeAfter clk step then
          throw (.hidden s!"an arm inside a timer pass at step {step} with the base clock {clk} not past it")
      modify fun k => { k with timerClk := some clk }
      placeOnWheel pid timer expires clk (some unit)
    let suffix (now expires : UInt64) (unit : Nat) : WG.M Unit := do
      let cb ← hidden .timerClk
      clockSuffix now expires unit cb
    have suffixEffect (now expires : UInt64) (unit : Nat) (a : Ambient)
        (exec : ((suffix now expires unit).run (recordedArmPrefixState entry pid timer now unit)).run a =
          .ok (((), final), after)) :
        ∃ clk, final = wheelPlacementState
          {recordedArmPrefixState entry pid timer now unit with timerClk := some clk}
          pid p timer expires clk := by
      let prepared := recordedArmPrefixState entry pid timer now unit
      have clockRead : ((hidden .timerClk : WG.M (List UInt8)).run prepared).run a =
          ((AmbientM.hidden .timerClk).run a >>= fun (bytes, next) =>
            Except.ok ((bytes, prepared), next)) := rfl
      change (((hidden .timerClk : WG.M (List UInt8)).run prepared).run a >>= _) = _ at exec
      rw [clockRead] at exec
      cases read : (AmbientM.hidden .timerClk).run a with
      | error err =>
        rw [read] at exec
        cases exec
      | ok out =>
        obtain ⟨bytes, middle⟩ := out
        rw [read] at exec
        change ((clockSuffix now expires unit bytes).run prepared).run middle = _ at exec
        change (((if (unit != 0 && recordWord bytes 1 != unit) = true then _ else _) : WG.M Unit).run prepared).run middle = _ at exec
        by_cases wrongUnit : (unit != 0 && recordWord bytes 1 != unit) = true
        · rw [ite_eq_left wrongUnit] at exec
          cases exec
        · rw [ite_eq_right wrongUnit] at exec
          change (((if timeAfter (recordWord64 bytes 0) (now + 1) = true then _ else _) : WG.M Unit).run prepared).run middle = _ at exec
          by_cases forward : timeAfter (recordWord64 bytes 0) (now + 1) = true
          · rw [ite_eq_left forward] at exec
            cases exec
          · rw [ite_eq_right forward] at exec
            simp only [StateT.run_bind, StateT.run_get, pure_bind] at exec
            have preparedClk : prepared.timerClk = entry.timerClk := rfl
            cases previous : entry.timerClk <;> simp only [preparedClk, previous] at exec
            all_goals
              try
                rename_i prev
                by_cases rewind : timeBefore (recordWord64 bytes 0) prev = true
                all_goals first
                  | (rw [ite_eq_left rewind] at exec; cases exec)
                  | rw [ite_eq_right rewind] at exec
            all_goals
              simp only [StateT.run_bind, devRun prepared device, pure_bind] at exec
              cases due : TimerWheel.earliestDue d now <;> simp only [due] at exec
            all_goals
              try
                rename_i bucket
                by_cases overdue : timeAfter (recordWord64 bytes 0) bucket = true
                all_goals first
                  | (rw [ite_eq_left overdue] at exec; cases exec)
                  | rw [ite_eq_right overdue] at exec
            all_goals
              cases step : entry.timerPassStep <;> simp only [step] at exec
            all_goals
              try
                rename_i point
                by_cases passed : (!timeAfter (recordWord64 bytes 0) point) = true
                all_goals first
                  | (rw [ite_eq_left passed] at exec; cases exec)
                  | rw [ite_eq_right passed] at exec
            all_goals
              simp only [StateT.run_bind, StateT.run_modify, pure_bind] at exec
              refine ⟨recordWord64 bytes 0, ?_⟩
              exact placeOnWheel_effect pid timer expires (recordWord64 bytes 0) (some unit)
                {prepared with timerClk := some (recordWord64 bytes 0)} p
                (by simpa [peerAt, prepared, recordedArmPrefixState] using resident)
                _ middle () final after rfl exec

    have ambientRead : ((getAmbient : WG.M Ambient).run entry).run ambient =
        .ok ((ambient, entry), ambient) := rfl
    have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run entry).run ambient =
        ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) =>
          Except.ok ((bytes, entry), next)) := rfl
    simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
    rw [ambientRead] at run
    simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
    rw [nativeBind, hiddenRead] at run
    cases read : (AmbientM.hidden .modTimerArm).run ambient with
    | error err =>
      rw [read] at run
      cases run
    | ok out =>
      obtain ⟨bytes, middle⟩ := out
      rw [read] at run
      dsimp only [bind, Except.bind] at run
      by_cases expiry : (caller + delay.toUInt64 != recordWord64 bytes 1) = true
      · rw [ite_eq_left expiry] at run
        cases run
      · rw [ite_eq_right expiry] at run
        have expiryEq : caller + delay.toUInt64 = recordWord64 bytes 1 := by simpa using expiry
        by_cases behind : (recordWord64 bytes 0 - caller).toInt64 < 0
        · rw [ite_eq_left behind] at run
          cases run
        · rw [ite_eq_right behind] at run
          by_cases stalled : (recordWord64 bytes 0 - caller).toInt64 > 1
          · rw [ite_eq_left stalled] at run
            cases run
          · rw [ite_eq_right stalled] at run
            have changed' : (p.timer timer == some (recordWord64 bytes 1)) = false := by
              apply beq_eq_false_iff_ne.mpr
              rw [← expiryEq]
              exact changed
            have finish (g : WGWorld) (a : Ambient)
                (state : g = recordedArmPrefixState entry pid timer (recordWord64 bytes 0) (recordWord bytes 2))
                (exec : ((suffix (recordWord64 bytes 0) (recordWord64 bytes 1) (recordWord bytes 2)).run g).run a =
                  .ok (((), final), after)) :
                ∃ now unit clk, 0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
                  final = wheelPlacementState
                    {recordedArmPrefixState entry pid timer now unit with timerClk := some clk}
                    pid p timer (caller + delay.toUInt64) clk := by
              subst g
              obtain ⟨clk, exactState⟩ := suffixEffect _ _ _ a exec
              exact ⟨_, _, clk, Int64.not_lt.mp behind, Int64.not_lt.mp stalled, by
                simpa only [expiryEq] using exactState⟩
            rw [nativeBind, modifyRun] at run
            dsimp only [bind, Except.bind] at run
            cases named : (recordWord bytes 2 != 0) with
            | false =>
              rw [ite_eq_right (by rw [named]; decide)] at run
              rw [nativeBind, peerRead
                {entry with jiffiesLast := some (recordWord64 bytes 0)} middle device] at run
              dsimp only [bind, Except.bind] at run
              simp only [changed', Bool.false_eq_true, ite_false] at run
              exact finish _ middle (by simp [recordedArmPrefixState, named]) run
            | true =>
              rw [ite_eq_left named] at run
              rw [nativeBind, modifyRun] at run
              dsimp only [bind, Except.bind] at run
              rw [nativeBind, peerRead
                {entry with
                  jiffiesLast := some (recordWord64 bytes 0)
                  timerUnits := (recordWord bytes 2, pid, timer) ::
                    entry.timerUnits.filter (·.1 != recordWord bytes 2)} middle device] at run
              dsimp only [bind, Except.bind] at run
              simp only [changed', Bool.false_eq_true, ite_false] at run
              exact finish _ middle (by simp [recordedArmPrefixState, named]) run

end Leanux.Proofs.WG.TimerDiscipline
