import Leanux.Proofs.WG.TimerDiscipline.ArmingOffSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Metadata written before the recorded same-expiry test. -/
def recordedArmPrefixState (entry : WGWorld) (pid : PeerId) (timer : PeerTimer)
    (now : UInt64) (unit : Nat) : WGWorld :=
  {entry with jiffiesLast := some now, timerUnits :=
    if unit != 0 then (unit, pid, timer) :: entry.timerUnits.filter (·.1 != unit)
    else entry.timerUnits}

theorem armTimer_sameExpiry_effect (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (entry : WGWorld) (p : Peer)
    (resident : peerAt entry pid = some p)
    (same : p.timer timer = some (caller + delay.toUInt64))
    (ambient after : Ambient) (final : WGWorld)
    (mode : ambient.armRecords = true)
    (run : ((armTimer pid timer delay (some caller)).run entry).run ambient =
      .ok (((), final), after)) :
    ∃ now unit, 0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
      final = recordedArmPrefixState entry pid timer now unit := by
  cases device : entry.dev with
  | none => simp [peerAt, device] at resident
  | some d =>
    have hp : d.peers[pid]? = some p := by simpa [peerAt, device] using resident
    have ambientRead : ((getAmbient : WG.M Ambient).run entry).run ambient =
        .ok ((ambient, entry), ambient) := rfl
    have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run entry).run ambient =
        ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) =>
          Except.ok ((bytes, entry), next)) := rfl
    simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
    rw [ambientRead] at run
    simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
    have nativeBind {α β : Type} (a : WG.M α) (f : α → WG.M β) (g : WGWorld) (b : Ambient) :
        ((StateT.bind a f).run g).run b =
          (((a.run g).run b) >>= fun ((value, next), ambient') =>
            ((f value).run next).run ambient') := rfl
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
            have same' : p.timer timer = some (recordWord64 bytes 1) := by rw [← expiryEq]; exact same
            have modifyRun (f : WGWorld → WGWorld) (g : WGWorld) (a : Ambient) :
                ((modify f : WG.M PUnit).run g).run a = .ok ((⟨⟩, f g), a) := rfl
            have peerRead (g : WGWorld) (a : Ambient) (hd : g.dev = some d) :
                ((getPeer pid).run g).run a = .ok ((p, g), a) := by
              simp [getPeer, getDev, hd, hp]
              rfl
            refine ⟨recordWord64 bytes 0, recordWord bytes 2,
              Int64.not_lt.mp behind, Int64.not_lt.mp stalled, ?_⟩
            rw [nativeBind, modifyRun] at run
            dsimp only [bind, Except.bind] at run
            cases named : (recordWord bytes 2 != 0) with
            | false =>
              simp only [named, Bool.false_eq_true, ite_false] at run
              rw [nativeBind, peerRead
                {entry with jiffiesLast := some (recordWord64 bytes 0)} middle device] at run
              dsimp only [bind, Except.bind] at run
              simp only [same', BEq.rfl, ite_true] at run
              cases run
              simp [recordedArmPrefixState, named]
            | true =>
              simp only [named, ite_true] at run
              rw [nativeBind, modifyRun] at run
              dsimp only [bind, Except.bind] at run
              rw [nativeBind, peerRead
                {entry with
                  jiffiesLast := some (recordWord64 bytes 0)
                  timerUnits := (recordWord bytes 2, pid, timer) ::
                    entry.timerUnits.filter (·.1 != recordWord bytes 2)} middle device] at run
              dsimp only [bind, Except.bind] at run
              simp only [same', BEq.rfl, ite_true] at run
              cases run
              simp [recordedArmPrefixState, named]

end Leanux.Proofs.WG.TimerDiscipline
