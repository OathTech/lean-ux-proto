import Leanux.Proofs.WG.TimerDiscipline.RecordedJitter

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The actual initiation-send prefix, retaining early exits and all branch logs.
True means control reaches the final retransmit arm hook; it does not assert
successful network transmission, whose return the original caller ignores. -/
def initiationArmPrefix (pid : PeerId) : M Bool := do
  if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then return false
  let now ← hiddenClock64 .initLastSent
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  let created ← createInitiation pid
  if ← branch .initCreated created.isSome then
    let some msg := created | invariant "unreachable"
    let msg ← addMacToPacket pid msg
    timersTraversal pid
    timersAnyAuthenticatedPacketSent pid
    let now ← hiddenClock64 .initLastSentAgain
    setPeer pid { (← getPeer pid) with lastSentHandshake := now }
    sendBufferToPeer pid msg
    return true
  return false

theorem sendInitiation_arm_source (pid : PeerId) :
    sendHandshakeInitiation pid = (do
      if ← initiationArmPrefix pid then timersHandshakeInitiated pid) := by
  simp only [sendHandshakeInitiation, initiationArmPrefix, bind_assoc, pure_bind]
  congr 1
  funext p
  congr 1
  funext limited
  cases limited <;> simp only [Bool.false_eq_true,  ite_false, ite_true, pure_bind, bind_assoc]
  congr 1
  funext now
  congr 1
  funext p
  congr 1
  funext u
  congr 1
  funext created
  congr 1
  funext made
  cases made <;> simp only [Bool.false_eq_true,  ite_false, ite_true, pure_bind, bind_assoc]
  cases created with
  | none => rfl
  | some msg =>
    simp only [bind_assoc, pure_bind, ite_true]

theorem sendInitiation_arm_execution (pid : PeerId) (initial final : World)
    (run : (sendHandshakeInitiation pid).run initial = .ok ((), final)) :
    ∃ reached beforeArm,
      (initiationArmPrefix pid).run initial = .ok (reached, beforeArm) ∧
      if reached then (timersHandshakeInitiated pid).run beforeArm = .ok ((), final)
      else final = beforeArm := by
  rw [sendInitiation_arm_source, StateT.run_bind] at run
  cases hp : (initiationArmPrefix pid).run initial with
  | error err => rw [hp] at run; cases run
  | ok pair =>
    obtain ⟨reached, beforeArm⟩ := pair
    rw [hp] at run
    refine ⟨reached, beforeArm, rfl, ?_⟩
    cases reached
    · change Except.ok ((), beforeArm) = Except.ok ((), final) at run
      exact (congrArg Prod.snd (Except.ok.inj run)).symm
    · exact run

theorem sendInitiation_arm_skipped (pid : PeerId) (initial afterPrefix : World)
    (hprefix : (initiationArmPrefix pid).run initial = .ok (false, afterPrefix)) :
    (sendHandshakeInitiation pid).run initial = .ok ((), afterPrefix) := by
  rw [sendInitiation_arm_source, StateT.run_bind, hprefix]
  rfl

theorem sendInitiation_arm_reached (pid : PeerId) (initial afterPrefix : World)
    (hprefix : (initiationArmPrefix pid).run initial = .ok (true, afterPrefix)) :
    (sendHandshakeInitiation pid).run initial = (timersHandshakeInitiated pid).run afterPrefix := by
  rw [sendInitiation_arm_source, StateT.run_bind, hprefix]
  rfl

theorem sendInitiation_arm_recorded (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial afterPrefix final : World)
    (hprefix : (initiationArmPrefix pid).run initial = .ok (true, afterPrefix))
    (device : afterPrefix.k.wg = some d) (records : afterPrefix.armRecords = true)
    (run : (sendHandshakeInitiation pid).run initial = .ok ((), final)) :
    ∃ caller afterRead jitter afterJitter,
      (callerJiffies .timerJiffiesHandshakeInitiated).run afterPrefix = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout .retransmitJitter).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer .retransmitHandshake
        (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  rw [sendInitiation_arm_reached pid initial afterPrefix hprefix, handshakeInitiated_source] at run
  exact jitteredArm_recorded_clock .timerJiffiesHandshakeInitiated .retransmitJitter pid
    .retransmitHandshake REKEY_TIMEOUT_TICKS d p resident running alive
    afterPrefix final device records run

end Leanux.Proofs.WG.TimerDiscipline
