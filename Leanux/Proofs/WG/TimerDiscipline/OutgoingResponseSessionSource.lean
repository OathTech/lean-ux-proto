import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionModel
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionSource
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- The outgoing sender uses its own original decision site. The caller clock
is inspected at the actual hook entry, before the original running/live guard. -/
def outgoingSessionPrefix (pid : PeerId) : M ResponseSessionCut := do
  let beforeSession ← Campaign2.read
  let begun ← beginSession pid
  let afterSession ← Campaign2.read
  let reached ← branch .respSessionBegun begun
  let beforeArm ← Campaign2.read
  let arm ← if reached then do
      let value ← observed (timersSessionDerived pid) (callerJiffies .timerJiffiesSessionDerived)
      let afterArm ← Campaign2.read
      pure (some ⟨value.1, afterArm⟩)
    else pure none
  return ⟨beforeSession, begun, afterSession, beforeArm, arm⟩

/-- The original remainder after the zero-key-material hook, including both
other timer hooks, the second sender clock/write and the actual socket send. -/
def outgoingResponseSessionFinish (pid : PeerId) (msg : List UInt8) (begun : Bool) : M Unit := do
  if begun then
    timersTraversal pid
    timersAnyAuthenticatedPacketSent pid
    let now ← hiddenClock64 .respLastSentAgain
    setPeer pid { (← getPeer pid) with lastSentHandshake := now }
    sendBufferToPeer pid msg

def outgoingResponseSessionPrefix (pid : PeerId) : M (Option OutgoingResponseSessionCall) := do
  let now ← hiddenClock64 .respLastSent
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  let created ← createResponse pid
  if ← branch .respCreated created.isSome then
    let some msg := created | invariant "unreachable"
    let msg ← addMacToPacket pid msg
    let session ← outgoingSessionPrefix pid
    return some ⟨msg, session⟩
  return none

def outgoingResponseSessionSuffix (pid : PeerId) : Option OutgoingResponseSessionCall → M Unit
  | none => pure ()
  | some cut => outgoingResponseSessionFinish pid cut.message cut.session.begun

theorem outgoingSessionPrefix_source (pid : PeerId) (msg : List UInt8) :
    (do let cut ← outgoingSessionPrefix pid; outgoingResponseSessionFinish pid msg cut.begun) =
      (do if ← branch .respSessionBegun (← beginSession pid) then
            timersSessionDerived pid
            timersTraversal pid
            timersAnyAuthenticatedPacketSent pid
            let now ← hiddenClock64 .respLastSentAgain
            setPeer pid { (← getPeer pid) with lastSentHandshake := now }
            sendBufferToPeer pid msg) := by
  have read_drop {α : Type} (a : M α) : (do let _ ← Campaign2.read; a) = a := rfl
  have inspect_drop {α β : Type} (a : M α) (probe : M β) :
      (do let _ ← inspect probe; a) = a := rfl
  simp only [outgoingSessionPrefix, observed, bind_assoc, pure_bind, bind_if,
    read_drop, inspect_drop]
  funext entry
  change ((beginSession pid).run entry >>= _) = ((beginSession pid).run entry >>= _)
  cases hs : (beginSession pid).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨begun, after⟩
    cases begun <;> rfl

/-- The optional cut selects the actual original suffix, including all errors. -/
theorem outgoingResponseSession_source (pid : PeerId) :
    (outgoingResponseSessionPrefix pid >>= outgoingResponseSessionSuffix pid) =
      sendHandshakeResponse pid := by
  simp only [outgoingResponseSessionPrefix, sendHandshakeResponse, bind_assoc,
    bind_if, pure_bind, bind_option, invariant_bind, outgoingResponseSessionSuffix]
  congr 1
  funext now
  congr 1
  funext peer
  congr 1
  funext ignored
  congr 1
  funext created
  congr 1
  funext accepted
  cases accepted <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_assoc,
    pure_bind, bind_option, invariant_bind]
  cases created with
  | none => rfl
  | some msg =>
    simp only [bind_assoc, pure_bind, outgoingResponseSessionSuffix]
    congr 1
    funext message
    exact outgoingSessionPrefix_source pid message

def observedOutgoingResponseSession (pid : PeerId) :
    M (Outcome (Option OutgoingResponseSessionCall)) := do
  let observation ← inspect (outgoingResponseSessionPrefix pid)
  sendHandshakeResponse pid
  return observation

def outgoingResponseSessionTranscript (pid : PeerId) :
    M (Outcome (Option OutgoingResponseSessionCall)) := do
  let candidate ← outgoingResponseSessionPrefix pid
  let afterPrefix ← Campaign2.read
  outgoingResponseSessionSuffix pid candidate
  return .ok (candidate, afterPrefix)

theorem observedOutgoingResponseSession_erase (pid : PeerId) :
    (do let _ ← observedOutgoingResponseSession pid; pure ()) = sendHandshakeResponse pid := by
  funext entry
  change (((sendHandshakeResponse pid).run entry >>= fun out =>
    Except.ok (observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2))
      >>= fun out => Except.ok ((), out.2)) = (sendHandshakeResponse pid).run entry
  cases run : (sendHandshakeResponse pid).run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨returned, final⟩; cases returned; rfl

/-- The observation comes from the same prefix that selects the actual suffix. -/
theorem observedOutgoingResponseSession_source (pid : PeerId) :
    observedOutgoingResponseSession pid = outgoingResponseSessionTranscript pid := by
  funext entry
  change ((sendHandshakeResponse pid).run entry >>= fun out =>
    Except.ok (observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) = _
  rw [← outgoingResponseSession_source pid]
  change (((outgoingResponseSessionPrefix pid).run entry >>= fun cut =>
    (outgoingResponseSessionSuffix pid cut.1).run cut.2) >>= fun out =>
      Except.ok (observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) =
    ((outgoingResponseSessionPrefix pid).run entry >>= fun cut =>
      (outgoingResponseSessionSuffix pid cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, snapshot cut.2), out.2))
  cases hp : (outgoingResponseSessionPrefix pid).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (outgoingResponseSessionSuffix pid candidate).run atCut <;> rfl

theorem outgoingSessionPrefix_facts (pid : PeerId) :
    Noise.Ensures (outgoingSessionPrefix pid) (fun _ => True)
      (fun cut final => ResponseSessionFacts pid cut ∧ responseSessionEnd cut = snapshot final) := by
  intro entry cut final pre run
  change ((beginSession pid).run entry >>= _) = _ at run
  cases sessionRun : (beginSession pid).run entry with
  | error err => rw [sessionRun] at run; cases run
  | ok found =>
    rcases found with ⟨begun, afterSession⟩
    obtain ⟨d, p, device, resident⟩ := beginSession_entry_resident pid entry afterSession begun sessionRun
    obtain ⟨next, nextDevice, effect⟩ := beginSession_effect pid d p entry.k.keypairCounter resident
      entry begun afterSession ⟨device, rfl⟩ sessionRun
    rw [sessionRun] at run
    cases begun with
    | false =>
      change Except.ok (_, _) = Except.ok (cut, final) at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
      refine ⟨?_, rfl⟩
      refine ⟨d, p, next, device, resident, nextDevice, effect, nextDevice, rfl, rfl, ?_⟩
      intro arm missing
      cases missing
    | true =>
      let before : World := { afterSession with steps := afterSession.steps.push { decision := .respSessionBegun, outcome := true, netRx := afterSession.netRxSection } }
      change ((observed (timersSessionDerived pid) (callerJiffies .timerJiffiesSessionDerived)).run before
        >>= fun out => Except.ok
          (⟨snapshot entry, true, snapshot afterSession, snapshot before,
            some ⟨out.1.1, snapshot out.2⟩⟩, out.2)) = .ok (cut, final) at run
      cases armRun : (observed (timersSessionDerived pid)
          (callerJiffies .timerJiffiesSessionDerived)).run before with
      | error err => rw [armRun] at run; cases run
      | ok found =>
        rcases found with ⟨value, afterArm⟩
        rw [armRun] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        obtain ⟨q, qResident, alive⟩ := sessionEffect_alive pid d p _ _ next effect
        refine ⟨?_, rfl⟩
        refine ⟨d, p, next, device, resident, nextDevice, effect, nextDevice, rfl, rfl, ?_⟩
        intro arm same
        cases same
        refine ⟨?_, q, qResident, alive, ?_⟩
        · exact effect.2.2.2.1
        · intro running records
          exact projected_session_derived_recorded pid next q qResident running alive
            before value afterArm ⟨nextDevice, records⟩ armRun


end Leanux.Proofs.WG.TimerDiscipline
