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
def outgoingSessionPrefix (pid : PeerId) : Leanux.M ResponseSessionCut := do
  let beforeSession ← Campaign2.Product.read
  let begun ← liftWG (beginSession pid)
  let afterSession ← Campaign2.Product.read
  let reached ← branch .respSessionBegun begun
  let beforeArm ← Campaign2.Product.read
  let arm ← if reached then do
      let value ← observed (liftWG (timersSessionDerived pid)) (liftWG (callerJiffies .timerJiffiesSessionDerived))
      let afterArm ← Campaign2.Product.read
      pure (some ⟨value.1, afterArm⟩)
    else pure none
  return ⟨beforeSession, begun, afterSession, beforeArm, arm⟩

/-- The original remainder after the zero-key-material hook, including both
other timer hooks, the second sender clock/write and the actual socket send. -/
def outgoingResponseSessionFinish (pid : PeerId) (msg : List UInt8) (begun : Bool) : WG.M Unit := do
  if begun then
    timersTraversal pid
    timersAnyAuthenticatedPacketSent pid
    let now ← hiddenClock64 .respLastSentAgain
    setPeer pid { (← getPeer pid) with lastSentHandshake := now }
    sendBufferToPeer pid msg

def outgoingResponseSessionPrefix (pid : PeerId) : Leanux.M (Option OutgoingResponseSessionCall) := do
  let now ← liftWG (hiddenClock64 .respLastSent)
  liftWG (setPeer pid { (← liftWG (getPeer pid)) with lastSentHandshake := now })
  let created ← liftWG (createResponse pid)
  if ← (branch .respCreated created.isSome : Leanux.M Bool) then
    let some msg := created | invariant "unreachable"
    let msg ← liftWG (addMacToPacket pid msg)
    let session ← outgoingSessionPrefix pid
    return some ⟨msg, session⟩
  return none

def outgoingResponseSessionSuffix (pid : PeerId) : Option OutgoingResponseSessionCall → Leanux.M Unit
  | none => pure ()
  | some cut => liftWG (outgoingResponseSessionFinish pid cut.message cut.session.begun)

theorem outgoingSessionPrefix_source (pid : PeerId) (msg : List UInt8) :
    (do let cut ← outgoingSessionPrefix pid; liftWG (outgoingResponseSessionFinish pid msg cut.begun)) =
      liftWG (do if ← branch .respSessionBegun (← beginSession pid) then
            timersSessionDerived pid
            timersTraversal pid
            timersAnyAuthenticatedPacketSent pid
            let now ← hiddenClock64 .respLastSentAgain
            setPeer pid { (← getPeer pid) with lastSentHandshake := now }
            sendBufferToPeer pid msg) := by
  have read_drop {α : Type} (a : Leanux.M α) : (do let _ ← Campaign2.Product.read; a) = a := rfl
  have inspect_drop {α β : Type} (a : Leanux.M α) (probe : Leanux.M β) :
      (do let _ ← Campaign2.Product.inspect probe; a) = a := rfl
  have lift_pure {α : Type} (value : α) : liftWG (pure value) = (pure value : Leanux.M α) := rfl
  have lift_branch (decision : Decision) (value : Bool) :
      liftWG (branch decision value : WG.M Bool) = (branch decision value : Leanux.M Bool) := rfl
  simp only [outgoingSessionPrefix, observed, bind_assoc, pure_bind, bind_if,
    read_drop, inspect_drop]
  funext entry
  simp only [liftWG_bind_variant, lift_branch]
  change ((liftWG (beginSession pid)).run entry >>= _) = ((liftWG (beginSession pid)).run entry >>= _)
  cases hs : (liftWG (beginSession pid)).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨begun, after⟩
    cases begun with
    | false => rfl
    | true =>
      let current := {after with ambient := {after.ambient with steps := after.ambient.steps.push {
        decision := .respSessionBegun, outcome := true, netRx := after.ambient.netRxSection}}}
      change ((liftWG (timersSessionDerived pid) >>= fun _ =>
        liftWG (outgoingResponseSessionFinish pid msg true)).run current) =
        (liftWG (do timersSessionDerived pid; outgoingResponseSessionFinish pid msg true)).run current
      rw [liftWG_bind_variant]


/-- The optional cut selects the actual original suffix, including all errors. -/
theorem outgoingResponseSession_source (pid : PeerId) :
    (outgoingResponseSessionPrefix pid >>= outgoingResponseSessionSuffix pid) =
      liftWG (sendHandshakeResponse pid) := by
  have lift_branch (decision : Decision) (value : Bool) :
      liftWG (branch decision value : WG.M Bool) = (branch decision value : Leanux.M Bool) := rfl
  simp only [outgoingResponseSessionPrefix, sendHandshakeResponse, liftWG_bind_variant, lift_branch, bind_assoc,
    bind_if, pure_bind, invariant_bind, outgoingResponseSessionSuffix]
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
  cases accepted with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases created with
    | none => rfl
    | some msg =>
      simp only [liftWG_bind_variant, bind_assoc, pure_bind, outgoingResponseSessionSuffix]
      congr 1
      funext message
      simpa only [liftWG_bind_variant] using outgoingSessionPrefix_source pid message

def observedOutgoingResponseSession (pid : PeerId) :
    Leanux.M (Campaign2.Product.Outcome (Option OutgoingResponseSessionCall)) := do
  let observation ← Campaign2.Product.inspect (outgoingResponseSessionPrefix pid)
  liftWG (sendHandshakeResponse pid)
  return observation

def outgoingResponseSessionTranscript (pid : PeerId) :
    Leanux.M (Campaign2.Product.Outcome (Option OutgoingResponseSessionCall)) := do
  let candidate ← outgoingResponseSessionPrefix pid
  let afterPrefix ← Campaign2.Product.read
  outgoingResponseSessionSuffix pid candidate
  return .ok (candidate, afterPrefix)

theorem observedOutgoingResponseSession_erase (pid : PeerId) :
    (do let _ ← observedOutgoingResponseSession pid; pure ()) = liftWG (sendHandshakeResponse pid) := by
  funext entry
  change (((liftWG (sendHandshakeResponse pid)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2))
      >>= fun out => Except.ok ((), out.2)) = (liftWG (sendHandshakeResponse pid)).run entry
  cases run : (liftWG (sendHandshakeResponse pid)).run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨returned, final⟩; cases returned; rfl

/-- The observation comes from the same prefix that selects the actual suffix. -/
theorem observedOutgoingResponseSession_source (pid : PeerId) :
    observedOutgoingResponseSession pid = outgoingResponseSessionTranscript pid := by
  funext entry
  change ((liftWG (sendHandshakeResponse pid)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) = _
  rw [← outgoingResponseSession_source pid]
  change (((outgoingResponseSessionPrefix pid).run entry >>= fun cut =>
    (outgoingResponseSessionSuffix pid cut.1).run cut.2) >>= fun out =>
      Except.ok (Campaign2.Product.observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) =
    ((outgoingResponseSessionPrefix pid).run entry >>= fun cut =>
      (outgoingResponseSessionSuffix pid cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.Product.snapshot cut.2), out.2))
  cases hp : (outgoingResponseSessionPrefix pid).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (outgoingResponseSessionSuffix pid candidate).run atCut <;> rfl

theorem outgoingSessionPrefix_facts (pid : PeerId) :
    Noise.Product.Ensures (outgoingSessionPrefix pid) (fun _ => True)
      (fun cut final => ResponseSessionFacts pid cut ∧ responseSessionEnd cut = Campaign2.Product.snapshot final) := by
  intro entry cut final pre run
  change ((liftWG (beginSession pid)).run entry >>= _) = _ at run
  cases sessionRun : (liftWG (beginSession pid)).run entry with
  | error err => rw [sessionRun] at run; cases run
  | ok found =>
    rcases found with ⟨begun, afterSession⟩
    obtain ⟨d, p, device, resident⟩ := beginSession_entry_resident pid entry afterSession begun sessionRun
    have native : ((beginSession pid).run entry.wg).run entry.ambient =
        .ok ((begun, afterSession.wg), afterSession.ambient) := by
      change (((beginSession pid).run entry.wg).run entry.ambient >>= fun ((value, current), inputs) =>
        Except.ok (value, {entry with wg := current, ambient := inputs})) = .ok (begun, afterSession) at sessionRun
      cases actual : ((beginSession pid).run entry.wg).run entry.ambient with
      | error stop => rw [actual] at sessionRun; cases sessionRun
      | ok pair =>
        obtain ⟨⟨value, current⟩, inputs⟩ := pair
        rw [actual] at sessionRun
        cases sessionRun
        rfl
    obtain ⟨next, nextDevice, effect⟩ := beginSession_effect pid d p entry.wg.keypairCounter resident
      entry.wg entry.ambient begun afterSession.wg afterSession.ambient ⟨device, rfl⟩ native
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
      let before : World := { afterSession with ambient := {afterSession.ambient with steps := afterSession.ambient.steps.push {decision := .respSessionBegun, outcome := true, netRx := afterSession.ambient.netRxSection}} }
      change ((observed (liftWG (timersSessionDerived pid)) (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before
        >>= fun out => Except.ok
          (⟨Campaign2.Product.snapshot entry, true, Campaign2.Product.snapshot afterSession, Campaign2.Product.snapshot before,
            some ⟨out.1.1, Campaign2.Product.snapshot out.2⟩⟩, out.2)) = .ok (cut, final) at run
      cases armRun : (observed (liftWG (timersSessionDerived pid))
          (liftWG (callerJiffies .timerJiffiesSessionDerived))).run before with
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
            (Campaign2.Product.snapshot before) before value afterArm ⟨rfl, nextDevice, records⟩ armRun


end Leanux.Proofs.WG.TimerDiscipline
