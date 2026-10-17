import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.HookObservationClaims
import Leanux.Proofs.WG.Roaming.ResponseCallProductClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- Exact original continuation after the session-derived timer hook. -/
def responseSessionFinish (msg : List UInt8) (pid : PeerId) (begun : Bool) : WG.M Unit := do
  if begun then
    timersHandshakeComplete pid
    sendKeepalive pid
  let peer := some pid
  if ← branch .hsWrongPacket peer.isNone then
    invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

/-- The clock is inspected at the real hook entry; the original hook executes
from that same state. Its caller read precedes the original running/live guard. -/
def responseSessionPrefix (pid : PeerId) : Leanux.M ResponseSessionCut := do
  let beforeSession ← Campaign2.Product.read
  let begun ← liftWG (beginSession pid)
  let afterSession ← Campaign2.Product.read
  let reached ← branch .hsRespSessionBegun begun
  let beforeArm ← Campaign2.Product.read
  let arm ← if reached then do
      let value ← observed (liftWG (timersSessionDerived pid)) (liftWG (callerJiffies .timerJiffiesSessionDerived))
      let afterArm ← Campaign2.Product.read
      pure (some ⟨value.1, afterArm⟩)
    else pure none
  return ⟨beforeSession, begun, afterSession, beforeArm, arm⟩

theorem responseSessionPrefix_source (msg : List UInt8) (pid : PeerId) :
    (do let cut ← responseSessionPrefix pid; liftWG (responseSessionFinish msg pid cut.begun)) =
      liftWG (Roaming.responseAfterSetter msg pid) := by
  have read_drop {α : Type} (a : Leanux.M α) : (do let _ ← Campaign2.Product.read; a) = a := rfl
  have inspect_drop {α β : Type} (a : Leanux.M α) (probe : Leanux.M β) :
      (do let _ ← Campaign2.Product.inspect probe; a) = a := rfl
  have lift_pure {α : Type} (value : α) : liftWG (pure value) = (pure value : Leanux.M α) := rfl
  have lift_branch (decision : Decision) (value : Bool) :
      liftWG (branch decision value : WG.M Bool) = (branch decision value : Leanux.M Bool) := rfl
  simp only [responseSessionPrefix, observed, bind_assoc, pure_bind, bind_if,
    read_drop, inspect_drop]
  funext entry
  unfold Roaming.responseAfterSetter
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
        decision := .hsRespSessionBegun, outcome := true, netRx := after.ambient.netRxSection}}}
      change ((liftWG (timersSessionDerived pid) >>= fun _ =>
        liftWG (responseSessionFinish msg pid true)).run current) =
        (liftWG (do timersSessionDerived pid; responseSessionFinish msg pid true)).run current
      rw [liftWG_bind_variant]


def responseSessionCallPrefix (msg : List UInt8) (src : SkbSource) : Leanux.M (Option ResponseSessionCall) := do
  let candidate ← Roaming.Product.responseCallPrefix msg src
  match candidate with
  | none => return none
  | some cut =>
    liftWG (setPeerEndpointFromSkb cut.consumed.input.pid src)
    let session ← responseSessionPrefix cut.consumed.input.pid
    return some ⟨cut, session⟩

def responseSessionCallSuffix (msg : List UInt8) : Option ResponseSessionCall → Leanux.M Unit
  | none => pure ()
  | some cut => liftWG (responseSessionFinish msg cut.response.consumed.input.pid cut.session.begun)

theorem responseSessionCall_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responseSessionCallPrefix msg src >>= responseSessionCallSuffix msg) =
      liftWG (receiveHandshakePacket msg src) := by
  rw [← Roaming.Product.receiveHandshakePacket_response msg src kind]
  simp only [responseSessionCallPrefix, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [bind_assoc, pure_bind, responseSessionCallSuffix, Roaming.Product.responseCallSuffix, liftWG_bind_variant]
    rw [responseSessionPrefix_source]

def observedResponseSession (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Product.Outcome (Option ResponseSessionCall)) := do
  let observation ← Campaign2.Product.inspect (responseSessionCallPrefix msg src)
  liftWG (receiveHandshakePacket msg src)
  return observation

def responseSessionTranscript (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Product.Outcome (Option ResponseSessionCall)) := do
  let candidate ← responseSessionCallPrefix msg src
  let afterPrefix ← Campaign2.Product.read
  responseSessionCallSuffix msg candidate
  return .ok (candidate, afterPrefix)

theorem observedResponseSession_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseSession msg src; pure ()) = liftWG (receiveHandshakePacket msg src) := by
  funext entry
  change (((liftWG (receiveHandshakePacket msg src)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((responseSessionCallPrefix msg src).run entry), out.2))
      >>= fun out => Except.ok ((), out.2)) = (liftWG (receiveHandshakePacket msg src)).run entry
  cases run : (liftWG (receiveHandshakePacket msg src)).run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨returned, final⟩; cases returned; rfl

/-- Completeness ties the observation to the prefix selecting the actual suffix;
an arbitrary constant-none observer would not satisfy this equation. -/
theorem observedResponseSession_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    observedResponseSession msg src = responseSessionTranscript msg src := by
  funext entry
  change ((liftWG (receiveHandshakePacket msg src)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) = _
  rw [← responseSessionCall_source msg src kind]
  change (((responseSessionCallPrefix msg src).run entry >>= fun cut =>
    (responseSessionCallSuffix msg cut.1).run cut.2) >>= fun out =>
      Except.ok (Campaign2.Product.observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) =
    ((responseSessionCallPrefix msg src).run entry >>= fun cut =>
      (responseSessionCallSuffix msg cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.Product.snapshot cut.2), out.2))
  cases hp : (responseSessionCallPrefix msg src).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (responseSessionCallSuffix msg candidate).run atCut <;> rfl

/-- A normal original session execution supplies its entry getter's resident
peer; callers need not assume an input execution or residency witness. -/
theorem beginSession_entry_resident (pid : PeerId) (entry final : World) (begun : Bool)
    (run : (liftWG (beginSession pid)).run entry = .ok (begun, final)) :
    ∃ d p, entry.wg.dev = some d ∧ d.peers[pid]? = some p := by
  cases device : entry.wg.dev with
  | none =>
    have stop : ((getPeer pid).run entry.wg).run entry.ambient =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getPeer, getDev, device]
      rfl
    change ((((getPeer pid).run entry.wg).run entry.ambient >>= _) >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      have stop : ((getPeer pid).run entry.wg).run entry.ambient =
          .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, device, peer]
        rfl
      change ((((getPeer pid).run entry.wg).run entry.ambient >>= _) >>= _) = _ at run
      rw [stop] at run
      cases run
    | some p => exact ⟨d, p, rfl, peer⟩

theorem responseSessionPrefix_facts (pid : PeerId) :
    Noise.Product.Ensures (responseSessionPrefix pid) (fun _ => True)
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
      let before : World := { afterSession with ambient := {afterSession.ambient with steps := afterSession.ambient.steps.push {decision := .hsRespSessionBegun, outcome := true, netRx := afterSession.ambient.netRxSection}} }
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
