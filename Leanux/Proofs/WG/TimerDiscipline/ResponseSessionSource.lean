import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionModel
import Leanux.Proofs.WG.TimerDiscipline.ObservationClaims
import Leanux.Proofs.WG.Roaming.ResponseCallClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming

/-- Exact original continuation after the session-derived timer hook. -/
def responseSessionFinish (msg : List UInt8) (pid : PeerId) (begun : Bool) : M Unit := do
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
def responseSessionPrefix (pid : PeerId) : M ResponseSessionCut := do
  let beforeSession ← Campaign2.read
  let begun ← beginSession pid
  let afterSession ← Campaign2.read
  let reached ← branch .hsRespSessionBegun begun
  let beforeArm ← Campaign2.read
  let arm ← if reached then do
      let value ← observed (timersSessionDerived pid) (callerJiffies .timerJiffiesSessionDerived)
      let afterArm ← Campaign2.read
      pure (some ⟨value.1, afterArm⟩)
    else pure none
  return ⟨beforeSession, begun, afterSession, beforeArm, arm⟩

theorem responseSessionPrefix_source (msg : List UInt8) (pid : PeerId) :
    (do let cut ← responseSessionPrefix pid; responseSessionFinish msg pid cut.begun) =
      responseAfterSetter msg pid := by
  have read_drop {α : Type} (a : M α) : (do let _ ← Campaign2.read; a) = a := rfl
  have inspect_drop {α β : Type} (a : M α) (probe : M β) :
      (do let _ ← inspect probe; a) = a := rfl
  simp only [responseSessionPrefix, observed, bind_assoc, pure_bind, bind_if,
    read_drop, inspect_drop]
  funext entry
  unfold responseAfterSetter
  simp only [bind_assoc]
  change ((beginSession pid).run entry >>= _) = ((beginSession pid).run entry >>= _)
  cases hs : (beginSession pid).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨begun, after⟩
    cases begun <;> rfl


def responseSessionCallPrefix (msg : List UInt8) (src : SkbSource) : M (Option ResponseSessionCall) := do
  let candidate ← responseCallPrefix msg src
  match candidate with
  | none => return none
  | some cut =>
    setPeerEndpointFromSkb cut.consumed.input.pid src
    let session ← responseSessionPrefix cut.consumed.input.pid
    return some ⟨cut, session⟩

def responseSessionCallSuffix (msg : List UInt8) : Option ResponseSessionCall → M Unit
  | none => pure ()
  | some cut => responseSessionFinish msg cut.response.consumed.input.pid cut.session.begun

theorem responseSessionCall_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responseSessionCallPrefix msg src >>= responseSessionCallSuffix msg) =
      receiveHandshakePacket msg src := by
  rw [← receiveHandshakePacket_response msg src kind]
  simp only [responseSessionCallPrefix, bind_assoc]
  congr 1
  funext candidate
  cases candidate with
  | none => rfl
  | some cut =>
    simp only [bind_assoc, pure_bind, responseSessionCallSuffix, responseCallSuffix]
    rw [responseSessionPrefix_source]

def observedResponseSession (msg : List UInt8) (src : SkbSource) :
    M (Outcome (Option ResponseSessionCall)) := do
  let observation ← inspect (responseSessionCallPrefix msg src)
  receiveHandshakePacket msg src
  return observation

def responseSessionTranscript (msg : List UInt8) (src : SkbSource) :
    M (Outcome (Option ResponseSessionCall)) := do
  let candidate ← responseSessionCallPrefix msg src
  let afterPrefix ← Campaign2.read
  responseSessionCallSuffix msg candidate
  return .ok (candidate, afterPrefix)

theorem observedResponseSession_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseSession msg src; pure ()) = receiveHandshakePacket msg src := by
  funext entry
  change (((receiveHandshakePacket msg src).run entry >>= fun out =>
    Except.ok (observeResult ((responseSessionCallPrefix msg src).run entry), out.2))
      >>= fun out => Except.ok ((), out.2)) = (receiveHandshakePacket msg src).run entry
  cases run : (receiveHandshakePacket msg src).run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨returned, final⟩; cases returned; rfl

/-- Completeness ties the observation to the prefix selecting the actual suffix;
an arbitrary constant-none observer would not satisfy this equation. -/
theorem observedResponseSession_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    observedResponseSession msg src = responseSessionTranscript msg src := by
  funext entry
  change ((receiveHandshakePacket msg src).run entry >>= fun out =>
    Except.ok (observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) = _
  rw [← responseSessionCall_source msg src kind]
  change (((responseSessionCallPrefix msg src).run entry >>= fun cut =>
    (responseSessionCallSuffix msg cut.1).run cut.2) >>= fun out =>
      Except.ok (observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) =
    ((responseSessionCallPrefix msg src).run entry >>= fun cut =>
      (responseSessionCallSuffix msg cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, snapshot cut.2), out.2))
  cases hp : (responseSessionCallPrefix msg src).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (responseSessionCallSuffix msg candidate).run atCut <;> rfl

/-- A normal original session execution supplies its entry getter's resident
peer; callers need not assume an input execution or residency witness. -/
theorem beginSession_entry_resident (pid : PeerId) (entry final : World) (begun : Bool)
    (run : (beginSession pid).run entry = .ok (begun, final)) :
    ∃ d p, entry.k.wg = some d ∧ d.peers[pid]? = some p := by
  cases device : entry.k.wg with
  | none =>
    have stop : (getPeer pid).run entry =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getPeer, getDev, getK, invariant, device, StateT.run_bind]
      rfl
    change ((getPeer pid).run entry >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      have stop : (getPeer pid).run entry = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, getK, invariant, device, peer, StateT.run_bind]
        rfl
      change ((getPeer pid).run entry >>= _) = _ at run
      rw [stop] at run
      cases run
    | some p => exact ⟨d, p, rfl, peer⟩

theorem responseSessionPrefix_facts (pid : PeerId) :
    Noise.Ensures (responseSessionPrefix pid) (fun _ => True)
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
      let before : World := { afterSession with steps := afterSession.steps.push { decision := .hsRespSessionBegun, outcome := true, netRx := afterSession.netRxSection } }
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
