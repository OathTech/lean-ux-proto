import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryBoundarySource
import Leanux.Proofs.WG.TimerDiscipline.SourceClaims

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

/-- A continuation contract at the actual sequence exit. No scheduler choice,
callback invocation, arm record, or successful give-up return is assumed. -/
theorem source_retry_boundary (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) (nineteen : units.length = 19)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d)
      (fun result boundary => SameRetryPeer pid result.2 →
        Campaign2.Product.AgreesOn (fun s => s = boundary)
          (liftWG (expiredRetransmitHandshake pid))
          (liftWG (do let _ ← retransmitDecision pid; retransmitGiveUp pid)) ∧
        Campaign2.Product.Ensures (liftWG (expiredRetransmitHandshake pid)) (fun s => s = boundary)
          (fun _ final => final.wg.device.map Device.sendWorkQueue = some [] ∧
            ∃ q, final.toSnapshot.peerAt pid = some q ∧ q.internalId = p.internalId ∧
              q.timerHandshakeAttempts = 19)) := by
  intro entry result finish pre run same
  have cert := source_retry_sequence d units empty entry result finish pre run
  have counts := (cert.2.2.2.2 pid p resident same).1
  have queue := cert.2.2.1
  cases device : (snapshot finish).wg.device with
  | none => simp [device] at queue
  | some next =>
    have nextEmpty : next.sendWorkQueue = [] := by simpa [device] using queue
    cases stored : next.peers[pid]? with
    | none => simp [workerObservation, Campaign2.Snapshot.peerAt, device, stored] at counts
    | some q =>
      have fields : q.internalId = p.internalId ∧ q.timerHandshakeAttempts = 19 ∧
          q.refcount = p.refcount := by
        simpa [workerObservation, Campaign2.Snapshot.peerAt, device, stored, workerView, zero, nineteen] using counts
      have limit : MAX_TIMER_HANDSHAKES < q.timerHandshakeAttempts := by
        simp [fields.2.1, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT]
      constructor
      · intro actual eqBoundary
        have actualDevice : actual.wg.dev = some next := by
          change (snapshot actual).wg.device = some next
          rw [eqBoundary]
          exact device
        obtain ⟨value, g, a, decision, isTrue, storedDevice⟩ :=
          retransmitDecision_above_limit pid next q stored limit actual.wg actual.ambient actualDevice
        subst value
        have native :
            ((expiredRetransmitHandshake pid).run actual.wg).run actual.ambient =
            ((do let _ ← retransmitDecision pid; retransmitGiveUp pid).run actual.wg).run actual.ambient := by
          rw [retransmitDecision_source]
          change (((retransmitDecision pid).run actual.wg).run actual.ambient >>= _) =
            (((retransmitDecision pid).run actual.wg).run actual.ambient >>= _)
          rw [decision]
          rfl
        change observeResult
            ((((expiredRetransmitHandshake pid).run actual.wg).run actual.ambient) >>=
              fun ((x, g), a) => Except.ok (x, {actual with wg := g, ambient := a})) =
          observeResult
            ((((do let _ ← retransmitDecision pid; retransmitGiveUp pid).run actual.wg).run actual.ambient) >>=
              fun ((x, g), a) => Except.ok (x, {actual with wg := g, ambient := a}))
        rw [native]
      · intro actual u final eqBoundary callback
        have actualDevice : actual.wg.dev = some next := by
          change (snapshot actual).wg.device = some next
          rw [eqBoundary]
          exact device
        have actualPeer : (Campaign2.snapshot actual.wg actual.ambient).peerAt pid = some q := by
          change (actual.wg.dev.bind fun d => d.peers[pid]?) = some q
          simp [actualDevice, stored]
        change ((((expiredRetransmitHandshake pid).run actual.wg).run actual.ambient) >>=
          fun ((x, g), a) => Except.ok (x, {actual with wg := g, ambient := a})) = .ok (u, final) at callback
        cases nativeRun : ((expiredRetransmitHandshake pid).run actual.wg).run actual.ambient with
        | error stop => rw [nativeRun] at callback; cases callback
        | ok out =>
          obtain ⟨⟨value, g⟩, a⟩ := out
          rw [nativeRun] at callback
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj callback)
          have outQueue := expiredRetransmit_giveUp_empty pid next q stored nextEmpty limit
            actual.wg actual.ambient value g a actualDevice nativeRun
          obtain ⟨after, afterPeer, identity, attempts, timer⟩ :=
            source_retransmit_counter pid q actual.wg actual.ambient value g a actualPeer nativeRun
          refine ⟨outQueue, after, afterPeer, identity.trans fields.1, ?_⟩
          simpa [fields.2.1] using attempts

end Leanux.Proofs.WG.TimerDiscipline
