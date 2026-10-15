import Leanux.Proofs.WG.TimerDiscipline.RetryBoundarySource
import Leanux.Proofs.WG.TimerDiscipline.SourceClaims

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- A continuation contract at the actual sequence exit. No scheduler choice,
callback invocation, arm record, or successful give-up return is assumed. -/
theorem source_retry_boundary (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) (nineteen : horizons.length = 19)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d)
      (fun result boundary => SameRetryPeer pid result.2 →
        Campaign2.AgreesOn (fun s => s = boundary)
          (expiredRetransmitHandshake pid)
          (do let _ ← retransmitDecision pid; retransmitGiveUp pid) ∧
        Campaign2.Ensures (expiredRetransmitHandshake pid) (fun s => s = boundary)
          (fun _ final => final.wg.device.map Device.sendWorkQueue = some [] ∧
            ∃ q, final.peerAt pid = some q ∧ q.internalId = p.internalId ∧
              q.timerHandshakeAttempts = 19)) := by
  intro entry result finish pre run same
  have cert := source_retry_sequence d horizons empty entry result finish pre run
  have counts := (cert.2.2.2.2 pid p resident same).1
  have queue := cert.2.2.1
  cases device : (snapshot finish).wg.device with
  | none => simp [device] at queue
  | some next =>
    have nextEmpty : next.sendWorkQueue = [] := by simpa [device] using queue
    cases stored : next.peers[pid]? with
    | none => simp [workerObservation, Snapshot.peerAt, device, stored] at counts
    | some q =>
      have fields : q.internalId = p.internalId ∧ q.timerHandshakeAttempts = 19 ∧
          q.refcount = p.refcount := by
        simpa [workerObservation, Snapshot.peerAt, device, stored, workerView, zero, nineteen] using counts
      have limit : MAX_TIMER_HANDSHAKES < q.timerHandshakeAttempts := by
        simp [fields.2.1, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT]
      constructor
      · intro actual eqBoundary
        apply expiredRetransmit_forced_giveUp pid next q stored limit actual
        rw [eqBoundary]
        exact device
      · intro actual u final eqBoundary callback
        have actualDevice : actual.k.wg = some next := by
          change (snapshot actual).wg.device = some next
          rw [eqBoundary]
          exact device
        have actualPeer : Leanux.Proofs.WG.Noise.peerAt actual pid = some q := by
          simp [Leanux.Proofs.WG.Noise.peerAt, actualDevice, stored]
        have outQueue := expiredRetransmit_giveUp_empty pid next q stored nextEmpty limit
          actual u final actualDevice callback
        obtain ⟨after, afterPeer, identity, attempts, timer⟩ :=
          source_retransmit_counter pid q actual u final actualPeer callback
        refine ⟨outQueue, after, afterPeer, identity.trans fields.1, ?_⟩
        simpa [fields.2.1] using attempts

end Leanux.Proofs.WG.TimerDiscipline
