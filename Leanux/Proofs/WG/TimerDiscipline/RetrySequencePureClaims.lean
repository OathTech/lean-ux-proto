import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceModel

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

theorem retryRearmCertificate_empty {d : Device} {unit : RetryUnit}
    {result : RetryRearmObservation} {final : Snapshot}
    (certificate : RetryRearmCertificate d unit result final) :
    ∃ next, final.wg.device = some next ∧ next.sendWorkQueue = [] := by
  obtain ⟨selected, send, p, seen, timer, inspection, sent, device, resident,
    limit, completed⟩ := certificate.1
  obtain ⟨queuedDev, queued, afterDev, queue, stored, fresh, picked, worker, view, work⟩ := completed
  have empty := congrArg Prod.fst work
  change final.wg.device.map Device.sendWorkQueue = some [] at empty
  cases hd : final.wg.device with
  | none => simp [hd] at empty
  | some next => exact ⟨next, rfl, by simpa [hd] using empty⟩

theorem retryRearmCertificate_selected {d : Device} {unit : RetryUnit}
    {result : RetryRearmObservation} {final : Snapshot} {pid : PeerId}
    {selected : Snapshot}
    (certificate : RetryRearmCertificate d unit result final)
    (selection : result.timer = .ok ((pid, .retransmitHandshake, selected), result.afterTimer)) :
    ∃ p next q, d.peers[pid]? = some p ∧
      p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES ∧
      final.wg.device = some next ∧ next.sendWorkQueue = [] ∧ next.peers[pid]? = some q ∧
      q.internalId = p.internalId ∧ q.timerHandshakeAttempts = p.timerHandshakeAttempts + 1 ∧
      q.refcount = p.refcount ∧ q.handshakePending = false := by
  obtain ⟨cut, send, p, seen, timer, inspection, sent, device, resident,
    limit, completed⟩ := certificate.1
  have same : unit.pid = pid := by
    change result.timer = .ok ((unit.pid, .retransmitHandshake, cut), result.afterTimer) at timer
    rw [selection] at timer
    exact (congrArg (fun x => x.1.1) (Except.ok.inj timer)).symm
  rw [same] at resident completed
  obtain ⟨queuedDev, queued, afterDev, queue, stored, fresh, picked, worker, view, work⟩ := completed
  obtain ⟨next, hd, empty⟩ := retryRearmCertificate_empty certificate
  cases hp : next.peers[pid]? with
  | none => simp [workerObservation, Campaign2.Snapshot.peerAt, hd, hp] at view
  | some q =>
    have fields : q.internalId = p.internalId ∧
        q.timerHandshakeAttempts = p.timerHandshakeAttempts + 1 ∧ q.refcount = p.refcount := by
      simpa [workerObservation, Campaign2.Snapshot.peerAt, hd, hp, workerView] using view
    have pending : q.handshakePending = false := by
      have flag := congrArg Prod.snd work
      simpa [workObservation, hd, hp] using flag
    exact ⟨p, next, q, resident, limit, hd, empty, hp, fields.1, fields.2.1, fields.2.2, pending⟩

theorem retrySequenceChain_nil {entry final : Snapshot} {steps : List RetrySequenceStep}
    (chain : RetrySequenceChain entry [] steps final) : final = entry := by
  cases chain
  rfl

theorem retrySequenceChain_counts {entry final : Snapshot} {units : List RetryUnit}
    {steps : List RetrySequenceStep} (chain : RetrySequenceChain entry units steps final)
    (pid : PeerId) (d : Device) (p : Peer) (device : entry.wg.device = some d)
    (resident : d.peers[pid]? = some p) (same : SameRetryPeer pid steps) :
    RetrySequenceCounts pid p units final := by
  induction chain generalizing d p with
  | nil entry =>
    constructor
    · simp [workerObservation, Campaign2.Snapshot.peerAt, device, resident, workerView]
    · simp
  | cons step units rest final initial entryDevice empty certificate tail ih =>
    rw [device] at entryDevice
    cases entryDevice
    obtain ⟨selected, selection⟩ := same step (by simp)
    obtain ⟨before, next, q, stored, limit, finalDevice, finalEmpty, qStored,
      identity, attempts, refs, pending⟩ := retryRearmCertificate_selected certificate selection
    rw [resident] at stored
    cases stored
    have restSame : SameRetryPeer pid rest := by
      intro item member
      exact same item (by simp [member])
    obtain ⟨view, bound⟩ := ih next q finalDevice qStored restSame
    constructor
    · simpa [List.length_cons, identity, attempts, refs, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using view
    · intro nonempty
      cases units with
      | nil =>
        have finish := retrySequenceChain_nil tail
        subst final
        constructor
        · simp only [List.length_cons, List.length_nil]; omega
        · simp [Campaign2.Snapshot.peerAt, finalDevice, qStored, pending]
      | cons h hs =>
        obtain ⟨limitFinal, flag⟩ := bound (by simp)
        constructor
        · simp only [List.length_cons] at limitFinal ⊢
          omega
        · exact flag

end Leanux.Proofs.WG.TimerDiscipline
