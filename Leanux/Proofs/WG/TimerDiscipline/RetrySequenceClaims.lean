import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceSource

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem retryRearmCertificate_empty {d : Device} {horizon : UInt64}
    {result : RetryRearmObservation} {final : Snapshot}
    (certificate : RetryRearmCertificate d horizon result final) :
    ∃ next, final.wg.device = some next ∧ next.sendWorkQueue = [] := by
  obtain ⟨pid, selected, send, p, expiry, timer, sent, device, listed, resident,
    armed, due, limit, completed⟩ := certificate.1
  obtain ⟨queuedDev, queued, afterDev, queue, stored, fresh, picked, worker, view, work⟩ := completed
  have empty := congrArg Prod.fst work
  change final.wg.device.map Device.sendWorkQueue = some [] at empty
  cases hd : final.wg.device with
  | none => simp [hd] at empty
  | some next => exact ⟨next, rfl, by simpa [hd] using empty⟩

theorem retryRearmCertificate_selected {d : Device} {horizon : UInt64}
    {result : RetryRearmObservation} {final : Snapshot} {pid : PeerId}
    {selected : Snapshot}
    (certificate : RetryRearmCertificate d horizon result final)
    (selection : result.timer = .ok ((pid, .retransmitHandshake, selected), result.afterTimer)) :
    ∃ p next q, d.peers[pid]? = some p ∧
      p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES ∧
      final.wg.device = some next ∧ next.sendWorkQueue = [] ∧ next.peers[pid]? = some q ∧
      q.internalId = p.internalId ∧ q.timerHandshakeAttempts = p.timerHandshakeAttempts + 1 ∧
      q.refcount = p.refcount ∧ q.handshakePending = false := by
  obtain ⟨picked, cut, send, p, expiry, timer, sent, device, listed, resident,
    armed, due, limit, completed⟩ := certificate.1
  have same : picked = pid := by
    change result.timer = .ok ((picked, .retransmitHandshake, cut), result.afterTimer) at timer
    rw [selection] at timer
    exact (congrArg (fun x => x.1.1) (Except.ok.inj timer)).symm
  subst picked
  obtain ⟨queuedDev, queued, afterDev, queue, stored, fresh, picked, worker, view, work⟩ := completed
  obtain ⟨next, hd, empty⟩ := retryRearmCertificate_empty certificate
  cases hp : next.peers[pid]? with
  | none => simp [workerObservation, Snapshot.peerAt, hd, hp] at view
  | some q =>
    have fields : q.internalId = p.internalId ∧
        q.timerHandshakeAttempts = p.timerHandshakeAttempts + 1 ∧ q.refcount = p.refcount := by
      simpa [workerObservation, Snapshot.peerAt, hd, hp, workerView] using view
    have pending : q.handshakePending = false := by
      have flag := congrArg Prod.snd work
      simpa [workObservation, hd, hp] using flag
    exact ⟨p, next, q, resident, limit, hd, empty, hp, fields.1, fields.2.1, fields.2.2, pending⟩

theorem retrySequenceChain_nil {entry final : Snapshot} {steps : List RetrySequenceStep}
    (chain : RetrySequenceChain entry [] steps final) : final = entry := by
  cases chain
  rfl

theorem retrySequenceChain_counts {entry final : Snapshot} {horizons : List UInt64}
    {steps : List RetrySequenceStep} (chain : RetrySequenceChain entry horizons steps final)
    (pid : PeerId) (d : Device) (p : Peer) (device : entry.wg.device = some d)
    (resident : d.peers[pid]? = some p) (same : SameRetryPeer pid steps) :
    RetrySequenceCounts pid p horizons final := by
  induction chain generalizing d p with
  | nil entry =>
    constructor
    · simp [workerObservation, Snapshot.peerAt, device, resident, workerView]
    · simp
  | cons step horizons rest final initial entryDevice empty certificate tail ih =>
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
      cases horizons with
      | nil =>
        have finish := retrySequenceChain_nil tail
        subst final
        constructor
        · simp only [List.length_cons, List.length_nil]; omega
        · simp [Snapshot.peerAt, finalDevice, qStored, pending]
      | cons h hs =>
        obtain ⟨limitFinal, flag⟩ := bound (by simp)
        constructor
        · simp only [List.length_cons] at limitFinal ⊢
          omega
        · exact flag

theorem observedRetrySteps_chain (horizons : List UInt64) (d : Device)
    (empty : d.sendWorkQueue = []) (w : World) (steps : List RetrySequenceStep) (final : World)
    (pre : (snapshot w).wg.device = some d)
    (run : (observedRetrySteps horizons).run w = .ok (steps, final)) :
    RetrySequenceChain (snapshot w) horizons steps (snapshot final) ∧
      (snapshot final).wg.device.map Device.sendWorkQueue = some [] := by
  induction horizons generalizing d w steps final with
  | nil =>
    change Except.ok ([], w) = .ok (steps, final) at run
    cases run
    exact ⟨.nil _, by simp [pre, empty]⟩
  | cons horizon rest ih =>
    change ((observedRetryRearm horizon).run w >>= fun pair =>
      (observedRetrySteps rest).run pair.2 >>= fun tail =>
      Except.ok (RetrySequenceStep.mk horizon (snapshot w) pair.1 (snapshot pair.2) :: tail.1,
        tail.2)) = .ok (steps, final) at run
    cases hs : (observedRetryRearm horizon).run w with
    | error e => rw [hs] at run; cases run
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [hs, Bind.bind, Except.bind] at run
      have certificate := source_retry_rearm d horizon empty w result after pre hs
      obtain ⟨next, device, nextEmpty⟩ := retryRearmCertificate_empty certificate
      cases ht : (observedRetrySteps rest).run after with
      | error e => rw [ht] at run; cases run
      | ok pair =>
        obtain ⟨tailSteps, finish⟩ := pair
        rw [ht] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        obtain ⟨tail, finalEmpty⟩ := ih next nextEmpty after tailSteps finish device ht
        exact ⟨.cons ⟨horizon, snapshot w, result, snapshot after⟩ rest tailSteps
          (snapshot finish) d pre empty certificate tail, finalEmpty⟩

theorem source_retry_sequence (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d) (RetrySequenceCertificate d horizons) := by
  intro w result final pre run
  change ((observedRetrySteps horizons).run w >>= fun out =>
    Except.ok ((snapshot w, out.1), out.2)) = .ok (result, final) at run
  cases hs : (observedRetrySteps horizons).run w with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨steps, finish⟩ := pair
    rw [hs] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨chain, finalEmpty⟩ := observedRetrySteps_chain horizons d empty w steps finish pre hs
    refine ⟨pre, chain, finalEmpty, ?_, ?_⟩
    · intro nil
      subst horizons
      exact retrySequenceChain_nil chain
    · intro pid p resident same
      exact retrySequenceChain_counts chain pid d p pre resident same

theorem source_retry_sequence_zero_bound (d : Device) (horizons : List UInt64)
    (empty : d.sendWorkQueue = []) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Ensures (observedRetrySequence horizons)
      (fun s => s.wg.device = some d)
      (fun result _ => SameRetryPeer pid result.2 → horizons.length ≤ 19) := by
  intro initial result final pre run same
  have certificate := source_retry_sequence d horizons empty initial result final pre run
  have counts := certificate.2.2.2.2 pid p resident same
  by_cases nil : horizons = []
  · simp [nil]
  · have bound := (counts.2 nil).1
    simpa [zero, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT] using bound

end Leanux.Proofs.WG.TimerDiscipline
