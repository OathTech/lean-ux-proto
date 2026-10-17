import Leanux.Proofs.WG.TimerDiscipline.RetrySequencePureClaims
import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceSource

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

theorem observedRetrySteps_chain (units : List RetryUnit) (d : Device)
    (empty : d.sendWorkQueue = []) (entry : Snapshot)
    (pre : entry.wg.device = some d) :
    Campaign2.Product.Ensures (observedRetrySteps units) (fun s => s = entry)
      (fun steps final => RetrySequenceChain entry units steps final ∧
        final.wg.device.map Device.sendWorkQueue = some []) := by
  induction units generalizing d entry with
  | nil =>
    intro w steps final equal run
    change Except.ok ([], w) = .ok (steps, final) at run
    cases run
    subst entry
    exact ⟨.nil _, by simp [pre, empty]⟩
  | cons unit rest ih =>
    intro w steps final equal run
    subst entry
    change ((observedRetryRearm unit).run w >>= fun pair =>
      (observedRetrySteps rest).run pair.2 >>= fun tail =>
      Except.ok (RetrySequenceStep.mk unit (snapshot w) pair.1 (snapshot pair.2) :: tail.1,
        tail.2)) = .ok (steps, final) at run
    cases hs : (observedRetryRearm unit).run w with
    | error e => rw [hs] at run; cases run
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [hs, Bind.bind, Except.bind] at run
      have certificate := source_retry_rearm d unit empty w result after pre hs
      obtain ⟨next, device, nextEmpty⟩ := retryRearmCertificate_empty certificate
      cases ht : (observedRetrySteps rest).run after with
      | error e => rw [ht] at run; cases run
      | ok pair =>
        obtain ⟨tailSteps, finish⟩ := pair
        rw [ht] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        obtain ⟨tail, finalEmpty⟩ := ih next nextEmpty (snapshot after) device
          after tailSteps finish rfl ht
        exact ⟨.cons ⟨unit, snapshot w, result, snapshot after⟩ rest tailSteps
          (snapshot finish) d pre empty certificate tail, finalEmpty⟩

theorem source_retry_sequence (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d) (RetrySequenceCertificate d units) := by
  intro w result final pre run
  change ((observedRetrySteps units).run w >>= fun out =>
    Except.ok ((snapshot w, out.1), out.2)) = .ok (result, final) at run
  cases hs : (observedRetrySteps units).run w with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨steps, finish⟩ := pair
    rw [hs] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨chain, finalEmpty⟩ := observedRetrySteps_chain units d empty (snapshot w) pre w steps finish rfl hs
    refine ⟨pre, chain, finalEmpty, ?_, ?_⟩
    · intro nil
      subst units
      exact retrySequenceChain_nil chain
    · intro pid p resident same
      exact retrySequenceChain_counts chain pid d p pre resident same

theorem source_retry_sequence_zero_bound (d : Device) (units : List RetryUnit)
    (empty : d.sendWorkQueue = []) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (zero : p.timerHandshakeAttempts = 0) :
    Campaign2.Product.Ensures (observedRetrySequence units)
      (fun s => s.wg.device = some d)
      (fun result _ => SameRetryPeer pid result.2 → units.length ≤ 19) := by
  intro initial result final pre run same
  have certificate := source_retry_sequence d units empty initial result final pre run
  have counts := certificate.2.2.2.2 pid p resident same
  by_cases nil : units = []
  · simp [nil]
  · have bound := (counts.2 nil).1
    simpa [zero, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT] using bound

end Leanux.Proofs.WG.TimerDiscipline
