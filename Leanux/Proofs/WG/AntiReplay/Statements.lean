import Leanux.Proofs.WG.CounterWindow.Bounds
import Leanux.Proofs.WG.ReplayWindow.Statements
import Leanux.Proofs.WG.Keypairs.Evolution.Bounds

/-! R1: anti-replay uniqueness and the inclusive receive-window floor.
The charter's exclusion of equality at the floor is false; the boundary
witness below and the campaign report record the intentional C behavior. -/
namespace Leanux.Proofs.WG.AntiReplay
open Lean Leanux Leanux.WG Leanux.Runner
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.Logged

/-- Under a single keypair lifetime, no wire counter is accepted twice in
any finite pure-window run, from any shape-correct initial bitmap. -/
theorem pure_uniqueness (c : ReplayCounter) (ns : List Nat)
    (hsize : c.backtrack.size = 128) : (accepted c ns).Nodup :=
  accepted_nodup c ns hsize

/-- The same uniqueness property holds for finite runs of the actual mirror
validator, with the keypair continuously allocated throughout the run. -/
theorem mirror_uniqueness (w w' : World) (kp : KeypairId) (c : ReplayCounter)
    (ns results : List Nat) (hc : counterAt w kp = some c)
    (hs : c.backtrack.size = 128)
    (hr : (mirrorCalls kp ns).run w = .ok (results, w')) : results.Nodup :=
  mirrorCalls_nodup w w' kp c ns results hc hs hr

/-- Every accepted full runner execution has its exact committed acceptance
history, with no repeated (allocation lifetime, wire counter) pair. This
includes arbitrary accepted recorded schedules and keypair-slot reuse. -/
theorem runner_uniqueness (trace : Trace) (placeholders : Bool) {floodExact : Bool} (json : Json)
    (hr : Runner.executeTrace trace placeholders floodExact = .ok json) :
    ∃ history, (executeTraceLogged trace placeholders floodExact).run [] = .ok (json, history) ∧
      history.Nodup :=
  Leanux.Proofs.WG.ReplayWindow.S1 trace placeholders json hr

/-- In every accepted full runner execution, each later accepted wire counter
is at most one window behind every earlier acceptance in the same allocation
lifetime. The bound includes equality and covers all accepted record streams,
schedules and keypair-slot reuse, through the exact committed observer. -/
theorem runner_floor (trace : Trace) (placeholders : Bool) {floodExact : Bool} (json : Json)
    (hr : Runner.executeTrace trace placeholders floodExact = .ok json) :
    ∃ history, (executeTraceLogged trace placeholders floodExact).run [] = .ok (json, history) ∧
      history.Pairwise (fun earlier later => earlier.keypair = later.keypair →
        earlier.nonce ≤ later.nonce + COUNTER_WINDOW_SIZE) := by
  obtain ⟨history, hh⟩ := (executeTraceLogged_success_iff trace placeholders json []).mp hr
  exact ⟨history, hh,
    Leanux.Proofs.WG.Keypairs.RunnerProof.executeTraceLogged_floor_of_calls
      Leanux.Proofs.WG.Keypairs.SyscallObservers.syscallLogged_evolves
      trace placeholders json history hh⟩

/-- After every finite pure-run prefix, an accepted counter is at or above
the inclusive lower edge: stored highest ≤ wire counter + 1 + window size.
This also covers the empty window without saturating subtraction. -/
theorem pure_run_floor (c : ReplayCounter) (priorCalls : List Nat) (nonce : Nat)
    (h : (step (finish c priorCalls) nonce).1 = true) :
    (finish c priorCalls).counter ≤ nonce + 1 + COUNTER_WINDOW_SIZE :=
  (step_accepted_bounds (finish c priorCalls) nonce h).1

/-- After every finite pure-run prefix, a counter strictly below that lower
edge is rejected. Equality at the edge is intentionally not excluded. -/
theorem pure_run_below_floor (c : ReplayCounter) (priorCalls : List Nat) (nonce : Nat)
    (h : nonce + 1 + COUNTER_WINDOW_SIZE < (finish c priorCalls).counter) :
    (step (finish c priorCalls) nonce).1 = false :=
  step_below_rejected (finish c priorCalls) nonce h

/-- Every successful original validator call obeys the same inclusive floor,
by exact S2 refinement, from any shape-correct allocated replay window. -/
theorem mirror_floor (w w' : World) (kp : KeypairId) (c : ReplayCounter)
    (nonce : Nat) (hc : counterAt w kp = some c) (hs : c.backtrack.size = 128)
    (hr : (counterValidate kp nonce).run w = .ok (true, w')) :
    c.counter ≤ nonce + 1 + COUNTER_WINDOW_SIZE :=
  (mirror_accepted_bounds w w' kp c nonce hc hs hr).1

/-- The floor applies after every finite sequence of original mirror calls;
the prefix's pure state is the exact projection of the resulting World. -/
theorem mirror_run_floor (w mid out : World) (kp : KeypairId) (c : ReplayCounter)
    (priorCalls results : List Nat) (nonce : Nat)
    (hc : counterAt w kp = some c) (hs : c.backtrack.size = 128)
    (hp : (mirrorCalls kp priorCalls).run w = .ok (results, mid))
    (hr : (counterValidate kp nonce).run mid = .ok (true, out)) :
    (finish c priorCalls).counter ≤ nonce + 1 + COUNTER_WINDOW_SIZE := by
  obtain ⟨actual, he, hcounter⟩ := mirrorCalls_refines w kp c priorCalls hc hs
  rw [hp] at he
  have hm : mid = actual := congrArg Prod.snd (Except.ok.inj he)
  subst actual
  exact mirror_floor mid out kp (finish c priorCalls) nonce hcounter
    (by simpa [finish_size] using hs) hr

/-- The C boundary is inclusive: after accepting wire counter 8129, unseen
counter 1 (exactly 8129−8128) is accepted; counter 0 and replayed 1 are rejected.
Thus the charter's original exclusion of equality is false even from empty. -/
theorem inclusive_boundary_witness :
    accepted ({} : ReplayCounter) [8129, 1, 0, 1] = [8129, 1] := by
  set_option maxRecDepth 4096 in decide

end Leanux.Proofs.WG.AntiReplay
