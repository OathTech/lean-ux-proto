import PeerReturnObservation
import PeerCountCuts
import LookupPeerRelation

namespace Binary.LookupRelation
open Leanux LookupObservation PeerCountPhase

/-- Once called, only an actual helper-return observation deactivates the
    helper; unrelated tags cannot do so. -/
theorem helperActive_append_no_return (seen delta : List Point)
    (active : helperActive seen = true)
    (noReturn : ∀ point ∈ delta, point.tag ≠ .returned "wg_peer_get_maybe_zero") :
    helperActive (seen ++ delta) = true := by
  induction delta generalizing seen with
  | nil => simpa using active
  | cons point rest ih =>
    have step : helperActive (seen ++ [point]) = true := by
      have different := noReturn point (by simp)
      simp only [helperActive, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change helperTag (helperActive seen) point = true
      rw [active]
      cases tag : point.tag with
      | decision d => simp [helperTag, tag]
      | call name => simp [helperTag, tag]
      | returned name =>
        have neq : name ≠ "wg_peer_get_maybe_zero" := by
          intro eq; subst name; exact different tag
        simp [helperTag, tag, neq]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (seen ++ [point]) step (fun q member => noReturn q (by simp [member]))

/-- Guard of the pending count equation, derived from the actual raw and
    observed prefixes. It is not an additional entry-domain assumption. -/
theorem helper_live_active {first boundary final : List MachineState} {address old}
    (phase : IncrementingReturnAt first boundary final address old)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (first.take n) ≠ none)
    (rx : Nat) (seen localEvents : List Point)
    (observed : observe rx first = .ok seen) (active : helperActive seen = true)
    (n : Nat) (later : first.length ≤ n) (proper : n < final.length)
    (localObs : observe rx (final.take n) = .ok localEvents) :
    helperActive localEvents = true := by
  have noReturn := observe_no_helper_return_of_scan_nonempty rx (final.take n) localEvents seed localObs (by
    intro k
    rw [List.take_take]
    exact phase.nonempty_before_return seed incoming (min k n) (by omega))
  have prefixed : first.IsPrefix final := by
    obtain ⟨body, af, stable, _, _, _, returned⟩ := phase
    exact stable.prefix.trans ((List.prefix_append boundary (PeerGet.incrementStates body af)).trans returned.prefix)
  obtain ⟨tail, recorded⟩ := prefixed
  have rawPrefix : final.take n = first ++ tail.take (n-first.length) := by
    rw [← recorded, List.take_append, List.take_of_length_le later]
  have firstNonempty : first ≠ [] := by intro empty; subst first; cases observed
  rw [rawPrefix] at localObs
  obtain ⟨earlierEvents, delta, earlierObs, equal⟩ :=
    observe_prefix rx first (tail.take (n-first.length)) localEvents localObs firstNonempty
  have same : earlierEvents = seen := Except.ok.inj (earlierObs.symm.trans observed)
  rw [same] at equal
  rw [equal]
  exact helperActive_append_no_return seen delta active
    (fun p member => noReturn p (by rw [equal]; exact List.mem_append.mpr (.inr member)))

/-- At each live-helper cut, R's activity-guarded scanner is exactly the
    executed scanner. At RET both are none, regardless of the tag guard. -/
theorem helper_live_countPhase {first boundary final : List MachineState} {address old}
    (phase : IncrementingReturnAt first boundary final address old)
    (initial : scan none first = none)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (first.take n) ≠ none)
    (rx : Nat) (seen localEvents : List Point)
    (observed : observe rx first = .ok seen) (active : helperActive seen = true)
    (n : Nat) (later : first.length ≤ n)
    (localObs : observe rx (final.take n) = .ok localEvents) :
    countPhase (final.take n) localEvents = scan none (final.take n) := by
  by_cases proper : n < final.length
  · have activeNow := helper_live_active phase seed incoming rx seen localEvents observed active n later proper localObs
    simp only [countPhase, activeNow, ite_true]
  · have cleared : scan none (final.take n) = none := by
      rw [(phase.schedule initial).2.2 n later]
      simp only [show final.length ≤ n by omega, ite_true]
    simp only [countPhase, cleared]
    split <;> rfl

#print axioms helperActive_append_no_return
#print axioms helper_live_active
#print axioms helper_live_countPhase
end Binary.LookupRelation
