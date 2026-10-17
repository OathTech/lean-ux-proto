import Leanux.Proofs.WG.Progress.PollStepSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Noise Roaming Std.Do

/-- The original list forIn stops before fuel exhaustion when its remaining
turns cover the remaining requested work budget. Callback errors are untouched. -/
theorem pollLoop_ready (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (turns : List Nat)
    (state : PollState) (below : state.1 < budget)
    (enough : budget ≤ state.1 + turns.length) :
    Noise.Product.Ensures (forIn turns state (pollStep pid budget toStack)) (fun _ => True)
      (fun result _ => PollLoopReady budget result) := by
  induction turns generalizing state with
  | nil => simp only [List.length_nil, Nat.add_zero] at enough; omega
  | cons turn turns ih =>
    intro w result out pre run
    rw [List.forIn_cons, StateT.run_bind] at run
    cases hs : (pollStep pid budget toStack turn state).run w with
    | error error => rw [hs] at run; cases run
    | ok pair =>
      obtain ⟨step, middle⟩ := pair
      have transition := pollStep_transition pid budget toStack turn state w step middle trivial hs
      rw [hs] at run
      cases step with
      | done next =>
        change Except.ok (next, middle) = .ok (result, out) at run
        cases run
        rcases transition with ⟨same, drained⟩ | ⟨increment, reached, drained⟩
        · exact ⟨by omega, Or.inl drained⟩
        · exact ⟨by omega, Or.inr reached⟩
      | yield next =>
        obtain ⟨increment, nextBelow, drained⟩ := transition
        change (forIn turns next (pollStep pid budget toStack)).run middle = .ok (result, out) at run
        exact ih next nextBelow (by simp only [List.length_cons] at enough; omega)
          middle result out trivial run

theorem pollRange_ready (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1) :
    Noise.Product.Ensures (forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
      ((0, {}, false) : PollState) (pollStep pid budget toStack)) (fun _ => 0 < budget)
      (fun result _ => PollLoopReady budget result) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  intro w result out positive run
  exact pollLoop_ready pid budget toStack (List.range' 0 (MAX_QUEUED_PACKETS + 1))
    (0, {}, false) positive (by simpa using enough) w result out trivial run

end Leanux.Proofs.WG.Progress
