import Leanux.Proofs.WG.Progress.PollBoundModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Roaming

theorem pollLoopReady_no_exhaustion (budget : Nat) (state : PollState)
    (ready : PollLoopReady budget state) :
    ¬ (state.2.2 = false ∧ state.1 < budget) := by
  obtain ⟨bound, drained | reached⟩ := ready
  · simp [drained]
  · omega

theorem pollLoopReady_not_drained (budget : Nat) (state : PollState)
    (ready : PollLoopReady budget state) (notDrained : state.2.2 = false) :
    state.1 = budget := by
  obtain ⟨bound, drained | reached⟩ := ready
  · simp [notDrained] at drained
  · omega

end Leanux.Proofs.WG.Progress
