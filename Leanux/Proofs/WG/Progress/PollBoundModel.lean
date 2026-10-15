import Leanux.Proofs.WG.Roaming.PollEndpointModel

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Roaming Campaign2

def PollTransition (budget : Nat) (before : PollState) : ForInStep PollState → Prop
  | .done after => (after.1 = before.1 ∧ after.2.2 = true) ∨
      (after.1 = before.1 + 1 ∧ budget ≤ after.1 ∧ after.2.2 = before.2.2)
  | .yield after => after.1 = before.1 + 1 ∧ after.1 < budget ∧ after.2.2 = before.2.2

/-- Either the original queue test stopped the loop or its requested budget
was reached. This rules out the poll's own loop-exhaustion guard. -/
def PollLoopReady (budget : Nat) (state : PollState) : Prop :=
  state.1 ≤ budget ∧ (state.2.2 = true ∨ budget ≤ state.1)

/-- Phase origins come from actual calls. A failed prefix has no final state;
the finish cut is historical and is not a failed completion's final state. -/
inductive PollBoundAudit where
  | prefixError (error : Stop)
  | zero (final : Snapshot)
  | finish (state : PollState) (before : Snapshot) (outcome : Outcome Nat)

def erasePollBoundAudit : PollBoundAudit → Outcome Nat
  | .prefixError error => .error error
  | .zero final => .ok (0, final)
  | .finish _ _ outcome => outcome

def PollBoundFacts (budget : Nat) : PollBoundAudit → Prop
  | .prefixError _ => True
  | .zero _ => budget = 0
  | .finish state _ outcome =>
    budget ≠ 0 ∧ PollLoopReady budget state ∧
    (state.2.2 = false → state.1 = budget) ∧
    ∀ n final, outcome = .ok (n, final) → n = state.1 ∧ n < budget

end Leanux.Proofs.WG.Progress
