import Leanux.Proofs.WG.Progress.PollBoundSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Roaming Campaign2

/-- Inspection's returned datum certifies the actual original loop boundary;
its own unchanged entry state is not a claimed successful poll final state. -/
theorem source_poll_bound (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1) :
    Campaign2.Product.Returns (observedPollBound pid budget toStack) (fun _ => True)
      (fun audit _ => PollBoundFacts budget audit) := by
  intro entry pre
  exact ⟨pollBoundAuditRun pid budget toStack entry, entry, rfl,
    pollBoundAuditRun_facts pid budget toStack enough entry⟩

end Leanux.Proofs.WG.Progress
