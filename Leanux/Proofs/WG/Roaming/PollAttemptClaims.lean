import Leanux.Proofs.WG.Roaming.PollAttemptFactsSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

theorem observedPollAttempts_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    Campaign2.Product.Observes (observedPollAttempts pid budget toStack) (fun _ => True)
      (fun entry observed => ∃ audit, observed = .ok (audit, entry) ∧
        ∀ iteration ∈ audit.iterations, PollAttemptIterationFacts pid iteration) := by
  intro entry pre
  exact ⟨pollAttemptAuditRun pid budget toStack entry, rfl,
    pollAttemptAuditRun_facts pid budget toStack entry⟩

end Leanux.Proofs.WG.Roaming
