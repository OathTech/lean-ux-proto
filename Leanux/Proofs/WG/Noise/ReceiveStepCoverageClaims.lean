import Leanux.Proofs.WG.Noise.ReceiveStepCoverageSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller
open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller

/-- Normal empty and consumed polls cover every surviving handshake tag through
the actual reception receipts. PollShape retains queue selection, MAC dispatch,
and the receipts' native validity; no new reachability or reference premise is
required. Peer deletion is allowed. -/
theorem original_receiveStep_tag_coverage (entry : Campaign2.Snapshot) :
    Campaign2.Ensures observeStep (fun s => s = entry)
      (fun r final =>
        r.entry = entry ∧ PollShape r.entry r.poll ∧
        TagCoverage entry.tagAt r.poll.receipts final.tagAt) := by
  intro g ambient receipt final after pre run
  have shape := original_receiveStep_receipt entry g ambient receipt final after pre run
  have coverage := observeStep_coverage g ambient receipt final after run
  refine ⟨shape.1,shape.2,?_⟩
  subst entry
  exact coverage

end Leanux.Proofs.WG.Noise.ReceiveStepCaller
